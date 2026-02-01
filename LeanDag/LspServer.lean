import Lean
import Lean.Server.FileWorker
import Lean.Server.Watchdog
import Lean.Server.Requests
import LeanDag.Protocol
import LeanDag.TcpServer
import LeanDag.InfoTreeParser
import LeanDag.DagBuilder

open Lean Elab Server Lsp JsonRpc
open Lean.Server.FileWorker Lean.Server.Snapshots
open LeanDag.InfoTreeParser

namespace LeanDag

/-! ## Logging -/

/-- Cached log file path (computed once). -/
builtin_initialize logPathRef : IO.Ref String ← do
  let home := (← IO.getEnv "HOME").getD "/tmp"
  IO.mkRef s!"{home}/.cache/lean-dag.log"

/-- Log a message with monotonic timestamp (no subprocess). -/
def logToFile (msg : String) : IO Unit := do
  let path ← logPathRef.get
  let ms ← IO.monoMsNow
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"[{ms}ms] {msg}\n"

/-! ## TUI Server Reference -/

/-- Global reference to the TUI TCP server (if started). -/
builtin_initialize tuiServerRef : IO.Ref (Option TcpServer) ← IO.mkRef none

/-- Cached cursor position for rebroadcasting after edits. -/
builtin_initialize lastCursorRef : IO.Ref (Option (String × Lsp.Position)) ← IO.mkRef none

/-! ## Server Request Emitter for Navigation -/

/-- Type alias for server request emitter function. -/
abbrev ServerRequestEmitterFn := String → Json → BaseIO (ServerTask (ServerRequestResponse Json))

/-- Global reference to the server request emitter (captured from RequestM context). -/
builtin_initialize serverRequestEmitterRef : IO.Ref (Option ServerRequestEmitterFn) ← IO.mkRef none

/-- ShowDocumentParams for window/showDocument request. -/
structure ShowDocumentParams where
  uri : String
  external : Option Bool := none
  takeFocus : Option Bool := some true
  selection : Option Lsp.Range := none
  deriving ToJson, FromJson

/-- Send a showDocument request to the editor. -/
def sendShowDocument (uri : String) (line : Nat) (character : Nat) : IO Unit := do
  logToFile s!"sendShowDocument: uri={uri} line={line} char={character}"
  match ← serverRequestEmitterRef.get with
  | some emitter =>
    let range : Lsp.Range := {
      start := { line := line, character := character }
      «end» := { line := line, character := character }
    }
    let params : ShowDocumentParams := {
      uri := uri
      takeFocus := some true
      selection := some range
    }
    let _ ← emitter "window/showDocument" (toJson params)
    logToFile "showDocument request sent"
  | none =>
    logToFile "No server request emitter available"

/-- Default TCP port for TUI server. -/
def defaultTcpPort : UInt16 := 9742

/-- Get TCP port from environment or use default. -/
def getTcpPort : IO UInt16 := do
  if let some portStr ← IO.getEnv "LEAN_DAG_TCP_PORT" then
    if let some n := portStr.toNat? then
      if n > 0 && n < 65536 then
        return n.toUInt16
  return defaultTcpPort

/-- Lazily start the TCP server on first use. Returns the server if available. -/
def ensureTuiServer : IO (Option TcpServer) := do
  match ← tuiServerRef.get with
  | some srv => return some srv
  | none =>
    logToFile "ensureTuiServer: starting TCP server lazily"
    try
      let port ← getTcpPort
      logToFile s!"Creating TCP server on port {port}"
      let srv ← TcpServer.create port .library
      logToFile "TCP server created, starting..."
      srv.start
      tuiServerRef.set (some srv)
      logToFile s!"TCP server started on port {port}"
      IO.eprintln s!"[LeanDag] TCP server started on port {port}"
      return some srv
    catch e =>
      logToFile s!"Failed to start TCP server: {e}"
      IO.eprintln s!"[LeanDag] Failed to start TCP server: {e}"
      return none

/-! ## RPC Types -/

structure GetProofDagParams where
  textDocument : TextDocumentIdentifier
  position     : Lsp.Position
  deriving FromJson, ToJson

structure GetProofDagResult where
  proofDag : CompleteProofDag
  version  : Nat := 5
  deriving FromJson, ToJson

/-! ## Proof DAG Computation -/

/-- Compute proof DAG from snapshot. -/
def computeProofDag (snap : Snapshot) (position : Lsp.Position) : RequestM (Option CompleteProofDag) := do
  let some result ← parseInfoTree snap.infoTree | return none
  let definitionName := getDefinitionName snap.infoTree
  return some (.build result.steps position definitionName)

/-! ## RPC Handler -/

@[server_rpc_method]
def getProofDag (params : GetProofDagParams) : RequestM (RequestTask GetProofDagResult) := do
  RequestM.withWaitFindSnapAtPos params.position fun snap => do
    match ← computeProofDag snap params.position with
    | some proofDag => return { proofDag }
    | none => return { proofDag := {} }

/-! ## Standalone Binary Support -/

builtin_initialize
  Lean.Server.registerBuiltinRpcProcedure
    `LeanDag.getCompleteProofDag GetProofDagParams GetProofDagResult getProofDag

/-! ## Proof DAG Broadcasting

Chain onto textDocument/hover to compute and broadcast proof DAG to TUI clients.
This uses the same worker that already has elaboration cached, avoiding redundant work.
-/

/-- Rebroadcast proof DAG at cached cursor position after document changes. -/
def rebroadcastProofDag : RequestM (RequestTask Unit) := do
  let some (uri, position) ← lastCursorRef.get | return .pure ()
  let doc ← RequestM.readDoc
  -- Only rebroadcast if same document
  if doc.meta.uri != uri then return .pure ()

  let srv? ← ensureTuiServer
  let some srv := srv? | return .pure ()

  RequestM.withWaitFindSnapAtPos position fun snap => do
    let proofDag ← computeProofDag snap position
    srv.broadcast (.proofDag uri position proofDag)

/-- Compute and broadcast proof DAG when hover request is received. -/
def broadcastProofDagOnHover (params : Lsp.HoverParams) : RequestM (RequestTask Unit) := do
  let doc ← RequestM.readDoc
  let uri := doc.meta.uri
  let position := params.position

  -- Cache cursor position for rebroadcast after edits
  lastCursorRef.set (some (uri, position))

  -- Ensure TCP server is running and get reference
  let srv? ← ensureTuiServer
  let some srv := srv? | return .pure ()

  -- Broadcast cursor position immediately
  let cursorInfo : EditorCursorPosition := { uri, position, method := "hover" }
  srv.broadcast (.cursor cursorInfo)

  -- Capture the server request emitter if not already captured
  if (← serverRequestEmitterRef.get).isNone then
    let ctx ← read
    serverRequestEmitterRef.set (some ctx.serverRequestEmitter)
    setNavigateHandler fun navUri navPos => do
      sendShowDocument navUri navPos.line navPos.character
    logToFile "Captured serverRequestEmitter and set navigate handler"

  -- Compute and broadcast proof DAG using cached elaboration
  RequestM.withWaitFindSnapAtPos position fun snap => do
    let proofDag ← computeProofDag snap position
    srv.broadcast (.proofDag uri position proofDag)

builtin_initialize
  Lean.Server.chainLspRequestHandler "textDocument/hover" Lsp.HoverParams (Option Lsp.Hover)
    fun params prevTask => do
      let _ ← broadcastProofDagOnHover params
      return prevTask

/-- Chain onto documentColor request to rebroadcast after edits.
This request is sent by the editor after document changes. -/
builtin_initialize
  Lean.Server.chainLspRequestHandler "textDocument/documentColor"
    Lsp.DocumentColorParams (Array Lsp.ColorInformation)
    fun _ prevTask => do
      let _ ← rebroadcastProofDag
      return prevTask

builtin_initialize
  Lean.Server.chainLspRequestHandler "$/lean/plainGoal"
    Lsp.PlainGoalParams (Option Lsp.PlainGoal)
    fun _ prevTask => do
      let _ ← rebroadcastProofDag
      return prevTask

/-- Chain onto definition request to rebroadcast on navigation. -/
builtin_initialize
  Lean.Server.chainLspRequestHandler "textDocument/definition"
    Lsp.TextDocumentPositionParams (Array Lsp.LocationLink)
    fun _ prevTask => do
      let _ ← rebroadcastProofDag
      return prevTask

/-- Entry point for running as a watchdog process (standalone binary mode). -/
def watchdogMain (args : List String) : IO UInt32 :=
  Lean.Server.Watchdog.watchdogMain args

/-- Entry point for running as a worker process (standalone binary mode). -/
def workerMain (opts : Lean.Options := {}) : IO UInt32 :=
  Lean.Server.FileWorker.workerMain opts

end LeanDag
