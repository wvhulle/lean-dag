import Lean
import Lean.Server.FileWorker
import Lean.Server.Watchdog
import Lean.Server.Requests
import LeanDag.Protocol
import LeanDag.TcpServer
import LeanDag.InfoTreeParser
import LeanDag.DagBuilder
import LeanDag.FunctionalDagBuilder

open Lean Elab Server Lsp JsonRpc
open Lean.Server.FileWorker Lean.Server.Snapshots
open LeanDag.InfoTreeParser
open LeanDag.FunctionalDagBuilder (computeFunctionalDag isTermModeTree)

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

/-- Default port range for TUI servers. Each worker gets a unique port from this range. -/
def defaultPortRangeMin : UInt16 := 9742
def defaultPortRangeMax : UInt16 := 9842

/-- Parse port from environment variable string. -/
def parsePort (s : String) (default_ : UInt16) : UInt16 :=
  match s.toNat? with
  | some n => if n > 0 && n < 65536 then n.toUInt16 else default_
  | none => default_

/-- Get TCP port range from environment or use defaults. -/
def getPortRange : IO (UInt16 × UInt16) := do
  let minPort ← match ← IO.getEnv "LEAN_DAG_PORT_MIN" with
    | some s => pure (parsePort s defaultPortRangeMin)
    | none => pure defaultPortRangeMin
  let maxPort ← match ← IO.getEnv "LEAN_DAG_PORT_MAX" with
    | some s => pure (parsePort s defaultPortRangeMax)
    | none => pure defaultPortRangeMax
  return (minPort, maxPort)

/-- Try to create a TcpServer on the given port. Returns none if port is in use. -/
def tryCreateServer (port : UInt16) (mode : ServerOperatingMode)
    (fileUri : Option String) (minPort maxPort : UInt16) : IO (Option TcpServer) := do
  try
    let srv ← TcpServer.create port mode fileUri minPort maxPort
    return some srv
  catch _ =>
    return none

/-- Find an available port and create the server. -/
def createServerWithAvailablePort (minPort maxPort : UInt16) (mode : ServerOperatingMode)
    (fileUri : Option String) : IO (Option TcpServer) := do
  let mut port := minPort
  while port ≤ maxPort do
    if let some srv ← tryCreateServer port mode fileUri minPort maxPort then
      return some srv
    port := port + 1
  return none

/-- Lazily start the TCP server on first use. Returns the server if available.
    The fileUri parameter is used to identify which file this worker is handling. -/
def ensureTuiServer (fileUri : Option String := none) : IO (Option TcpServer) := do
  match ← tuiServerRef.get with
  | some srv => return some srv
  | none =>
    logToFile "ensureTuiServer: starting TCP server lazily"
    try
      let (minPort, maxPort) ← getPortRange
      let fileDesc := fileUri.getD "unknown file"
      logToFile s!"Looking for available port in range {minPort}-{maxPort} for {fileDesc}"
      match ← createServerWithAvailablePort minPort maxPort .library fileUri with
      | some srv =>
        logToFile s!"TCP server created on port {srv.port}"
        srv.start
        tuiServerRef.set (some srv)
        logToFile s!"TCP server started on port {srv.port} for {fileDesc}"
        IO.eprintln s!"[LeanDag] TCP server started on port {srv.port} for {fileDesc}"
        return some srv
      | none =>
        logToFile s!"No available port in range {minPort}-{maxPort}"
        IO.eprintln s!"[LeanDag] No available port in range {minPort}-{maxPort}"
        return none
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

  let srv? ← ensureTuiServer (some (toString uri))
  let some srv := srv? | return .pure ()

  RequestM.withWaitFindSnapAtPos position fun snap => do
    if isTermModeTree snap.infoTree then
      let functionalDag ← computeFunctionalDag snap position
      srv.broadcast (.functionalDag (uri := uri) (position := position) (dag := functionalDag))
    else
      let proofDag ← computeProofDag snap position
      srv.broadcast (.proofDag (uri := uri) (position := position) (dag := proofDag))

/-- Compute and broadcast proof DAG when hover request is received. -/
def broadcastProofDagOnHover (params : Lsp.HoverParams) : RequestM (RequestTask Unit) := do
  let doc ← RequestM.readDoc
  let uri := doc.meta.uri
  let position := params.position

  -- Cache cursor position for rebroadcast after edits
  lastCursorRef.set (some (uri, position))

  -- Ensure TCP server is running and get reference
  let srv? ← ensureTuiServer (some (toString uri))
  let some srv := srv? | return .pure ()

  -- Broadcast cursor position immediately
  let cursorInfo : EditorCursorPosition := { uri, position, method := "hover" }
  srv.broadcast (.cursor (uri := cursorInfo.uri) (position := cursorInfo.position) (method := cursorInfo.method))

  -- Capture the server request emitter if not already captured
  if (← serverRequestEmitterRef.get).isNone then
    let ctx ← read
    serverRequestEmitterRef.set (some ctx.serverRequestEmitter)
    setNavigateHandler fun navUri navPos => do
      sendShowDocument navUri navPos.line navPos.character
    logToFile "Captured serverRequestEmitter and set navigate handler"

  -- Compute and broadcast DAG using cached elaboration
  -- Try functional DAG for term-mode, fall back to proof DAG for tactic-mode
  RequestM.withWaitFindSnapAtPos position fun snap => do
    if isTermModeTree snap.infoTree then
      let functionalDag ← computeFunctionalDag snap position
      srv.broadcast (.functionalDag (uri := uri) (position := position) (dag := functionalDag))
    else
      let proofDag ← computeProofDag snap position
      srv.broadcast (.proofDag (uri := uri) (position := position) (dag := proofDag))

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

/-- Entry point for running as a watchdog process (standalone binary mode). -/
def watchdogMain (args : List String) : IO UInt32 :=
  Lean.Server.Watchdog.watchdogMain args

/-- Entry point for running as a worker process (standalone binary mode). -/
def workerMain (opts : Lean.Options := {}) : IO UInt32 :=
  Lean.Server.FileWorker.workerMain opts

end LeanDag
