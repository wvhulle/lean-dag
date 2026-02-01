import Lean
import Lean.Server.FileWorker
import Lean.Server.Watchdog
import Lean.Server.Requests
import LeanDag.Types
import LeanDag.InfoTreeParser
import LeanDag.NameUtils
import LeanDag.Conversion
import LeanDag.DiffComputation
import LeanDag.DagBuilder
import LeanDag.TuiServer.Protocol
import LeanDag.TuiServer.TcpServer

open Lean Elab Server Lsp JsonRpc
open Lean.Server.FileWorker Lean.Server.Snapshots
open LeanDag.InfoTreeParser
open LeanDag.TuiServer

namespace LeanDag

/-! ## TUI Server Reference -/

/-- Global reference to the TUI TCP server (if started). -/
builtin_initialize tuiServerRef : IO.Ref (Option TcpServer) ← IO.mkRef none

/-- Default TCP port for TUI server. -/
def defaultTcpPort : UInt16 := 9742

/-- Get TCP port from environment or use default. -/
def getTcpPort : IO UInt16 := do
  if let some portStr ← IO.getEnv "LEAN_DAG_TCP_PORT" then
    if let some n := portStr.toNat? then
      if n > 0 && n < 65536 then
        return n.toUInt16
  return defaultTcpPort

/-- Start the TCP server for TUI clients. Called during initialization. -/
def startTuiServer : IO Unit := do
  try
    let port ← getTcpPort
    let srv ← TcpServer.create port .library
    srv.start
    tuiServerRef.set (some srv)
    IO.eprintln s!"[LeanDag] TCP server started on port {port}"
  catch e =>
    IO.eprintln s!"[LeanDag] Failed to start TCP server: {e}"

/-- Start TCP server when library is loaded. -/
builtin_initialize do
  startTuiServer

/-- Broadcast proof DAG to TUI clients if server is running. -/
def broadcastToTui (uri : String) (position : Lsp.Position) (proofDag : Option ProofDag) : IO Unit := do
  if let some srv ← tuiServerRef.get then
    srv.broadcastProofDag uri position proofDag

/-! ## RPC Types -/

structure GetProofDagParams where
  textDocument : TextDocumentIdentifier
  position     : Lsp.Position
  mode         : String := "tree"
  deriving FromJson, ToJson

structure GetProofDagResult where
  proofDag : ProofDag
  version  : Nat := 5
  deriving FromJson, ToJson

/-! ## RPC Handler -/

def handleGetProofDag (params : GetProofDagParams) : RequestM (RequestTask GetProofDagResult) := do
  let doc ← RequestM.readDoc
  let uri : String := doc.meta.uri
  let utf8Pos := doc.meta.text.lspPosToUtf8Pos params.position
  IO.eprintln s!"[RPC] getProofDag mode={params.mode} pos={params.position} utf8={utf8Pos} uri={doc.meta.uri}"
  IO.eprintln s!"[RPC] document version={doc.meta.version} headerSnap exists"
  RequestM.withWaitFindSnapAtPos params.position fun snap => do
    IO.eprintln s!"[RPC] snapshot found endPos={snap.endPos}"
    let text := doc.meta.text
    let hoverPos := text.lspPosToUtf8Pos params.position
    match params.mode with
    | "tree" =>
      match ← parseInfoTree snap.infoTree with
      | some result =>
        let definitionName := getDefinitionName snap.infoTree
        IO.eprintln s!"[RPC] tree mode: {result.steps.length} steps, def={definitionName}"
        let proofDag := buildProofDag result.steps params.position definitionName
        -- Broadcast to TUI clients
        broadcastToTui uri params.position (some proofDag)
        return { proofDag }
      | none =>
        IO.eprintln "[RPC] tree mode: no result"
        broadcastToTui uri params.position none
        return { proofDag := {} }
    | "single_tactic" =>
      match goalsAt? snap.infoTree text hoverPos with
      | r :: _ =>
        let binderCache := buildBinderCache snap.infoTree text
        let result ← parseTacticInfo r.ctxInfo (.ofTacticInfo r.tacticInfo) [] {} true snap.infoTree binderCache doc.meta.uri
        let definitionName := getDefinitionName snap.infoTree
        IO.eprintln s!"[RPC] single_tactic mode: {result.steps.length} steps, def={definitionName}"
        let proofDag := buildProofDag result.steps params.position definitionName
        -- Broadcast to TUI clients
        broadcastToTui uri params.position (some proofDag)
        return { proofDag }
      | [] =>
        IO.eprintln "[RPC] single_tactic mode: no goals at position"
        broadcastToTui uri params.position none
        return { proofDag := {} }
    | _ =>
      IO.eprintln s!"[RPC] unknown mode: {params.mode}"
      broadcastToTui uri params.position none
      return { proofDag := {} }

/-! ## RPC Registration -/

/--
Get proof DAG for the current position in a document.

This RPC method is registered via `@[server_rpc_method]` for library mode
(when users `import LeanDag` in their Lean files).
-/
@[server_rpc_method]
def getProofDag (params : GetProofDagParams) : RequestM (RequestTask GetProofDagResult) :=
  handleGetProofDag params

/-! ## Standalone Binary Support

When running as a standalone binary (lean-dag executable), the RPC method must be
registered as a builtin procedure since the worker processes don't import LeanDag.
-/

builtin_initialize
  Lean.Server.registerBuiltinRpcProcedure
    `LeanDag.getProofDag GetProofDagParams GetProofDagResult handleGetProofDag

/-- Entry point for running as a watchdog process (standalone binary mode). -/
def watchdogMain (args : List String) : IO UInt32 :=
  Lean.Server.Watchdog.watchdogMain args

/-- Entry point for running as a worker process (standalone binary mode). -/
def workerMain (opts : Lean.Options := {}) : IO UInt32 :=
  Lean.Server.FileWorker.workerMain opts

end LeanDag
