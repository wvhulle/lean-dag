import Lean
import Lean.Data.Lsp.Ipc

namespace Tests.LspClient

open Lean Lsp Ipc JsonRpc IO

def testProjectPath : System.FilePath := "Tests/samples/test-project"

def fileUri (path : System.FilePath) : IO String := do
  let cwd ← IO.currentDir
  return s!"file://{cwd}/{path}"

def rootUri : IO String := fileUri testProjectPath

def initializeServer (requestId : Nat := 0) : IpcM InitializeResult := do
  let root ← rootUri
  let params : InitializeParams := {
    processId? := none
    rootUri? := some root
    capabilities := {}
  }
  writeRequest ⟨requestId, "initialize", params⟩
  let resp ← readResponseAs requestId InitializeResult
  writeNotification ⟨"initialized", InitializedParams.mk⟩
  return resp.result

def openDocument (uri : String) (content : String) : IpcM Unit := do
  let params : DidOpenTextDocumentParams := {
    textDocument := {
      uri := uri
      languageId := "lean4"
      version := 1
      text := content
    }
  }
  writeNotification ⟨"textDocument/didOpen", params⟩

def waitForFileReady (uri : String) (version : Nat := 1) : IpcM Unit := do
  let _ ← collectDiagnostics 100 uri version

def callRpc (requestId : Nat) (sessionId : UInt64) (uri : String) (line col : Nat) (method : String) (innerParams : Json) : IpcM Json := do
  let mode := innerParams.getObjValAs? String "mode" |>.toOption.getD "tree"
  let procedureParams := Json.mkObj [
    ("textDocument", Json.mkObj [("uri", toJson uri)]),
    ("position", Json.mkObj [("line", line), ("character", col)]),
    ("mode", mode)
  ]

  let rpcParams := Json.mkObj [
    ("textDocument", Json.mkObj [("uri", toJson uri)]),
    ("position", Json.mkObj [("line", line), ("character", col)]),
    ("sessionId", toJson sessionId),
    ("method", toJson method),
    ("params", procedureParams)
  ]
  writeRequest (α := Json) ⟨requestId, "$/lean/rpc/call", rpcParams⟩
  let resp ← readResponseAs requestId Json
  return resp.result

def connectRpcSession (requestId : Nat) (uri : String) : IpcM UInt64 := do
  let params := Json.mkObj [("uri", toJson uri)]
  writeRequest (α := Json) ⟨requestId, "$/lean/rpc/connect", params⟩
  let resp ← readResponseAs requestId Json
  match resp.result.getObjValAs? UInt64 "sessionId" with
  | .ok sessionId => return sessionId
  | .error e => throw <| IO.userError s!"Failed to parse sessionId: {e}"

def hoverRequest (requestId : Nat) (uri : String) (line col : Nat) : IpcM (Option Hover) := do
  let params : HoverParams := {
    textDocument := { uri := uri }
    position := ⟨line, col⟩
  }
  writeRequest ⟨requestId, "textDocument/hover", params⟩
  let resp ← readResponseAs requestId (Option Hover)
  return resp.result

def leanAnalyzerPath : IO System.FilePath := do
  let cwd ← IO.currentDir
  return cwd / ".lake" / "build" / "bin" / "lean-analyzer"

def runWithLeanAnalyzer (action : IpcM α) : IO α := do
  let cwd ← IO.currentDir
  let serverPath ← leanAnalyzerPath
  let projectDir := cwd / testProjectPath
  Ipc.runWith "sh" #["-c",
    s!"cd {projectDir} && unset LEAN_PATH LEAN_SYSROOT && exec lake env sh -c 'LEAN_WORKER_PATH={serverPath} exec {serverPath}'"] action

end Tests.LspClient
