import Lean
import Lean.Data.Lsp.Ipc
import Tests.LspClient
import Tests.Helpers

namespace Tests.LspIntegration

open Lean Lsp Ipc JsonRpc Tests.LspClient Tests.Helpers

def basicLeanFile : System.FilePath := testProjectPath / "Simple.lean"

unsafe def testLspServerStartup : IO Unit := do
  IO.println "\n  [LSP: Server Startup]"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "server startup" s!"lean-analyzer not found at {analyzerPath}"
    return
  
  runWithLeanAnalyzer do
    let initResult ← initializeServer 0
    IO.println s!"  ✓ server initialized"
    IO.println s!"  ✓ capabilities: {(toJson initResult.capabilities).compress.take 100}..."
    
    shutdown 1
    let exitCode ← waitForExit
    assertTrue "server exited cleanly" (exitCode == 0)

unsafe def testLspOpenDocument : IO Unit := do
  IO.println "\n  [LSP: Open Document]"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "open document" "lean-analyzer not built"
    return
  
  unless ← basicLeanFile.pathExists do
    skipTest "open document" "Basic.lean not found"
    return
  
  runWithLeanAnalyzer do
    let _ ← initializeServer 0
    
    let content ← IO.FS.readFile basicLeanFile
    let uri ← fileUri basicLeanFile
    
    openDocument uri content
    IO.println s!"  ✓ document opened: {uri}"
    
    -- Wait for diagnostics to confirm file was processed
    waitForFileReady uri
    IO.println s!"  ✓ file elaborated"
    
    shutdown 1
    let _ ← waitForExit
    IO.println s!"  ✓ document test complete"

unsafe def testLspRpcConnect : IO Unit := do
  IO.println "\n  [LSP: RPC Connect]"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "RPC connect" "lean-analyzer not built"
    return
  
  unless ← basicLeanFile.pathExists do
    skipTest "RPC connect" "Basic.lean not found"
    return
  
  runWithLeanAnalyzer do
    let _ ← initializeServer 0
    
    let content ← IO.FS.readFile basicLeanFile
    let uri ← fileUri basicLeanFile
    
    openDocument uri content
    waitForFileReady uri
    
    let sessionId ← connectRpcSession 2 uri
    IO.println s!"  ✓ RPC session connected: {sessionId}"
    
    shutdown 3
    let _ ← waitForExit
    IO.println s!"  ✓ RPC connect test complete"

unsafe def testHover : IO Unit := do
  IO.println "\n  [LSP: Hover]"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "hover" "lean-analyzer not built"
    return

  unless ← basicLeanFile.pathExists do
    skipTest "hover" "test file not found"
    return

  runWithLeanAnalyzer do
    let root ← rootUri
    IO.println s!"  rootUri: {root}"

    let _ ← initializeServer 0

    let content ← IO.FS.readFile basicLeanFile
    let uri ← fileUri basicLeanFile
    IO.println s!"  fileUri: {uri}"
    IO.println s!"  content: {content.take 50}..."

    openDocument uri content
    waitForFileReady uri

    -- Try hover at position (0, 10) - should be on "simple_rfl"
    let hover ← hoverRequest 2 uri 0 10
    match hover with
    | some h => IO.println s!"  ✓ hover result: {h.contents.value.take 100}..."
    | none => IO.println s!"  ✗ hover returned none at (0, 10)"

    shutdown 3
    let _ ← waitForExit
    IO.println s!"  ✓ hover test complete"

unsafe def testGetProofDagRpc : IO Unit := do
  IO.println "\n  [LSP: LeanAnalyzer.getProofDag RPC]"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "getProofDag RPC" "lean-analyzer not built"
    return

  unless ← basicLeanFile.pathExists do
    skipTest "getProofDag RPC" "test file not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile basicLeanFile
    let uri ← fileUri basicLeanFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Call LeanAnalyzer.getProofDag at line 0 (only line in Simple.lean)
    let result ← callRpc 3 sessionId uri 0 10 "LeanAnalyzer.getProofDag" (Json.mkObj [("mode", "tree")])
    IO.println s!"  ✓ LeanAnalyzer.getProofDag called"
    IO.println s!"  Result (first 500 chars): {result.compress.take 500}"

    shutdown 4
    let _ ← waitForExit
    IO.println s!"  ✓ getProofDag RPC test complete"

unsafe def runTests : IO Unit := do
  IO.println ""
  IO.println "══════════════════════════════════════════════════════════════"
  IO.println "  LSP Integration Tests (lean-analyzer)"
  IO.println "══════════════════════════════════════════════════════════════"
  
  testLspServerStartup
  testLspOpenDocument
  testLspRpcConnect
  testHover
  testGetProofDagRpc
  
  IO.println ""
  IO.println "  ✓ LSP integration tests complete"

end Tests.LspIntegration
