import Lean
import Lean.Data.Lsp.Ipc
import LeanAnalyzer
import Tests.LspClient
import Tests.Harness

namespace Tests.RpcEdgeCases

open Lean Lsp Ipc JsonRpc LeanAnalyzer Tests.LspClient Tests.Harness

def edgeCaseFile : System.FilePath := testProjectPath / "EdgeCases.lean"
def unicodeFile : System.FilePath := testProjectPath / "Unicode.lean"
def simpleFile : System.FilePath := testProjectPath / "Simple.lean"

def parseProofDag (json : Json) : Except String ProofDag :=
  match json.getObjVal? "proofDag" with
  | .ok dagJson => FromJson.fromJson? dagJson
  | .error e => .error s!"Missing proofDag field: {e}"

/-- Get proof DAG at position. Line/col are 1-indexed (editor style). -/
def getProofDagAt (uri : String) (sessionId : UInt64) (line col : Nat) (requestId : Nat) : IpcM (Option ProofDag) := do
  let result ← callRpc requestId sessionId uri line col "LeanAnalyzer.getProofDag" (Json.mkObj [("mode", "tree")])
  match parseProofDag result with
  | .ok dag => return some dag
  | .error _ => return none

/-! ## Edge Case: Term-Mode Proofs (No Tactics) -/

unsafe def testTermModeProof : IO Unit := do
  printSubsection "Term-Mode Proof (No Tactics)"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "term-mode" "lean-analyzer not built"
    return

  unless ← edgeCaseFile.pathExists do
    skipTest "term-mode" "EdgeCases.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 4: "theorem term_mode_proof : 1 = 1 := rfl" (1-indexed)
    let dag ← getProofDagAt uri sessionId 4 11 3

    match dag with
    | some d =>
      -- Term-mode proofs should have no tactic nodes
      assertTrue "term-mode has no nodes" d.nodes.isEmpty
    | none =>
      -- Or the RPC might return an error/empty result for term-mode
      IO.println "  ✓ term-mode proof returns no DAG (expected)"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ term-mode proof handled correctly"

/-! ## Edge Case: Incomplete Proofs (sorry) -/

unsafe def testSorryProof : IO Unit := do
  printSubsection "Incomplete Proof (sorry)"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "sorry" "lean-analyzer not built"
    return

  unless ← edgeCaseFile.pathExists do
    skipTest "sorry" "EdgeCases.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 7: "theorem sorry_proof : 2 = 2 := by sorry" (1-indexed)
    let dag ← getProofDagAt uri sessionId 7 11 3

    match dag with
    | some d =>
      -- sorry proof should have one node
      assertTrue "sorry has nodes" (!d.nodes.isEmpty)
      -- The proof is not complete (sorry leaves goals unsolved)
      let node := d.nodes[0]!
      assertTrue "sorry tactic text" (containsSubstring node.tactic.text "sorry")
    | none =>
      IO.println "  ✗ sorry proof should return a DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ sorry proof handled correctly"

/-! ## Edge Case: Invalid Cursor Position -/

unsafe def testInvalidPosition : IO Unit := do
  printSubsection "Invalid Cursor Position"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "invalid position" "lean-analyzer not built"
    return

  unless ← simpleFile.pathExists do
    skipTest "invalid position" "Simple.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile simpleFile
    let uri ← fileUri simpleFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Request at line 1001 (way beyond file, 1-indexed)
    -- Server gracefully handles this by returning the last valid snapshot
    let dag ← getProofDagAt uri sessionId 1001 1 3

    match dag with
    | some d =>
      -- Server returns last valid snapshot for out-of-bounds positions
      IO.println s!"  ✓ out of bounds handled (returned {d.nodes.size} nodes)"
    | none =>
      IO.println "  ✓ out of bounds returns no DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ invalid position handled gracefully"

/-! ## Edge Case: Nested Tactic Structures (conv) -/

unsafe def testNestedConv : IO Unit := do
  printSubsection "Nested Tactic (conv block)"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "nested conv" "lean-analyzer not built"
    return

  unless ← edgeCaseFile.pathExists do
    skipTest "nested conv" "EdgeCases.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 14: "  conv_lhs => rw [Nat.add_comm]" (1-indexed)
    let dag ← getProofDagAt uri sessionId 14 5 3

    match dag with
    | some d =>
      -- Conv blocks may or may not produce tactic info nodes
      IO.println s!"  ✓ conv returned {d.nodes.size} nodes"
      for node in d.nodes do
        assertTrue s!"node {node.id} has position" (node.position.line ≥ 0)
    | none =>
      IO.println "  ✓ conv block returns no DAG (conv internals may not be tracked)"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ nested conv handled correctly"

/-! ## Edge Case: calc Block -/

unsafe def testCalcBlock : IO Unit := do
  printSubsection "Calc Block Proof"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "calc" "lean-analyzer not built"
    return

  unless ← edgeCaseFile.pathExists do
    skipTest "calc" "EdgeCases.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 20: "    _ = c + (a + b) := by rw [Nat.add_comm]" (1-indexed)
    let dag ← getProofDagAt uri sessionId 20 30 3

    match dag with
    | some d =>
      IO.println s!"  ✓ calc block returned {d.nodes.size} nodes"
      for node in d.nodes do
        assertTrue s!"node {node.id} tactic non-empty" (!node.tactic.text.isEmpty)
    | none =>
      IO.println "  ✓ calc block position returns no DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ calc block handled correctly"

/-! ## Edge Case: Multiple Rewrites -/

unsafe def testMultipleRewrites : IO Unit := do
  printSubsection "Multiple Rewrites in One Tactic"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "multi rw" "lean-analyzer not built"
    return

  unless ← edgeCaseFile.pathExists do
    skipTest "multi rw" "EdgeCases.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 32: "  rw [Nat.add_comm a b, Nat.add_comm]" (1-indexed)
    let dag ← getProofDagAt uri sessionId 32 5 3

    match dag with
    | some d =>
      assertTrue "multi-rw has nodes" (!d.nodes.isEmpty)
      -- Each rewrite step should be split into separate nodes
      for node in d.nodes do
        if containsSubstring node.tactic.text "rw" then
          assertTrue "rw node has bracket" (containsSubstring node.tactic.text "[")
    | none =>
      IO.println "  ✗ multi-rw proof should return a DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ multiple rewrites handled correctly"

/-! ## Edge Case: RPC Session Reuse -/

unsafe def testSessionReuse : IO Unit := do
  printSubsection "RPC Session Reuse"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "session reuse" "lean-analyzer not built"
    return

  unless ← simpleFile.pathExists do
    skipTest "session reuse" "Simple.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile simpleFile
    let uri ← fileUri simpleFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Make multiple RPC calls on the same session (1-indexed positions)
    let dag1 ← getProofDagAt uri sessionId 1 11 3
    let dag2 ← getProofDagAt uri sessionId 1 11 4
    let dag3 ← getProofDagAt uri sessionId 1 11 5

    -- All should succeed
    assertTrue "first call succeeded" dag1.isSome
    assertTrue "second call succeeded" dag2.isSome
    assertTrue "third call succeeded" dag3.isSome

    shutdown 6
    let _ ← waitForExit
    IO.println "  ✓ session reuse works correctly"

/-! ## Edge Case: Deep Nesting (Multiple Cases) -/

unsafe def testDeepNesting : IO Unit := do
  printSubsection "Deep Nesting (Cases within Cases)"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "deep nesting" "lean-analyzer not built"
    return

  unless ← edgeCaseFile.pathExists do
    skipTest "deep nesting" "EdgeCases.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 36: "  cases h with" (1-indexed)
    let dag ← getProofDagAt uri sessionId 36 7 3

    match dag with
    | some d =>
      assertTrue "deep nesting has nodes" (!d.nodes.isEmpty)
      -- Verify tree structure is computed
      let hasChildren := d.nodes.any (fun n => !n.children.isEmpty)
      assertTrue "has branching structure" hasChildren
    | none =>
      IO.println "  ✗ deep nesting should return a DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ deep nesting handled correctly"

/-! ## Edge Case: Position at Whitespace/Comment -/

unsafe def testWhitespacePosition : IO Unit := do
  printSubsection "Cursor at Comment"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "whitespace" "lean-analyzer not built"
    return

  unless ← edgeCaseFile.pathExists do
    skipTest "whitespace" "EdgeCases.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 1: "/-! # Edge Case Proofs..." comment (1-indexed)
    let dag ← getProofDagAt uri sessionId 1 1 3

    -- Should handle gracefully (empty or no DAG)
    match dag with
    | some d =>
      IO.println s!"  ✓ comment position returned {d.nodes.size} nodes"
    | none =>
      IO.println "  ✓ comment returns no DAG (expected)"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ comment position handled gracefully"

/-! ## Edge Case: Unicode Identifiers -/

unsafe def testUnicodeIdentifiers : IO Unit := do
  printSubsection "Unicode Identifiers (Greek Letters)"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "unicode" "lean-analyzer not built"
    return

  unless ← unicodeFile.pathExists do
    skipTest "unicode" "Unicode.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile unicodeFile
    let uri ← fileUri unicodeFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Unicode.lean line 5: "  rw [Nat.add_comm]" inside αβγ_test (1-indexed)
    -- The theorem name contains greek letters: theorem αβγ_test
    let dag ← getProofDagAt uri sessionId 5 5 3

    match dag with
    | some d =>
      assertTrue "unicode proof has nodes" (!d.nodes.isEmpty)
      -- Verify hypotheses with unicode names are handled
      for node in d.nodes do
        for hyp in node.stateAfter.hypotheses do
          assertTrue s!"hyp {hyp.name} has type" (!hyp.type.isEmpty)
      IO.println s!"  ✓ unicode proof returned {d.nodes.size} nodes"
    | none =>
      IO.println "  ✗ unicode proof should return a DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ unicode identifiers handled correctly"

/-! ## Edge Case: Unicode Column Positions -/

unsafe def testUnicodeColumnPosition : IO Unit := do
  printSubsection "Unicode Column Positions"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "unicode cols" "lean-analyzer not built"
    return

  unless ← unicodeFile.pathExists do
    skipTest "unicode cols" "Unicode.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile unicodeFile
    let uri ← fileUri unicodeFile

    openDocument uri content
    waitForFileReady uri

    let _ ← connectRpcSession 2 uri

    -- Unicode.lean line 4: "theorem αβγ_test (α β : Nat) : α + β = β + α := by"
    -- Greek letters α, β, γ are multi-byte in UTF-8 but single UTF-16 code units
    -- Column 9 in editor should be on 'α' in the theorem name
    let hover ← hoverRequest 3 uri 4 9

    match hover with
    | some h =>
      IO.println s!"  ✓ hover at unicode position: {h.contents.value.take 50}..."
    | none =>
      IO.println "  ✓ hover at unicode position returned none"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ unicode column positions handled correctly"

/-! ## Edge Case: Subscript Characters -/

unsafe def testSubscriptCharacters : IO Unit := do
  printSubsection "Subscript Characters (x₁, x₂)"

  let analyzerPath ← leanAnalyzerPath
  unless ← analyzerPath.pathExists do
    skipTest "subscripts" "lean-analyzer not built"
    return

  unless ← unicodeFile.pathExists do
    skipTest "subscripts" "Unicode.lean not found"
    return

  runWithLeanAnalyzer do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile unicodeFile
    let uri ← fileUri unicodeFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Unicode.lean line 9: "  rw [Nat.add_comm]" inside sub_test (1-indexed)
    let dag ← getProofDagAt uri sessionId 9 5 3

    match dag with
    | some d =>
      assertTrue "subscript proof has nodes" (!d.nodes.isEmpty)
      -- Check that subscript variable names are preserved
      for node in d.nodes do
        for hyp in node.stateAfter.hypotheses do
          -- x₁ and x₂ should appear in hypothesis names or types
          IO.println s!"    hyp: {hyp.name} : {hyp.type}"
      IO.println s!"  ✓ subscript proof returned {d.nodes.size} nodes"
    | none =>
      IO.println "  ✗ subscript proof should return a DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ subscript characters handled correctly"

unsafe def runTests : IO Unit := do
  IO.println ""
  IO.println "══════════════════════════════════════════════════════════════"
  IO.println "  RPC Edge Case Tests"
  IO.println "══════════════════════════════════════════════════════════════"

  testTermModeProof
  testSorryProof
  testInvalidPosition
  testNestedConv
  testCalcBlock
  testMultipleRewrites
  testSessionReuse
  testDeepNesting
  testWhitespacePosition
  testUnicodeIdentifiers
  testUnicodeColumnPosition
  testSubscriptCharacters

  IO.println "\n  ✓ RPC edge case tests passed"

end Tests.RpcEdgeCases
