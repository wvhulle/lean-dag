import Lean
import Lean.Data.Lsp.Ipc
import LeanDag
import Tests.LspClient
import Tests.Harness

namespace Tests.RpcProofDag

open Lean Lsp Ipc JsonRpc LeanDag Tests.LspClient Tests.Harness

def logicFile : System.FilePath := testProjectPath / "Logic.lean"
def inductionFile : System.FilePath := testProjectPath / "Induction.lean"

def parseProofDag (json : Json) : Except String ProofDag :=
  match json.getObjVal? "proofDag" with
  | .ok dagJson => FromJson.fromJson? dagJson
  | .error e => .error s!"Missing proofDag field: {e}"

/-- Get proof DAG at position. Line/col are 1-indexed (editor style). -/
def getProofDagAt (uri : String) (sessionId : UInt64) (line col : Nat) (requestId : Nat) : IpcM ProofDag := do
  let result ← callRpc requestId sessionId uri line col "LeanDag.getProofDag" (Json.mkObj [("mode", "tree")])
  match parseProofDag result with
  | .ok dag => return dag
  | .error e => throw <| IO.userError s!"Failed to parse ProofDag: {e}"

unsafe def testLinearProofStructure : IO Unit := do
  printSubsection "Linear Proof - contrapositive"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 4: "  intro hnq hp" (1-indexed)
    let dag ← getProofDagAt uri sessionId 4 5 3

    -- Verify basic structure
    assertTrue "has nodes" (!dag.nodes.isEmpty)
    assertSome "has root" dag.root
    assertSome "has currentNode" dag.currentNode

    -- Verify initial state has the theorem goal
    assertTrue "initialState has goal" (!dag.initialState.goals.isEmpty)
    let initialGoal := dag.initialState.goals[0]!
    assertTrue "initial goal has type" (!initialGoal.type.isEmpty)
    assertTrue "initial goal has id" (!initialGoal.id.isEmpty)

    -- Verify nodes have required fields for TUI
    for node in dag.nodes do
      assertTrue s!"node {node.id} has tactic text" (!node.tactic.text.isEmpty)
      assertTrue s!"node {node.id} has position" (node.position.line ≥ 0)

      -- stateBefore and stateAfter must exist
      -- Goals in states must have required fields
      for goal in node.stateBefore.goals do
        assertTrue s!"node {node.id} stateBefore goal has type" (!goal.type.isEmpty)
        assertTrue s!"node {node.id} stateBefore goal has id" (!goal.id.isEmpty)

      for goal in node.stateAfter.goals do
        assertTrue s!"node {node.id} stateAfter goal has type" (!goal.type.isEmpty)
        assertTrue s!"node {node.id} stateAfter goal has id" (!goal.id.isEmpty)

      -- Hypotheses must have required fields
      for hyp in node.stateBefore.hypotheses do
        assertTrue s!"node {node.id} hyp has name" (!hyp.name.isEmpty)
        assertTrue s!"node {node.id} hyp has type" (!hyp.type.isEmpty)
        assertTrue s!"node {node.id} hyp has id" (!hyp.id.isEmpty)

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ linear proof structure validated"

unsafe def testBranchingProofStructure : IO Unit := do
  printSubsection "Branching Proof - or_assoc_logic"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 23: "    cases h with" inside or_assoc_logic (1-indexed)
    let dag ← getProofDagAt uri sessionId 23 7 3

    assertTrue "has nodes" (!dag.nodes.isEmpty)
    assertSome "has root" dag.root

    -- Verify all nodes have valid structure
    for node in dag.nodes do
      -- Parent references should be valid (if present)
      if let some parentId := node.parent then
        assertTrue s!"node {node.id} parent {parentId} exists" (dag.nodes.any (·.id == parentId))

      -- Children references should be valid
      for childId in node.children do
        assertTrue s!"node {node.id} child {childId} exists" (dag.nodes.any (·.id == childId))

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ branching proof structure validated"

unsafe def testInductionProofStructure : IO Unit := do
  printSubsection "Induction Proof - nat_add_zero"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile inductionFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile inductionFile
    let uri ← fileUri inductionFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Induction.lean line 5: "  | zero => rfl" (1-indexed)
    let dag ← getProofDagAt uri sessionId 5 5 3

    assertTrue "has nodes" (!dag.nodes.isEmpty)

    -- Verify goal types are non-empty strings (not hygienic names)
    for node in dag.nodes do
      for goal in node.stateAfter.goals do
        -- username should be None or a visible name (filtered)
        if let some name := goal.username then
          assertTrue s!"goal username is visible" (!name.isEmpty && !containsSubstring name "._hyg.")

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ induction proof structure validated"

unsafe def testGotoLocationsField : IO Unit := do
  printSubsection "GotoLocations Field Present"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 4: "  intro hnq hp" (1-indexed)
    let dag ← getProofDagAt uri sessionId 4 5 3

    -- Verify gotoLocations field exists in goals (even if empty)
    for goal in dag.initialState.goals do
      -- The field should exist (default value is empty GotoLocations)
      -- We just verify the structure is valid by accessing it
      let _ := goal.gotoLocations
      IO.println s!"  ✓ initialState goal has gotoLocations field"

    for node in dag.nodes do
      for goal in node.stateAfter.goals do
        let _ := goal.gotoLocations
      for hyp in node.stateAfter.hypotheses do
        let _ := hyp.gotoLocations

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ gotoLocations fields present"

unsafe def testUsernameFiltering : IO Unit := do
  printSubsection "Username Filtering"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath

  let simpleFile := testProjectPath / "Simple.lean"
  requireFile simpleFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile simpleFile
    let uri ← fileUri simpleFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Simple.lean line 1: "theorem simple_rfl : 1 = 1 := by rfl" (1-indexed)
    let dag ← getProofDagAt uri sessionId 1 11 3

    -- Verify anonymous usernames are filtered to None
    for goal in dag.initialState.goals do
      if let some name := goal.username then
        assertTrue "username not [anonymous]" (name != "[anonymous]")
        assertTrue "username not hygienic" (!containsSubstring name "._hyg." && !containsSubstring name "._@.")

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ username filtering correct"

unsafe def testNewHypothesesIndices : IO Unit := do
  printSubsection "New Hypotheses Indices"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 4: "  intro hnq hp" (1-indexed)
    let dag ← getProofDagAt uri sessionId 4 5 3

    for node in dag.nodes do
      -- newHypotheses indices must be valid
      for idx in node.newHypotheses do
        assertTrue s!"node {node.id} newHyp idx {idx} valid"
          (idx < node.stateAfter.hypotheses.length)

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ newHypotheses indices valid"

unsafe def testTacticInfoFields : IO Unit := do
  printSubsection "Tactic Info Fields"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 4: "  intro hnq hp" (1-indexed)
    let dag ← getProofDagAt uri sessionId 4 5 3

    for node in dag.nodes do
      -- tactic.text must be non-empty
      assertTrue s!"node {node.id} tactic text non-empty" (!node.tactic.text.isEmpty)

      -- dependsOn should be a list (can be empty)
      let _ := node.tactic.dependsOn

      -- theoremsUsed should be a list (can be empty)
      let _ := node.tactic.theoremsUsed

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ tactic info fields valid"

def setsFile : System.FilePath := testProjectPath / "Sets.lean"

unsafe def testGotoLocationsPopulated : IO Unit := do
  printSubsection "GotoLocations Populated (Sets proof)"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile setsFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile setsFile
    let uri ← fileUri setsFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Sets.lean line 8: "  ext x" in inter_comm_set (1-indexed)
    -- This proof has hypotheses s, t : Set Nat which should have goto locations
    let dag ← getProofDagAt uri sessionId 8 5 3

    assertTrue "has nodes" (!dag.nodes.isEmpty)

    -- Check that at least some hypotheses have goto locations
    let mut foundHypWithDef := false
    let mut foundHypWithTypeDef := false
    let mut foundGoalWithDef := false

    for node in dag.nodes do
      for hyp in node.stateAfter.hypotheses do
        if hyp.gotoLocations.definition.isSome then
          foundHypWithDef := true
          IO.println s!"  Found hyp '{hyp.name}' with definition location"
        if hyp.gotoLocations.typeDef.isSome then
          foundHypWithTypeDef := true
          IO.println s!"  Found hyp '{hyp.name}' with typeDef location: {hyp.gotoLocations.typeDef.get!.uri}"

      for goal in node.stateAfter.goals do
        if goal.gotoLocations.definition.isSome then
          foundGoalWithDef := true
          IO.println s!"  Found goal with definition location: {goal.gotoLocations.definition.get!.uri}"

    -- At least hypotheses should have typeDef (Set is resolvable)
    assertTrue "found hyp with typeDef location" foundHypWithTypeDef

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ gotoLocations populated for relevant items"

unsafe def runTests : IO Unit := do
  printSection "RPC ProofDag Validation Tests"

  testLinearProofStructure
  testBranchingProofStructure
  testInductionProofStructure
  testGotoLocationsField
  testGotoLocationsPopulated
  testUsernameFiltering
  testNewHypothesesIndices
  testTacticInfoFields

  IO.println "\n  ✓ RPC ProofDag tests passed"

end Tests.RpcProofDag
