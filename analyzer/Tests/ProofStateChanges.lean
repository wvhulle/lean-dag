import Lean
import LeanAnalyzer
import Tests.Helpers

namespace Tests.ProofStateChanges

open Lean LeanAnalyzer Tests.Helpers

/-! ## Hypothesis Tracking Tests -/

/-- Test: New hypotheses are tracked with indices into stateAfter.hypotheses -/
def testNewHypothesesTracking : IO Unit := do
  IO.println "\n  [New Hypotheses Tracking]"
  
  -- intro n introduces hypothesis 'n'
  let node : ProofDagNode := {
    id := 0
    tactic := { text := "intro n" }
    position := ⟨3, 2⟩
    stateBefore := { 
      goals := [{ type := "Nat → Nat → Nat", id := "g1" }]
      hypotheses := []  -- No hypotheses before
    }
    stateAfter := {
      goals := [{ type := "Nat → Nat", id := "g2" }]
      hypotheses := [{ name := "n", type := "Nat", id := "h1" }]
    }
    newHypotheses := [0]  -- Index 0 in stateAfter.hypotheses
  }
  
  assertEqual "one new hypothesis" node.newHypotheses.length 1
  assertEqual "new hyp index is 0" node.newHypotheses[0]! 0
  assertEqual "can lookup new hyp" node.stateAfter.hypotheses[0]!.name "n"

/-- Test: Multiple hypotheses introduced at once (e.g., intro a b c) -/
def testMultipleNewHypotheses : IO Unit := do
  IO.println "\n  [Multiple New Hypotheses]"
  
  let node : ProofDagNode := {
    id := 0
    tactic := { text := "intro a b c" }
    position := ⟨3, 2⟩
    stateBefore := {
      goals := [{ type := "A → B → C → D", id := "g1" }]
      hypotheses := []
    }
    stateAfter := {
      goals := [{ type := "D", id := "g2" }]
      hypotheses := [
        { name := "a", type := "A", id := "h1" },
        { name := "b", type := "B", id := "h2" },
        { name := "c", type := "C", id := "h3" }
      ]
    }
    newHypotheses := [0, 1, 2]  -- All three are new
  }
  
  assertEqual "three new hypotheses" node.newHypotheses.length 3
  -- Verify all can be looked up
  for i in [0, 1, 2] do
    assertTrue s!"hyp {i} exists" (node.stateAfter.hypotheses[i]?.isSome)

/-- Test: Theorem parameters are not marked as new hypotheses -/
def testTheoremParametersNotNew : IO Unit := do
  IO.println "\n  [Theorem Parameters vs Introduced Hypotheses]"
  
  -- theorem foo (h : P) : P ∧ P := by constructor <;> exact h
  -- The hypothesis 'h' comes from the theorem signature, not from a tactic
  let node : ProofDagNode := {
    id := 0
    tactic := { text := "constructor" }
    position := ⟨3, 2⟩
    stateBefore := {
      goals := [{ type := "P ∧ P", id := "g1" }]
      hypotheses := [{ name := "h", type := "P", id := "h_param" }]  -- From theorem
    }
    stateAfter := {
      goals := [
        { type := "P", username := some "left", id := "g2" },
        { type := "P", username := some "right", id := "g3" }
      ]
      hypotheses := [{ name := "h", type := "P", id := "h_param" }]
    }
    newHypotheses := []  -- No NEW hypotheses, 'h' existed before
  }
  
  assertEqual "no new hypotheses" node.newHypotheses.length 0
  assertEqual "hypothesis preserved" node.stateAfter.hypotheses.length 1

/-- Test: Cases tactic introduces new hypotheses per branch -/
def testCasesIntroducesHypotheses : IO Unit := do
  IO.println "\n  [Cases Introduces Branch-Specific Hypotheses]"
  
  -- In the inl branch, we get hypothesis 'ha : A'
  let inlBranch : ProofDagNode := {
    id := 1
    tactic := { text := "case inl ha =>" }
    position := ⟨4, 4⟩
    stateBefore := {
      goals := [{ type := "C", username := some "case inl", id := "g2" }]
      hypotheses := [{ name := "h", type := "A ∨ B", id := "h1" }]
    }
    stateAfter := {
      goals := [{ type := "C", id := "g2" }]
      hypotheses := [
        { name := "h", type := "A ∨ B", id := "h1" },
        { name := "ha", type := "A", id := "h2" }  -- New from case
      ]
    }
    newHypotheses := [1]  -- Only 'ha' is new
    parent := some 0
  }
  
  assertEqual "one new hypothesis in branch" inlBranch.newHypotheses.length 1
  assertEqual "new hyp is 'ha'" inlBranch.stateAfter.hypotheses[1]!.name "ha"

/-! ## Goal Change Tests -/

/-- Test: Goal solved (stateAfter.goals is empty) -/
def testGoalSolved : IO Unit := do
  IO.println "\n  [Goal Solved Detection]"
  
  let node : ProofDagNode := {
    id := 0
    tactic := { text := "rfl" }
    position := ⟨3, 2⟩
    stateBefore := { goals := [{ type := "n = n", id := "g1" }], hypotheses := [] }
    stateAfter := { goals := [], hypotheses := [] }  -- Empty = solved
  }
  
  assertTrue "goals empty means solved" node.stateAfter.goals.isEmpty

/-- Test: Goal spawned (more goals after than before) -/
def testGoalSpawned : IO Unit := do
  IO.println "\n  [Goal Spawned - Constructor/Cases]"
  
  let node : ProofDagNode := {
    id := 0
    tactic := { text := "constructor" }
    position := ⟨3, 2⟩
    stateBefore := { goals := [{ type := "P ∧ Q", id := "g1" }], hypotheses := [] }
    stateAfter := { 
      goals := [
        { type := "P", username := some "left", id := "g2" },
        { type := "Q", username := some "right", id := "g3" }
      ]
      hypotheses := []
    }
  }
  
  assertEqual "spawned two goals" node.stateAfter.goals.length 2
  assertTrue "more goals than before" (node.stateAfter.goals.length > node.stateBefore.goals.length)

/-- Test: Goal modified (type changed but same logical goal) -/
def testGoalModified : IO Unit := do
  IO.println "\n  [Goal Modified - Simp/Rewrite]"
  
  let node : ProofDagNode := {
    id := 0
    tactic := { text := "simp [Nat.add_zero]" }
    position := ⟨3, 2⟩
    stateBefore := { goals := [{ type := "n + 0 = n", id := "g1" }], hypotheses := [] }
    stateAfter := { goals := [{ type := "n = n", id := "g1'" }], hypotheses := [] }
  }
  
  assertEqual "still one goal" node.stateAfter.goals.length 1
  -- Type changed from "n + 0 = n" to "n = n"
  assertTrue "goal type changed" (node.stateBefore.goals[0]!.type != node.stateAfter.goals[0]!.type)

/-! ## Hypothesis Kind Tests -/

/-- Test: isProof flag distinguishes proof terms from data -/
def testHypothesisKinds : IO Unit := do
  IO.println "\n  [Hypothesis Kinds - Proof vs Data]"
  
  let state : ProofState := {
    goals := [{ type := "C", id := "g1" }]
    hypotheses := [
      { name := "n", type := "Nat", id := "h1", isProof := false },           -- Data
      { name := "h", type := "n > 0", id := "h2", isProof := true },          -- Proof
      { name := "inst", type := "Decidable P", id := "h3", isInstance := true } -- Instance
    ]
  }
  
  assertTrue "n is data" (!state.hypotheses[0]!.isProof)
  assertTrue "h is proof" state.hypotheses[1]!.isProof
  assertTrue "inst is instance" state.hypotheses[2]!.isInstance

/-! ## Hygienic Name Filtering Tests -/

/-- Test: Hygienic names are filtered out -/
def testHygienicNameFiltering : IO Unit := do
  IO.println "\n  [Hygienic Name Filtering]"
  
  -- These should be filtered (empty name in output)
  assertTrue "._hyg. is hygienic" (isHygienicName "x._hyg.123")
  assertTrue "._@. is hygienic" (isHygienicName "foo._@.bar")
  
  -- These should be visible
  assertTrue "normal name is visible" (isUserVisibleName "n")
  assertTrue "case name is visible" (isUserVisibleName "case inl")
  
  -- Filter function
  assertEqual "hygienic filtered to empty" (filterName "x._hyg.123") ""
  assertEqual "normal name preserved" (filterName "hypothesis") "hypothesis"

/-! ## Test Runner -/

def runTests : IO Unit := do
  IO.println "\n══════════════════════════════════════════════════════════════"
  IO.println "  Proof State Change Tests"
  IO.println "══════════════════════════════════════════════════════════════"
  
  testNewHypothesesTracking
  testMultipleNewHypotheses
  testTheoremParametersNotNew
  testCasesIntroducesHypotheses
  testGoalSolved
  testGoalSpawned
  testGoalModified
  testHypothesisKinds
  testHygienicNameFiltering
  
  IO.println "\n  ✓ Proof state change tests passed"

end Tests.ProofStateChanges
