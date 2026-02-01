import Lean
import LeanDag
import Tests.Harness

namespace Tests.UnitProofDag

open Lean LeanDag Tests.Harness

/-! ## DAG Structure Tests -/

/-- Test: Empty proof produces empty DAG. -/
def testEmptyProofDag : IO Unit := do
  IO.println "\n  [Empty Proof DAG]"
  let dag : CompleteProofDag := {}

  assertEqual "no nodes" dag.nodes.size 0
  assertTrue "no root" dag.root.isNone
  assertEqual "no orphans" dag.orphans.length 0

/-- Test: Single tactic proof has one node as both root and leaf. -/
def testSingleTacticProof : IO Unit := do
  IO.println "\n  [Single Tactic Proof]"

  -- Simulates: theorem foo : True := by trivial
  let node : ProofDagTacticNode := {
    id := 0
    tactic := { text := "trivial", hypothesis_dependencies := [], referenced_theorems := ["True.intro"] }
    position := ⟨3, 2⟩
    proof_state_before := { goals := [{ type := "True", id := "g1" }], hypotheses := [] }
    proof_state_after := { goals := [], hypotheses := [] }  -- Goal solved
  }

  let dag : CompleteProofDag := {
    nodes := #[node]
    root := some 0
    current_node_id := some 0
    initial_proof_state := node.proof_state_before
  }

  assertEqual "one node" dag.nodes.size 1
  assertEqual "root is 0" dag.root (some 0)
  assertTrue "node is leaf (no children)" dag.nodes[0]!.children.isEmpty
  assertTrue "goal is solved" dag.nodes[0]!.proof_state_after.goals.isEmpty

/-- Test: Linear proof chain forms a path in the DAG. -/
def testLinearProofChain : IO Unit := do
  IO.println "\n  [Linear Proof Chain]"

  -- Simulates: theorem foo (n : Nat) : n = n := by intro; rfl
  let nodes : Array ProofDagTacticNode := #[
    { id := 0
      tactic := { text := "intro n" }
      position := ⟨3, 2⟩
      proof_state_before := { goals := [{ type := "∀ n, n = n", id := "g1" }], hypotheses := [] }
      proof_state_after := {
        goals := [{ type := "n = n", id := "g2" }]
        hypotheses := [{ name := "n", type := "Nat", id := "h1" }]
      }
      new_hypothesis_indices := [0]  -- Index of 'n' in proof_state_after.hypotheses
      children := [1]
      depth := 0 },
    { id := 1
      tactic := { text := "rfl" }
      position := ⟨4, 2⟩
      proof_state_before := {
        goals := [{ type := "n = n", id := "g2" }]
        hypotheses := [{ name := "n", type := "Nat", id := "h1" }]
      }
      proof_state_after := { goals := [], hypotheses := [{ name := "n", type := "Nat", id := "h1" }] }
      parent := some 0
      depth := 1 }
  ]

  let dag : CompleteProofDag := {
    nodes := nodes
    root := some 0
    initial_proof_state := nodes[0]!.proof_state_before
  }

  assertEqual "two nodes" dag.nodes.size 2
  assertEqual "node 0 has child 1" dag.nodes[0]!.children [1]
  assertEqual "node 1 has parent 0" dag.nodes[1]!.parent (some 0)
  assertEqual "node 0 depth is 0" dag.nodes[0]!.depth 0
  assertEqual "node 1 depth is 1" dag.nodes[1]!.depth 1

/-- Test: Branching proof (cases/induction) creates multiple children. -/
def testBranchingProof : IO Unit := do
  IO.println "\n  [Branching Proof - Cases/Induction]"

  -- Simulates: cases h with | inl => ... | inr => ...
  let nodes : Array ProofDagTacticNode := #[
    { id := 0
      tactic := { text := "cases h" }
      position := ⟨3, 2⟩
      proof_state_before := {
        goals := [{ type := "A ∨ B → C", id := "g1" }]
        hypotheses := [{ name := "h", type := "A ∨ B", id := "h1" }]
      }
      proof_state_after := {
        goals := [
          { type := "C", username := some "case inl", id := "g2" },
          { type := "C", username := some "case inr", id := "g3" }
        ]
        hypotheses := [{ name := "h", type := "A ∨ B", id := "h1" }]
      }
      children := [1, 2]
      depth := 0 },
    { id := 1
      tactic := { text := "exact ha" }
      position := ⟨4, 4⟩
      proof_state_before := {
        goals := [{ type := "C", username := some "case inl", id := "g2" }]
        hypotheses := [
          { name := "h", type := "A ∨ B", id := "h1" },
          { name := "ha", type := "A", id := "h2" }
        ]
      }
      proof_state_after := { goals := [], hypotheses := [] }
      new_hypothesis_indices := [1]  -- 'ha' is new
      parent := some 0
      depth := 1 },
    { id := 2
      tactic := { text := "exact hb" }
      position := ⟨5, 4⟩
      proof_state_before := {
        goals := [{ type := "C", username := some "case inr", id := "g3" }]
        hypotheses := [
          { name := "h", type := "A ∨ B", id := "h1" },
          { name := "hb", type := "B", id := "h3" }
        ]
      }
      proof_state_after := { goals := [], hypotheses := [] }
      new_hypothesis_indices := [1]  -- 'hb' is new
      parent := some 0
      depth := 1 }
  ]

  let dag : CompleteProofDag := {
    nodes := nodes
    root := some 0
    initial_proof_state := nodes[0]!.proof_state_before
  }

  assertEqual "three nodes" dag.nodes.size 3
  assertEqual "root has two children" dag.nodes[0]!.children.length 2
  assertEqual "both children have same parent"
    (dag.nodes[1]!.parent, dag.nodes[2]!.parent)
    (some 0, some 0)
  -- Verify case names are preserved
  assertEqual "first goal has case name"
    dag.nodes[0]!.proof_state_after.goals[0]!.username (some "case inl")

/-- Test: Orphan nodes are disconnected from main tree. -/
def testOrphanNodes : IO Unit := do
  IO.println "\n  [Orphan Nodes - Inline Proofs]"

  -- Simulates: have h : P := by some_tactic (inline proof)
  let nodes : Array ProofDagTacticNode := #[
    { id := 0
      tactic := { text := "have h : P := by sorry" }
      position := ⟨3, 2⟩
      proof_state_before := { goals := [{ type := "Q", id := "g1" }], hypotheses := [] }
      proof_state_after := {
        goals := [{ type := "Q", id := "g1" }]
        hypotheses := [{ name := "h", type := "P", id := "h1" }]
      }
      new_hypothesis_indices := [0]
      has_unsolved_spawned_goals := true  -- The inline proof wasn't fully resolved
      children := [2]
      depth := 0 },
    { id := 1  -- This is an orphan (from the inline `by sorry`)
      tactic := { text := "sorry" }
      position := ⟨3, 20⟩
      proof_state_before := { goals := [{ type := "P", id := "g_spawned" }], hypotheses := [] }
      proof_state_after := { goals := [], hypotheses := [] }
      depth := 0 },  -- No parent set
    { id := 2
      tactic := { text := "exact h" }
      position := ⟨4, 2⟩
      proof_state_before := {
        goals := [{ type := "Q", id := "g1" }]
        hypotheses := [{ name := "h", type := "P", id := "h1" }]
      }
      proof_state_after := { goals := [], hypotheses := [] }
      parent := some 0
      depth := 1 }
  ]

  let dag : CompleteProofDag := {
    nodes := nodes
    root := some 0
    orphans := [1]  -- Node 1 is disconnected
    initial_proof_state := nodes[0]!.proof_state_before
  }

  assertEqual "one orphan" dag.orphans.length 1
  assertEqual "orphan is node 1" dag.orphans[0]! 1
  assertTrue "orphan has no parent" dag.nodes[1]!.parent.isNone
  assertTrue "node 0 has unsolved spawned goals" dag.nodes[0]!.has_unsolved_spawned_goals

/-- Test: Current node tracking for cursor position. -/
def testCurrentNodeTracking : IO Unit := do
  IO.println "\n  [Current Node Tracking]"

  let nodes : Array ProofDagTacticNode := #[
    { id := 0, tactic := { text := "intro" }, position := ⟨3, 2⟩,
      proof_state_before := {}, proof_state_after := {}, children := [1] },
    { id := 1, tactic := { text := "simp" }, position := ⟨4, 2⟩,
      proof_state_before := {}, proof_state_after := {}, parent := some 0, children := [2] },
    { id := 2, tactic := { text := "rfl" }, position := ⟨5, 2⟩,
      proof_state_before := {}, proof_state_after := {}, parent := some 1 }
  ]

  -- Cursor at different positions
  let dag1 : CompleteProofDag := { nodes, root := some 0, current_node_id := some 0 }
  let dag2 : CompleteProofDag := { nodes, root := some 0, current_node_id := some 1 }
  let dag3 : CompleteProofDag := { nodes, root := some 0, current_node_id := some 2 }

  assertEqual "current node 0" dag1.current_node_id (some 0)
  assertEqual "current node 1" dag2.current_node_id (some 1)
  assertEqual "current node 2" dag3.current_node_id (some 2)

/-! ## Test Runner -/

def runTests : IO Unit := do
  IO.println "\n══════════════════════════════════════════════════════════════"
  IO.println "  ProofDag Structure Tests (Unit)"
  IO.println "══════════════════════════════════════════════════════════════"

  testEmptyProofDag
  testSingleTacticProof
  testLinearProofChain
  testBranchingProof
  testOrphanNodes
  testCurrentNodeTracking

  IO.println "\n  ✓ ProofDag unit tests passed"

end Tests.UnitProofDag
