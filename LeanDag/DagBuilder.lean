import Lean
import LeanDag.Protocol
import LeanDag.InfoTreeParser
import LeanDag.DiffComputation

open Lean Elab

namespace LeanDag

open LeanDag.InfoTreeParser

/-! ## Definition Name Extraction -/

/-- Extract the definition name from the InfoTree by finding the enclosing command.
    Uses the same pattern as Lean's DocumentSymbol handler. -/
def getDefinitionName (tree : InfoTree) : Option String :=
  let names := tree.collectNodesBottomUp fun _ctx i _cs acc =>
    match i with
    | .ofCommandInfo ci =>
      -- For declarations: stx[1][1] contains the declId
      -- Pattern: `(declId|$id$[.{$ls,*}]?)` extracts the identifier
      let declId := ci.stx.getArg 1 |>.getArg 1
      let id := declId.getArg 0 |>.getId  -- First child of declId is the identifier
      if id.isAnonymous then acc else id.toString :: acc
    | _ => acc
  names.head?

/-! ## DAG Building -/

def CompleteProofDag.build (steps : List ParsedStep) (cursorPos : Lsp.Position)
    (definitionName : Option String := none) : CompleteProofDag :=
  if steps.isEmpty then {} else
  let stepsArray := steps.toArray
  -- Build goal ID to step index map: which step produces which goals
  -- goalsAfter are the goals that result from applying the tactic
  let goalToProducer : Std.HashMap String Nat := Id.run do
    let mut m : Std.HashMap String Nat := {}
    for h : idx in [:stepsArray.size] do
      let step := stepsArray[idx]
      for goal in step.goalsAfter do
        m := m.insert goal.mvarId.name.toString idx
    return m
  -- For each step, find parent (the step whose goalsAfter contains this step's goalBefore)
  let parentOf : Array (Option Nat) := stepsArray.map fun step =>
    goalToProducer.get? step.goalBefore.mvarId.name.toString
  -- Compute children from parent relationships
  let childrenOf : Array (List Nat) := Id.run do
    let mut result : Array (List Nat) := stepsArray.map (fun _ => [])
    for h : childIdx in [:parentOf.size] do
      if let some parentIdx := parentOf[childIdx] then
        if parentIdx < result.size then
          result := result.modify parentIdx (childIdx :: ·)
    return result
  -- Compute depth: count steps to root
  let depths : Array Nat := Id.run do
    let mut result := stepsArray.map (fun _ => 0)
    for h : idx in [:stepsArray.size] do
      let mut depth := 0
      let mut current := idx
      let mut visited : Std.HashSet Nat := {}
      while true do
        if visited.contains current then break
        visited := visited.insert current
        match parentOf[current]? with
        | some (some p) =>
          depth := depth + 1
          current := p
        | _ => break
      result := result.set! idx depth
    return result
  -- Build nodes with computed relationships
  let nodes := stepsArray.mapIdx fun idx step =>
    let goalBefore := step.goalBefore.obligation
    let goalsAfter := (step.goalsAfter.map (·.obligation)).toArray
    let hypsBefore := (step.goalBefore.hypotheses.filter (·.name != "")).toArray
    -- Get hypotheses from first goal after tactic (if any), otherwise use before
    let hypsAfter := match step.goalsAfter.head? with
      | some g => (g.hypotheses.filter (·.name != "")).toArray
      | none => hypsBefore
    -- Compute new hypotheses: indices in hypsAfter for hyps not in hypsBefore
    let hypIdsBefore : Std.HashSet String := Std.HashSet.ofArray (hypsBefore.map (·.id))
    let new_hypothesis_indices := Id.run do
      let mut result : Array Nat := #[]
      for h : i in [:hypsAfter.size] do
        let hyp := hypsAfter[i]!
        if !hypIdsBefore.contains hyp.id then
          result := result.push i
      return result
    -- Build raw states (without diff)
    let rawStateBefore : TacticProofState := { goals := #[goalBefore], hypotheses := hypsBefore }
    let rawStateAfter : TacticProofState := { goals := goalsAfter, hypotheses := hypsAfter }
    -- Apply diff highlighting: proof_state_before shows what will change, proof_state_after shows what changed
    let proof_state_before := rawStateBefore.diffBefore rawStateAfter
    let proof_state_after := rawStateBefore.diffAfter rawStateAfter
    { id := idx
      tactic := { text := step.tacticString, hypothesis_dependencies := step.hypothesis_dependencies.toArray, referenced_theorems := (step.theorems.map (·.name)).toArray }
      position := step.position.start  -- Coerces to LineCharacterPosition
      proof_state_before
      proof_state_after
      new_hypothesis_indices
      children := (childrenOf[idx]?.getD []).toArray
      parent := parentOf[idx]?.join
      depth := depths[idx]?.getD 0 }
  -- Find all nodes with no parent (potential roots/orphans)
  let rootCandidates := nodes.toList.filterMap fun n =>
    if n.parent.isNone then some n.id else none
  -- First rootless node is the main root, rest are orphans (disconnected components)
  let (root, orphans) := match rootCandidates with
    | [] => (none, #[])
    | r :: rest => (some r, rest.toArray)
  -- Find current node: the node whose position is closest to (but not after) cursor
  let current_node_id : Option Nat := Id.run do
    let mut best : Option Nat := none
    let mut bestPos : Lsp.Position := ⟨0, 0⟩
    for h : i in [:nodes.size] do
      let node : ProofDagTacticNode := nodes[i]
      let pos : Lsp.Position := node.position
      -- Node is at or before cursor position
      if pos.line < cursorPos.line || (pos.line == cursorPos.line && pos.character <= cursorPos.character) then
        -- And it's better than current best (closer to cursor)
        if best.isNone || pos.line > bestPos.line || (pos.line == bestPos.line && pos.character > bestPos.character) then
          best := some node.id
          bestPos := pos
    return best
  { nodes, root_node_id := root, orphans, current_node_id, initial_proof_state := some nodes[0]!.proof_state_before, definition_name := definitionName }

end LeanDag
