import Lean
import LeanAnalyzer.Types
import LeanAnalyzer.Conversion
import Services.BetterParser

open Lean Paperproof.Services

namespace LeanAnalyzer

abbrev GoalStepIndex := Std.HashMap String (List Nat)

def buildGoalIndex (steps : List ProofStep) : GoalStepIndex :=
  steps.zipIdx.foldl (init := {}) fun acc (step, i) =>
    let goalId := step.goalBefore.id.name.toString
    acc.alter goalId fun
      | none => some [i]
      | some indices => some (indices ++ [i])

def goalHasSolver (index : GoalStepIndex) (goalId : String) (afterStep : Nat) : Bool :=
  match index.get? goalId with
  | none => false
  | some indices => indices.any (· > afterStep)

structure TreeBuildState where
  nodes : Array ProofDagNode
  orphans : List Nat := []
  deriving Inhabited

def TreeBuildState.updateNode (state : TreeBuildState) (idx : Nat)
    (f : ProofDagNode → ProofDagNode) : TreeBuildState :=
  if h : idx < state.nodes.size then
    { state with nodes := state.nodes.set idx (f state.nodes[idx]) }
  else state

def TreeBuildState.addOrphan (state : TreeBuildState) (idx : Nat) : TreeBuildState :=
  { state with orphans := state.orphans ++ [idx] }

def analyzeGoal (index : GoalStepIndex) (stepIdx : Nat) 
    (g : Paperproof.Services.GoalInfo) : String × Bool :=
  let goalId := g.id.name.toString
  let solved := goalHasSolver index goalId stepIdx
  (goalId, solved)

def analyzeStepGoals (index : GoalStepIndex) (stepIdx : Nat) (step : ProofStep)
    : List String × Bool :=
  let processGoal (acc : List String × Bool) (g : Paperproof.Services.GoalInfo) : List String × Bool :=
    let (childGoalIds, hasUnsolved) := acc
    let (goalId, solved) := analyzeGoal index stepIdx g
    let newUnsolved := hasUnsolved || !solved
    let newChildIds := if childGoalIds.contains goalId then childGoalIds else childGoalIds ++ [goalId]
    (newChildIds, newUnsolved)
  
  let init : List String × Bool := ([], false)
  let afterSpawned := step.spawnedGoals.foldl processGoal init
  step.goalsAfter.foldl processGoal afterSpawned

def getStep? (steps : List ProofStep) (idx : Nat) : Option ProofStep :=
  steps[idx]?

partial def buildBranchRecursive (state : TreeBuildState) (steps : List ProofStep)
    (index : GoalStepIndex) (goalId : String) (startFrom : Nat)
    (parentId : Option Nat) (depth : Nat) : TreeBuildState × Option Nat :=
  -- Find step that works on this goal (>= startFrom)
  let stepIndices := index.get? goalId |>.getD []
  match stepIndices.find? (· >= startFrom) with
  | none => (state, none)
  | some stepIdx =>
    let nodeId := stepIdx

    -- Get step and analyze its goals
    match getStep? steps stepIdx with
    | none => (state, none)
    | some step =>
      let (childGoalIds, hasUnsolved) := analyzeStepGoals index stepIdx step

      -- Update node with tree structure
      let state := state.updateNode stepIdx fun n =>
        { n with parent := parentId, depth, hasUnsolvedSpawnedGoals := hasUnsolved }

      -- Add as child of parent
      let state := match parentId with
        | none => state
        | some pid => state.updateNode pid fun n =>
            if n.children.contains nodeId then n
            else { n with children := n.children ++ [nodeId] }

      -- Recursively process children
      let state := childGoalIds.foldl (init := state) fun state childGoalId =>
        let (state', _) := buildBranchRecursive state steps index childGoalId (stepIdx + 1) (some nodeId) (depth + 1)
        state'

      (state, some nodeId)

def connectOrphanNodes (state : TreeBuildState) (steps : List ProofStep)
    (rootId : Nat) : TreeBuildState :=
  -- Find nodes with no parent (except root)
  let orphanIds := state.nodes.toList.filterMap fun n =>
    if n.parent.isNone && n.id != rootId then some n.id else none

  orphanIds.foldl (init := state) fun state orphanId =>
    match getStep? steps orphanId with
    | none => state
    | some orphanStep =>
      let orphanGoalId := orphanStep.goalBefore.id.name.toString

      -- Find parent by goal ID match in goalsAfter or spawnedGoals
      let parentOpt := state.nodes.toList.find? fun n =>
        match getStep? steps n.id with
        | none => false
        | some step =>
          step.goalsAfter.any (·.id.name.toString == orphanGoalId) ||
          step.spawnedGoals.any (·.id.name.toString == orphanGoalId)

      match parentOpt with
      | none =>
        -- No match found - mark as detached orphan
        state.addOrphan orphanId
      | some parent =>
        let parentId := parent.id
        let parentDepth := match state.nodes[parentId]? with
          | some n => n.depth
          | none => 0

        -- Connect orphan to parent
        let state := state.updateNode orphanId fun n =>
          { n with parent := some parentId, depth := parentDepth + 1 }
        state.updateNode parentId fun n =>
          if n.children.contains orphanId then n
          else { n with children := n.children ++ [orphanId] }

def findRootIndex (nodes : Array ProofDagNode) : Nat :=
  if nodes.isEmpty then 0
  else
    nodes.toList.zipIdx.foldl (init := 0) fun best (n, i) =>
      if i == 0 then 0
      else
        match nodes[best]? with
        | none => i
        | some bestNode =>
          if n.position.line < bestNode.position.line ||
             (n.position.line == bestNode.position.line && n.position.character < bestNode.position.character)
          then i else best

def buildTreeStructure (steps : List ProofStep) (nodes : Array ProofDagNode)
    : Array ProofDagNode × List Nat :=
  if steps.isEmpty then (nodes, [])
  else
    let rootIdx := findRootIndex nodes
    let index := buildGoalIndex steps
    let rootGoalId := match getStep? steps rootIdx with
      | none => ""
      | some step => step.goalBefore.id.name.toString

    let initialState : TreeBuildState := { nodes }

    -- Build tree recursively from root
    let (state, _) := buildBranchRecursive initialState steps index rootGoalId 0 none 0

    -- Connect any orphan nodes
    let state := connectOrphanNodes state steps rootIdx

    (state.nodes, state.orphans)

end LeanAnalyzer
