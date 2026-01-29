import Lean
import LeanAnalyzer.Types
import LeanAnalyzer.Conversion
import LeanAnalyzer.TreeBuilder
import Services.BetterParser

open Lean Paperproof.Services

namespace LeanAnalyzer

def findCurrentNode (nodes : Array ProofDagNode) (line col : Nat) : Option Nat :=
  if nodes.isEmpty then none
  else
    let pos := Lsp.Position.mk line col
    let candidates := nodes.toList.filter fun n =>
      n.position.line < pos.line ||
      (n.position.line == pos.line && n.position.character <= pos.character)
    match candidates.getLast? with
    | none => some 0
    | some n => some n.id

def buildProofDag (steps : List ProofStep) (line col : Nat)
    (definitionName : Option String := none) : ProofDag :=
  if steps.isEmpty then {}
  else
    let nodes := (steps.zipIdx.map fun (step, i) => nodeFromProofStep i step).toArray

    let rootIdx := findRootIndex nodes

    let (nodes, orphans) := buildTreeStructure steps nodes

    let initialState := match getStep? steps rootIdx with
      | none => {}
      | some step => proofStateFromGoal step.goalBefore

    let currentNode := findCurrentNode nodes line col

    { nodes
      root := some rootIdx
      currentNode
      initialState
      definitionName
      orphans }

def buildProofDagFromResult (result : Result) (line col : Nat)
    (definitionName : Option String := none) : ProofDag :=
  buildProofDag result.steps line col definitionName

end LeanAnalyzer
