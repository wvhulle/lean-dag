import LeanDag.Protocol
import Std.Data.HashMap
import Std.Data.HashSet

open Lean.Widget (DiffTag)

namespace LeanDag

/-! ## Diff Computation -/

/-- Direction of diff comparison, determining which tags to use. -/
private inductive DiffDirection where
  | before  -- Computing diff for "before" state (will change/delete, mark removed)
  | after   -- Computing diff for "after" state (was changed/inserted)

private def DiffDirection.changedTag : DiffDirection → DiffTag
  | .before => .willChange
  | .after => .wasChanged

private def DiffDirection.missingTag : DiffDirection → DiffTag
  | .before => .willDelete
  | .after => .wasInserted

private def DiffDirection.markRemoved : DiffDirection → Bool
  | .before => true
  | .after => false

private def diffHypotheses (source target : List HypothesisInfo) (dir : DiffDirection)
    : List HypothesisInfo :=
  let targetIds := Std.HashSet.ofList (target.map (·.id))
  let targetById : Std.HashMap String HypothesisInfo :=
    target.foldl (init := {}) fun m h => m.insert h.id h
  source.map fun h =>
    if targetIds.contains h.id then
      match targetById.get? h.id with
      | some th =>
        if h.type.toPlainText != th.type.toPlainText then
          { h with type := h.type.withDiff dir.changedTag }
        else h
      | none => h
    else if dir.markRemoved then
      { h with isRemoved := true, type := h.type.withDiff dir.missingTag }
    else
      { h with type := h.type.withDiff dir.missingTag }

private def diffGoals (source target : List GoalInfo) (dir : DiffDirection) : List GoalInfo :=
  let targetIds := Std.HashSet.ofList (target.map (·.id))
  let targetById : Std.HashMap String GoalInfo :=
    target.foldl (init := {}) fun m g => m.insert g.id g
  source.map fun g =>
    if targetIds.contains g.id then
      match targetById.get? g.id with
      | some tg =>
        if g.type.toPlainText != tg.type.toPlainText then
          { g with type := g.type.withDiff dir.changedTag }
        else g
      | none => g
    else if dir.markRemoved then
      { g with isRemoved := true, type := g.type.withDiff dir.missingTag }
    else
      { g with type := g.type.withDiff dir.missingTag }

/-- Compute diff for a "before" state by comparing with "after" state.
    Marks hypotheses/goals that will change or be deleted. -/
def ProofState.diffBefore (before after : ProofState) : ProofState :=
  { hypotheses := diffHypotheses before.hypotheses after.hypotheses .before
    goals := diffGoals before.goals after.goals .before }

/-- Compute diff for an "after" state by comparing with "before" state.
    Marks hypotheses/goals that changed or were inserted. -/
def ProofState.diffAfter (before after : ProofState) : ProofState :=
  { hypotheses := diffHypotheses after.hypotheses before.hypotheses .after
    goals := diffGoals after.goals before.goals .after }

end LeanDag
