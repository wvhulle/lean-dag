import LeanDag.Types

namespace LeanDag

/-! ## Diff Computation -/

/-- Mark a hypothesis type with a diff tag. -/
def HypothesisInfo.withDiffTag (h : HypothesisInfo) (tag : DiffTag) : HypothesisInfo :=
  { h with type := h.type.withDiff tag }

/-- Mark a goal type with a diff tag. -/
def GoalInfo.withDiffTag (g : GoalInfo) (tag : DiffTag) : GoalInfo :=
  { g with type := g.type.withDiff tag }

/-- Compute diff for a "before" state by comparing with "after" state.
    Marks hypotheses/goals that will change or be deleted. -/
def diffStateBefore (before after : ProofState) : ProofState :=
  let afterHypIds := after.hypotheses.map (·.id) |>.toArray
  let afterGoalIds := after.goals.map (·.id) |>.toArray
  let diffedHyps := before.hypotheses.map fun h =>
    if afterHypIds.contains h.id then
      -- Check if type changed
      let afterHyp := after.hypotheses.find? (·.id == h.id)
      match afterHyp with
      | some ah =>
        if h.type.toPlainText != ah.type.toPlainText then
          h.withDiffTag .willChange
        else h
      | none => h
    else
      -- Hypothesis will be deleted
      { h with isRemoved := true, type := h.type.withDiff .willDelete }
  let diffedGoals := before.goals.map fun g =>
    if afterGoalIds.contains g.id then
      let afterGoal := after.goals.find? (·.id == g.id)
      match afterGoal with
      | some ag =>
        if g.type.toPlainText != ag.type.toPlainText then
          g.withDiffTag .willChange
        else g
      | none => g
    else
      { g with isRemoved := true, type := g.type.withDiff .willDelete }
  { hypotheses := diffedHyps, goals := diffedGoals }

/-- Compute diff for an "after" state by comparing with "before" state.
    Marks hypotheses/goals that changed or were inserted. -/
def diffStateAfter (before after : ProofState) : ProofState :=
  let beforeHypIds := before.hypotheses.map (·.id) |>.toArray
  let beforeGoalIds := before.goals.map (·.id) |>.toArray
  let diffedHyps := after.hypotheses.map fun h =>
    if beforeHypIds.contains h.id then
      let beforeHyp := before.hypotheses.find? (·.id == h.id)
      match beforeHyp with
      | some bh =>
        if h.type.toPlainText != bh.type.toPlainText then
          h.withDiffTag .wasChanged
        else h
      | none => h
    else
      -- New hypothesis was inserted
      h.withDiffTag .wasInserted
  let diffedGoals := after.goals.map fun g =>
    if beforeGoalIds.contains g.id then
      let beforeGoal := before.goals.find? (·.id == g.id)
      match beforeGoal with
      | some bg =>
        if g.type.toPlainText != bg.type.toPlainText then
          g.withDiffTag .wasChanged
        else g
      | none => g
    else
      g.withDiffTag .wasInserted
  { hypotheses := diffedHyps, goals := diffedGoals }

end LeanDag
