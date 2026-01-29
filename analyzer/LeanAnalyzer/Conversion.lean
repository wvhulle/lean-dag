import LeanAnalyzer.Types
import LeanAnalyzer.Names
import Services.BetterParser

open Paperproof.Services

namespace LeanAnalyzer

/-- Convert a Paperproof Hypothesis to HypothesisInfo. Filters hygienic names. -/
def hypothesisFromServices (h : Hypothesis) : HypothesisInfo :=
  { name := filterName h.username
    type := h.type
    value := h.value
    id := h.id
    isProof := h.isProof == "proof"
    isInstance := false }

/-- Convert a Paperproof GoalInfo to LeanAnalyzer GoalInfo. Filters hygienic names. -/
def goalFromServices (g : Paperproof.Services.GoalInfo) : LeanAnalyzer.GoalInfo :=
  { type := g.type
    username := filterNameOpt g.username
    id := g.id.name.toString }

/-- Convert a Paperproof GoalInfo to ProofState (single goal with its hypotheses). -/
def proofStateFromGoal (g : Paperproof.Services.GoalInfo) : ProofState :=
  { goals := [goalFromServices g]
    hypotheses := g.hyps.map hypothesisFromServices |>.filter (·.name != "") }

/-- Convert a list of goals to ProofState (using first goal's hypotheses). -/
def proofStateFromGoals (goals : List Paperproof.Services.GoalInfo) : ProofState :=
  match goals with
  | [] => {}
  | g :: _ =>
    { goals := goals.map goalFromServices
      hypotheses := g.hyps.map hypothesisFromServices |>.filter (·.name != "") }

/-- Resolve fvar IDs in tacticDependsOn to user-visible hypothesis names. -/
def resolveDependsOn (step : ProofStep) : List String :=
  let idToName := step.goalBefore.hyps.filterMap fun h =>
    if isHygienicName h.username then none
    else some (h.id, h.username)
  step.tacticDependsOn.filterMap fun id =>
    (idToName.find? fun (hid, _) => hid == id).map Prod.snd

def computeNewHypotheses (before after : ProofState) : List Nat :=
  let beforeIds := before.hypotheses.map (·.id)
  after.hypotheses.toArray.toList.zipIdx.filterMap fun (h, i) =>
    if beforeIds.contains h.id then none else some i

def nodeFromProofStep (idx : Nat) (step : ProofStep) : ProofDagNode :=
  let stateBefore := proofStateFromGoal step.goalBefore
  let stateAfter := proofStateFromGoals step.goalsAfter
  { id := idx
    tactic := {
      text := step.tacticString
      dependsOn := resolveDependsOn step
      theoremsUsed := step.theorems.map (·.name)
    }
    position := step.position.start
    stateBefore
    stateAfter
    newHypotheses := computeNewHypotheses stateBefore stateAfter
    children := []
    parent := none
    depth := 0
    hasUnsolvedSpawnedGoals := false }

end LeanAnalyzer
