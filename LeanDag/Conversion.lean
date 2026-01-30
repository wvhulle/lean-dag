import LeanDag.Types
import LeanDag.NameUtils
import LeanDag.InfoTreeParser

namespace LeanDag

open LeanDag.InfoTreeParser

/-! ## Conversion from Parsed Types to Output Types -/

def convertGoalInfo (g : ParsedGoal) : GoalInfo where
  type := .plain g.type
  username := filterNameOpt g.username
  id := g.id.name.toString
  gotoLocations := g.gotoLocations

def convertHypothesis (h : ParsedHypothesis) : HypothesisInfo where
  name := filterName h.username
  type := .plain h.type
  value := h.value.map TaggedText.plain
  id := h.id
  isProof := h.isProof == "proof"
  isInstance := false
  gotoLocations := h.gotoLocations

end LeanDag
