import LeanDag.Protocol
import LeanDag.NameUtils
import LeanDag.InfoTreeParser

namespace LeanDag.InfoTreeParser

/-! ## Conversion from Parsed Types to Output Types -/

def ParsedGoal.toGoalInfo (g : ParsedGoal) : LeanDag.GoalInfo where
  type := .plain g.type
  username := g.username.filterNameOpt
  id := g.id.name.toString
  gotoLocations := {}

def ParsedHypothesis.toHypothesisInfo (h : ParsedHypothesis) : LeanDag.HypothesisInfo where
  name := h.username.filterName
  type := .plain h.type
  value := h.value.map LeanDag.TaggedText.plain
  id := h.id
  isProof := h.isProof
  isInstance := false
  gotoLocations := h.gotoLocations

end LeanDag.InfoTreeParser
