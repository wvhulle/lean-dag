import Lean

open Lean

namespace LeanAnalyzer

/-! ## Navigation Types -/

/-- A location for "go to definition" navigation. -/
structure GotoLocation where
  uri : String
  position : Lsp.Position
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-- Pre-resolved goto locations for navigation. -/
structure GotoLocations where
  definition : Option GotoLocation := none
  typeDef : Option GotoLocation := none
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Hypothesis Types -/

/-- Hypothesis info for the TUI proof DAG. -/
structure HypothesisInfo where
  /-- User-visible name. -/
  name : String
  /-- Type expression. -/
  type : String
  /-- Value for let-bindings. -/
  value : Option String := none
  /-- Internal ID for tracking. -/
  id : String
  /-- Whether this hypothesis is a proof term. -/
  isProof : Bool := false
  /-- Whether this is a type class instance. -/
  isInstance : Bool := false
  /-- Pre-resolved navigation locations. -/
  gotoLocations : GotoLocations := {}
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Goal Types -/

/-- Goal info for the TUI proof DAG. -/
structure GoalInfo where
  /-- Goal type expression. -/
  type : String
  /-- User-visible name (e.g., "case inl"). -/
  username : Option String := none
  /-- Internal goal ID for tracking. -/
  id : String
  /-- Pre-resolved navigation locations. -/
  gotoLocations : GotoLocations := {}
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Proof State -/

/-- A proof state (goals and hypotheses at a point in the proof). -/
structure ProofState where
  goals : List GoalInfo := []
  hypotheses : List HypothesisInfo := []
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Tactic Info -/

/-- Information about a tactic application. -/
structure TacticInfo where
  /-- The tactic text (e.g., "intro n"). -/
  text : String
  /-- Hypothesis names used by this tactic. -/
  dependsOn : List String := []
  /-- Theorem names referenced by this tactic. -/
  theoremsUsed : List String := []
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Proof DAG Node -/

/-- Single node in the proof DAG. -/
structure ProofDagNode where
  id : Nat
  /-- Tactic information. -/
  tactic : TacticInfo
  /-- Position in source file (line, character). -/
  position : Lsp.Position
  /-- State before tactic. -/
  stateBefore : ProofState
  /-- State after tactic. -/
  stateAfter : ProofState
  /-- Indices into stateAfter.hypotheses for new hypotheses. -/
  newHypotheses : List Nat := []
  /-- Child node IDs. -/
  children : List Nat := []
  /-- Parent node ID. -/
  parent : Option Nat := none
  /-- Depth in tree. -/
  depth : Nat := 0
  /-- True if node has spawned goals that are not solved (inline `by` blocks). -/
  hasUnsolvedSpawnedGoals : Bool := false
  deriving Inhabited, ToJson, FromJson, Repr

/-! ## Complete Proof DAG -/

/-- Complete proof DAG structure. -/
structure ProofDag where
  nodes : Array ProofDagNode := #[]
  root : Option Nat := none
  currentNode : Option Nat := none
  initialState : ProofState := {}
  definitionName : Option String := none
  orphans : List Nat := []
  deriving Inhabited, ToJson, FromJson, Repr

instance : BEq ProofDagNode where
  beq a b := a.id == b.id

instance : BEq ProofDag where
  beq a b := a.nodes.toList == b.nodes.toList && a.root == b.root && a.orphans == b.orphans

end LeanAnalyzer
