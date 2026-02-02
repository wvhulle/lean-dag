import Lean

open Lean
open Lean.Widget (DiffTag)

deriving instance BEq, Repr for DiffTag

namespace LeanDag

/-- Subexpression annotation with optional diff status. Simplified version of Lean.Widget.SubexprInfo. -/
structure SubexpressionAnnotation where
  /-- Diff status for this subexpression (for before/after highlighting). -/
  diff_status : Option DiffTag := none
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-! ## Annotated Text Tree (matching Lean.Widget.TaggedText structure) -/

/-- Annotated text tree that can carry diff information per subexpression.
    Matches the JSON structure of Lean.Widget.TaggedText. -/
inductive AnnotatedTextTree where
  | text (s : String)
  | append (children : Array AnnotatedTextTree)
  | tag (subexpression_info : SubexpressionAnnotation) (tagged_content : AnnotatedTextTree)
  deriving Inhabited, BEq, Repr

/-- Convert AnnotatedTextTree to JSON matching Lean.Widget.TaggedText format. -/
partial def AnnotatedTextTree.toJson : AnnotatedTextTree → Json
  | .text s => Json.mkObj [("kind", "text"), ("text", s)]
  | .append children => Json.mkObj [("kind", "append"), ("children", Json.arr (children.map AnnotatedTextTree.toJson))]
  | .tag subexpr_info content => Json.mkObj [("kind", "tag"), ("subexpression_info", Lean.toJson subexpr_info), ("tagged_content", content.toJson)]

instance : ToJson AnnotatedTextTree := ⟨AnnotatedTextTree.toJson⟩

/-- Parse AnnotatedTextTree from JSON. -/
partial def AnnotatedTextTree.fromJson? (j : Json) : Except String AnnotatedTextTree := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "text" => return .text (← j.getObjValAs? String "text")
  | "append" =>
    let children ← j.getObjValAs? (Array Json) "children"
    return .append (← children.mapM AnnotatedTextTree.fromJson?)
  | "tag" =>
    let subexpr_info ← j.getObjValAs? SubexpressionAnnotation "subexpression_info"
    let content ← j.getObjVal? "tagged_content" >>= AnnotatedTextTree.fromJson?
    return .tag subexpr_info content
  | _ => throw s!"invalid AnnotatedTextTree kind: {kind}"

instance : FromJson AnnotatedTextTree := ⟨AnnotatedTextTree.fromJson?⟩

/-- Create plain text (no diff info). -/
def AnnotatedTextTree.plain (s : String) : AnnotatedTextTree := .text s

/-- Wrap text with a diff tag. -/
def AnnotatedTextTree.withDiff (t : AnnotatedTextTree) (tag : DiffTag) : AnnotatedTextTree :=
  .tag { diff_status := some tag } t

/-- Extract plain text, stripping all tags. -/
partial def AnnotatedTextTree.toPlainText : AnnotatedTextTree → String
  | .text s => s
  | .append children => String.join (children.toList.map AnnotatedTextTree.toPlainText)
  | .tag _ content => content.toPlainText

/-- Check if the AnnotatedTextTree is empty. -/
def AnnotatedTextTree.isEmpty (t : AnnotatedTextTree) : Bool :=
  t.toPlainText.isEmpty

instance : ToString AnnotatedTextTree where
  toString t := t.toPlainText

/-- Allow strings to be used where AnnotatedTextTree is expected. -/
instance : Coe String AnnotatedTextTree := ⟨AnnotatedTextTree.text⟩

/-! ## Navigation Types -/

/-- A location for "go to definition" navigation. -/
structure NavigationTargetLocation where
  uri : String
  position : Lsp.Position
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-- Pre-resolved navigation targets for go-to-definition functionality. -/
structure PreresolvedNavigationTargets where
  definition : Option NavigationTargetLocation := none
  type_definition : Option NavigationTargetLocation := none
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Hypothesis Types -/

/-- Hypothesis info for the TUI proof DAG. -/
structure ProofContextHypothesis where
  /-- User-visible name. -/
  name : String
  /-- Type expression (with diff highlighting). -/
  type : AnnotatedTextTree
  /-- Value for let-bindings (with diff highlighting). -/
  value : Option AnnotatedTextTree := none
  /-- Internal ID for tracking. -/
  id : String
  /-- Whether this hypothesis is a proof term. -/
  is_proof_term : Bool := false
  /-- Whether this is a type class instance. -/
  is_typeclass_instance : Bool := false
  /-- Whether this hypothesis was removed (for diff display in "before" view). -/
  is_removed : Bool := false
  /-- Pre-resolved navigation locations. -/
  navigation_locations : PreresolvedNavigationTargets := {}
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Goal Types -/

/-- Goal info for the TUI proof DAG. -/
structure ProofObligation where
  /-- Goal type expression (with diff highlighting). -/
  type : AnnotatedTextTree
  /-- User-visible name (e.g., "case inl"). -/
  username : Option String := none
  /-- Internal goal ID for tracking. -/
  id : String
  /-- Whether this goal was removed (for diff display in "before" view). -/
  is_removed : Bool := false
  /-- Pre-resolved navigation locations. -/
  navigation_locations : PreresolvedNavigationTargets := {}
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Proof State -/

/-- A proof state (goals and hypotheses at a point in the proof). -/
structure TacticProofState where
  goals : List ProofObligation := []
  hypotheses : List ProofContextHypothesis := []
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Tactic Info -/

/-- Information about a tactic application. -/
structure TacticApplicationInfo where
  /-- The tactic text (e.g., "intro n"). -/
  text : String
  /-- Hypothesis names used by this tactic. -/
  hypothesis_dependencies : List String := []
  /-- Theorem names referenced by this tactic. -/
  referenced_theorems : List String := []
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Proof DAG Node -/

/-- Single node in the proof DAG. -/
structure ProofDagTacticNode where
  id : Nat
  /-- Tactic information. -/
  tactic : TacticApplicationInfo
  /-- Position in source file (line, character). -/
  position : Lsp.Position
  /-- State before tactic. -/
  proof_state_before : TacticProofState
  /-- State after tactic. -/
  proof_state_after : TacticProofState
  /-- Indices into proof_state_after.hypotheses for new hypotheses. -/
  new_hypothesis_indices : List Nat := []
  /-- Child node IDs. -/
  children : List Nat := []
  /-- Parent node ID. -/
  parent : Option Nat := none
  /-- Depth in tree. -/
  depth : Nat := 0
  /-- True if node has spawned goals that are not solved (inline `by` blocks). -/
  has_unsolved_spawned_goals : Bool := false
  deriving Inhabited, ToJson, FromJson, Repr

/-! ## Complete Proof DAG -/

/-- Complete proof DAG structure. -/
structure CompleteProofDag where
  nodes : Array ProofDagTacticNode := #[]
  root_node_id : Option Nat := none
  current_node_id : Option Nat := none
  initial_proof_state : TacticProofState := {}
  definition_name : Option String := none
  orphans : List Nat := []
  deriving Inhabited, ToJson, FromJson, Repr

instance : BEq ProofDagTacticNode where
  beq a b := a.id == b.id

instance : BEq CompleteProofDag where
  beq a b := a.nodes.toList == b.nodes.toList && a.root_node_id == b.root_node_id && a.orphans == b.orphans

/-! ## Functional DAG Types (for term-mode code) -/

/-- The kind of binding in term-mode code. -/
inductive BindingKind where
  | let_bind    -- let-binding
  | fun_param   -- function parameter
  | match_var   -- pattern match variable
  | for_var     -- for-loop variable
  deriving Inhabited, BEq, Repr

instance : ToJson BindingKind where
  toJson
    | .let_bind => "let_bind"
    | .fun_param => "fun_param"
    | .match_var => "match_var"
    | .for_var => "for_var"

instance : FromJson BindingKind where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "let_bind" => pure .let_bind
    | "fun_param" => pure .fun_param
    | "match_var" => pure .match_var
    | "for_var" => pure .for_var
    | _ => throw s!"invalid BindingKind: {s}"

/-- Information about a local binding in term-mode code. Analogous to ProofContextHypothesis. -/
structure LocalBinding where
  /-- User-visible name. -/
  name : String
  /-- Type expression (with diff highlighting). -/
  type : AnnotatedTextTree
  /-- Value for let-bindings (with diff highlighting). -/
  value : Option AnnotatedTextTree := none
  /-- Internal ID for tracking. -/
  id : String
  /-- The kind of binding. -/
  binding_kind : BindingKind
  /-- Whether this binding is implicit. -/
  is_implicit : Bool := false
  /-- Whether this is a typeclass instance. -/
  is_instance : Bool := false
  /-- Whether this binding goes out of scope (for diff display). -/
  is_removed : Bool := false
  /-- Pre-resolved navigation locations. -/
  navigation_locations : PreresolvedNavigationTargets := {}
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-- Single node in the functional DAG. -/
structure FunctionalDagNode where
  id : Nat
  /-- Expression at this step. -/
  expression : AnnotatedTextTree
  /-- Bindings in scope before this expression. -/
  bindings_before : List LocalBinding := []
  /-- Bindings in scope after this expression. -/
  bindings_after : List LocalBinding := []
  /-- Indices into bindings_after for new bindings. -/
  new_binding_indices : List Nat := []
  /-- Expected type at this point (continuation type). -/
  expected_type : Option AnnotatedTextTree := none
  /-- Position in source file. -/
  position : Lsp.Position
  /-- Child node IDs (for pattern match branches, if-else, etc.). -/
  children : List Nat := []
  /-- Parent node ID. -/
  parent : Option Nat := none
  /-- Depth in tree. -/
  depth : Nat := 0
  deriving Inhabited, ToJson, FromJson, Repr

instance : BEq FunctionalDagNode where
  beq a b := a.id == b.id

/-- Complete functional DAG structure for term-mode definitions. -/
structure CompleteFunctionalDag where
  nodes : Array FunctionalDagNode := #[]
  root_node_id : Option Nat := none
  current_node_id : Option Nat := none
  initial_bindings : List LocalBinding := []
  definition_name : Option String := none
  definition_type : Option AnnotatedTextTree := none
  orphans : List Nat := []
  deriving Inhabited, ToJson, FromJson, Repr

instance : BEq CompleteFunctionalDag where
  beq a b := a.nodes.toList == b.nodes.toList && a.root_node_id == b.root_node_id && a.orphans == b.orphans

/-! ## Server Mode -/

/-- Server operating mode for RPC communication. -/
inductive ServerOperatingMode where
  | library    -- Library mode: uses `lake serve`, requires `import LeanDag`
  | standalone -- Standalone mode: uses lean-dag binary, no import required
  deriving Inhabited, BEq, Repr

instance : ToJson ServerOperatingMode where
  toJson
    | .library => "Library"
    | .standalone => "Standalone"

instance : FromJson ServerOperatingMode where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "Library" => pure .library
    | "Standalone" => pure .standalone
    | _ => throw s!"invalid ServerOperatingMode: {s}"

/-! ## Cursor Info -/

/-- Cursor location with document URI and trigger method. -/
structure EditorCursorPosition where
  uri : String
  position : Lsp.Position
  method : String
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-! ## Messages (Server -> TUI) -/

/-- Messages sent from server to TUI over the socket. -/
inductive ServerToClientMessage where
  | connected (server_mode : Option ServerOperatingMode)
  | cursor (info : EditorCursorPosition)
  | proofDag (uri : String) (position : Lsp.Position) (proof_dag : Option CompleteProofDag)
  | functionalDag (uri : String) (position : Lsp.Position) (functional_dag : Option CompleteFunctionalDag)
  | error (error : String)
  deriving Inhabited, Repr

/-- Convert ServerToClientMessage to JSON with tagged format matching Rust serde. -/
def ServerToClientMessage.toJson : ServerToClientMessage → Json
  | .connected server_mode =>
    Json.mkObj [("type", "Connected"), ("server_mode", Lean.toJson server_mode)]
  | .cursor info =>
    Json.mkObj [("type", "Cursor"), ("uri", info.uri), ("position", Lean.toJson info.position), ("method", info.method)]
  | .proofDag uri pos dag =>
    Json.mkObj [("type", "ProofDag"), ("uri", uri), ("position", Lean.toJson pos), ("proof_dag", Lean.toJson dag)]
  | .functionalDag uri pos dag =>
    Json.mkObj [("type", "FunctionalDag"), ("uri", uri), ("position", Lean.toJson pos), ("functional_dag", Lean.toJson dag)]
  | .error err =>
    Json.mkObj [("type", "Error"), ("error", err)]

instance : ToJson ServerToClientMessage := ⟨ServerToClientMessage.toJson⟩

/-- Parse ServerToClientMessage from JSON. -/
def ServerToClientMessage.fromJson? (j : Json) : Except String ServerToClientMessage := do
  let type ← j.getObjValAs? String "type"
  match type with
  | "Connected" =>
    let server_mode ← j.getObjValAs? (Option ServerOperatingMode) "server_mode"
    return .connected server_mode
  | "Cursor" =>
    let uri ← j.getObjValAs? String "uri"
    let position ← j.getObjValAs? Lsp.Position "position"
    let method ← j.getObjValAs? String "method"
    return .cursor { uri, position, method }
  | "ProofDag" =>
    let uri ← j.getObjValAs? String "uri"
    let position ← j.getObjValAs? Lsp.Position "position"
    let proof_dag ← j.getObjValAs? (Option CompleteProofDag) "proof_dag"
    return .proofDag uri position proof_dag
  | "FunctionalDag" =>
    let uri ← j.getObjValAs? String "uri"
    let position ← j.getObjValAs? Lsp.Position "position"
    let functional_dag ← j.getObjValAs? (Option CompleteFunctionalDag) "functional_dag"
    return .functionalDag uri position functional_dag
  | "Error" =>
    let error ← j.getObjValAs? String "error"
    return .error error
  | _ => throw s!"invalid ServerToClientMessage type: {type}"

instance : FromJson ServerToClientMessage := ⟨ServerToClientMessage.fromJson?⟩

/-! ## Commands (TUI -> Server) -/

/-- Commands sent from TUI to server. -/
inductive ClientToServerCommand where
  | navigate (uri : String) (position : Lsp.Position)
  | getProofDag (uri : String) (position : Lsp.Position) (mode : String)
  deriving Inhabited, BEq, Repr

/-- Convert ClientToServerCommand to JSON with tagged format matching Rust serde. -/
def ClientToServerCommand.toJson : ClientToServerCommand → Json
  | .navigate uri position =>
    Json.mkObj [("type", "Navigate"), ("uri", uri), ("position", Lean.toJson position)]
  | .getProofDag uri position mode =>
    Json.mkObj [("type", "GetProofDag"), ("uri", uri), ("position", Lean.toJson position), ("mode", mode)]

instance : ToJson ClientToServerCommand := ⟨ClientToServerCommand.toJson⟩

/-- Parse ClientToServerCommand from JSON. -/
def ClientToServerCommand.fromJson? (j : Json) : Except String ClientToServerCommand := do
  let type ← j.getObjValAs? String "type"
  match type with
  | "Navigate" =>
    let uri ← j.getObjValAs? String "uri"
    let position ← j.getObjValAs? Lsp.Position "position"
    return .navigate uri position
  | "GetProofDag" =>
    let uri ← j.getObjValAs? String "uri"
    let position ← j.getObjValAs? Lsp.Position "position"
    let mode ← j.getObjValAs? String "mode" <|> pure "tree"
    return .getProofDag uri position mode
  | _ => throw s!"invalid ClientToServerCommand type: {type}"

instance : FromJson ClientToServerCommand := ⟨ClientToServerCommand.fromJson?⟩

end LeanDag
