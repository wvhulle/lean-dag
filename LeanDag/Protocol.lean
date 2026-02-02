import Lean
import LeanDag.SchemaCodegen

/-!
# Protocol Types for LeanDag

This module generates types from `protocol-schema.json` and adds
extension methods and conversion functions for compatibility with the Lean LSP types.
-/

open Lean

namespace LeanDag

/-! ## Generated Types from JSON Schema -/

-- Generate all types from the JSON schema
gen_types_from_schema "../protocol-schema.json"

/-! ## DiffTag Conversion Functions -/

open Lean.Widget (DiffTag)

/-- Convert from Lean.Widget.DiffTag to generated SubexpressionDiffTag. -/
def SubexpressionDiffTag.fromWidgetDiffTag : DiffTag → SubexpressionDiffTag
  | .wasChanged => .wasChanged
  | .willChange => .willChange
  | .wasDeleted => .wasDeleted
  | .willDelete => .willDelete
  | .wasInserted => .wasInserted
  | .willInsert => .willInsert

/-- Convert from generated SubexpressionDiffTag to Lean.Widget.DiffTag. -/
def SubexpressionDiffTag.toWidgetDiffTag : SubexpressionDiffTag → DiffTag
  | .wasChanged => .wasChanged
  | .willChange => .willChange
  | .wasDeleted => .wasDeleted
  | .willDelete => .willDelete
  | .wasInserted => .wasInserted
  | .willInsert => .willInsert

instance : Coe DiffTag SubexpressionDiffTag := ⟨SubexpressionDiffTag.fromWidgetDiffTag⟩
instance : Coe SubexpressionDiffTag DiffTag := ⟨SubexpressionDiffTag.toWidgetDiffTag⟩

/-! ## Position Conversion Functions -/

/-- Convert from generated LineCharacterPosition to Lsp.Position. -/
def LineCharacterPosition.toLspPosition (p : LineCharacterPosition) : Lsp.Position :=
  ⟨p.line, p.character⟩

/-- Convert from Lsp.Position to generated LineCharacterPosition. -/
def LineCharacterPosition.fromLspPosition (p : Lsp.Position) : LineCharacterPosition :=
  ⟨p.character, p.line⟩

instance : Coe LineCharacterPosition Lsp.Position := ⟨LineCharacterPosition.toLspPosition⟩
instance : Coe Lsp.Position LineCharacterPosition := ⟨LineCharacterPosition.fromLspPosition⟩

/-! ## AnnotatedTextTree Extension Methods -/

/-- Create plain text (no diff info). -/
def AnnotatedTextTree.plain (s : String) : AnnotatedTextTree := .text s

/-- Wrap text with a diff tag. -/
def AnnotatedTextTree.withDiff (t : AnnotatedTextTree) (tag : SubexpressionDiffTag) : AnnotatedTextTree :=
  .tag { diff_status := some tag } t

/-- Extract plain text, stripping all tags. -/
partial def AnnotatedTextTree.toPlainText : AnnotatedTextTree → String
  | .text s => s
  | .append children => String.join (children.toList.map AnnotatedTextTree.toPlainText)
  | .tag _ content => AnnotatedTextTree.toPlainText content

/-- Check if the AnnotatedTextTree is empty. -/
def AnnotatedTextTree.isEmpty (t : AnnotatedTextTree) : Bool :=
  t.toPlainText.isEmpty

instance : ToString AnnotatedTextTree where
  toString t := t.toPlainText

/-- Allow strings to be used where AnnotatedTextTree is expected. -/
instance : Coe String AnnotatedTextTree := ⟨AnnotatedTextTree.text⟩

/-! ## BEq instances for node types -/

instance : BEq ProofDagTacticNode where
  beq a b := a.id == b.id

instance : BEq CompleteProofDag where
  beq a b := a.nodes.toList == b.nodes.toList && a.root_node_id == b.root_node_id && a.orphans == b.orphans

instance : BEq FunctionalDagNode where
  beq a b := a.id == b.id

instance : BEq CompleteFunctionalDag where
  beq a b := a.nodes.toList == b.nodes.toList && a.root_node_id == b.root_node_id && a.orphans == b.orphans

end LeanDag
