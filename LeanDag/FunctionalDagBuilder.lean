import Lean
import Lean.Meta.Basic
import LeanDag.Protocol
import LeanDag.NameUtils
import LeanDag.DagBuilder

open Lean Elab Server

namespace LeanDag.FunctionalDagBuilder

/-! ## Parsed Term Types

These types collect term-mode information from InfoTree TermInfo nodes.
-/

/-- A parsed binding from LocalContext. -/
structure ParsedBinding where
  binding : LocalBinding
  fvarId : FVarId
  deriving Inhabited

instance : BEq ParsedBinding where beq b1 b2 := b1.fvarId == b2.fvarId

/-- A parsed term step from TermInfo. -/
structure ParsedTermStep where
  /-- The expression at this step. -/
  expression : String
  /-- Bindings in scope at this step. -/
  bindings : List ParsedBinding
  /-- Expected type (if available). -/
  expectedType : Option String
  /-- Whether this step introduces a new binding. -/
  isBinder : Bool
  /-- Source position. -/
  position : Lsp.Position
  /-- Depth hint from tree structure. -/
  depth : Nat
  deriving Inhabited

/-! ## Binder Location Cache (reused from InfoTreeParser) -/

abbrev BinderCache := Std.HashMap FVarId Lsp.Position

def buildBinderCache (infoTree : InfoTree) (text : FileMap) : BinderCache :=
  infoTree.foldInfo (init := {}) fun _ctx info cache =>
    match info with
    | .ofTermInfo { isBinder := true, expr := .fvar fvarId .., .. } =>
      match info.range? with
      | some range => cache.insert fvarId (text.utf8PosToLspPos range.start)
      | none => cache
    | _ => cache

/-! ## Parsing Context -/

structure TermParserContext where
  binderCache : BinderCache
  fileUri : String
  text : FileMap

/-! ## Binding Formatting -/

/-- Determine the binding kind from LocalDecl. -/
def bindingKindFromDecl (decl : LocalDecl) : BindingKind :=
  match decl.binderInfo with
  | .default => if decl.value?.isSome then .letBind else .funParam
  | .implicit | .strictImplicit => .funParam
  | .instImplicit => .funParam

/-- Format a local declaration to LocalBinding. -/
def formatBinding (ppCtx : PPContext) (decl : LocalDecl) (binderCache : BinderCache) (fileUri : String)
    : IO ParsedBinding := do
  let typeStr := (← ppExprWithInfos ppCtx decl.type).fmt.pretty
  let valueStr ← decl.value?.mapM fun v => do pure (← ppExprWithInfos ppCtx v).fmt.pretty
  let navigationLocations : Option PreresolvedNavigationTargets := match binderCache.get? decl.fvarId with
    | some pos => some { definition := some { uri := fileUri, position := pos } }
    | none => none
  let binding : LocalBinding := {
    name := decl.userName.toString.filterName
    type := .plain typeStr
    value := valueStr.map AnnotatedTextTree.plain
    id := decl.fvarId.name.toString
    bindingKind := bindingKindFromDecl decl
    isImplicit := decl.binderInfo == .implicit || decl.binderInfo == .strictImplicit
    isInstance := decl.binderInfo == .instImplicit
    navigationLocations
  }
  return { binding, fvarId := decl.fvarId }

/-- Format all bindings from LocalContext. -/
def formatBindings (ppCtx : PPContext) (lctx : LocalContext) (binderCache : BinderCache) (fileUri : String)
    : IO (List ParsedBinding) := do
  lctx.foldrM (init := []) fun decl acc => do
    if decl.isAuxDecl || decl.isImplementationDetail then return acc
    let binding ← formatBinding ppCtx decl binderCache fileUri
    return binding :: acc

/-! ## Term Info Collection -/

/-- Check if this is a "significant" term worth showing in the DAG.
    We want let-bindings, function applications, pattern matches, etc. -/
def isSignificantTerm (termInfo : Elab.TermInfo) : Bool :=
  -- Always show binders (let, fun params, match vars)
  termInfo.isBinder ||
  -- Show function applications (but not trivial ones)
  match termInfo.expr with
  | .app .. => true
  | .letE .. => true
  | .lam .. => true
  | .mdata _ e => e.isApp || e.isLet || e.isLambda
  | _ => false

/-- Collect TermInfo nodes from InfoTree using foldInfo. -/
def collectTermInfos (pctx : TermParserContext) (infoTree : InfoTree)
    : IO (List ParsedTermStep) := do
  let steps := infoTree.foldInfo (init := []) fun ctx info acc =>
    match info with
    | .ofTermInfo termInfo =>
      if isSignificantTerm termInfo then
        match info.pos? with
        | some pos =>
          let step := (ctx, termInfo, pos)
          step :: acc
        | none => acc
      else acc
    | _ => acc

  -- Process each step with its context
  let mut result : List ParsedTermStep := []
  for (ctx, termInfo, pos) in steps do
    let lctx := termInfo.lctx.sanitizeNames.run' {options := {}}
    let ppCtx := ctx.toPPContext lctx

    let exprStr := (← ppExprWithInfos ppCtx termInfo.expr).fmt.pretty
    let expectedTypeStr ← termInfo.expectedType?.mapM fun ty => do
      pure (← ppExprWithInfos ppCtx ty).fmt.pretty

    let bindings ← formatBindings ppCtx lctx pctx.binderCache pctx.fileUri

    let step : ParsedTermStep := {
      expression := exprStr
      bindings := bindings
      expectedType := expectedTypeStr
      isBinder := termInfo.isBinder
      position := pctx.text.utf8PosToLspPos pos
      depth := 0  -- Depth computed during DAG building
    }
    result := step :: result

  return result

/-! ## DAG Building -/

/-- Compute which bindings are new compared to parent. -/
def computeNewBindings (parentBindings childBindings : List ParsedBinding) : Array Nat :=
  let withIndices : List (ParsedBinding × Nat) := childBindings.zipIdx
  (withIndices.filterMap fun (binding, idx) =>
    if parentBindings.any fun p => p.fvarId == binding.fvarId then none
    else some idx).toArray

/-- Build CompleteFunctionalDag from parsed steps. -/
def buildDag (steps : List ParsedTermStep) (position : Lsp.Position) (definitionName : Option String)
    : CompleteFunctionalDag :=
  if steps.isEmpty then {} else Id.run do
    -- Sort by position (line, then character)
    let sortedSteps := steps.toArray.insertionSort fun a b =>
      a.position.line < b.position.line ||
      (a.position.line == b.position.line && a.position.character < b.position.character)

    -- Build nodes
    let mut nodes : Array FunctionalDagNode := #[]
    let mut parentStack : List (Nat × List ParsedBinding) := [] -- (nodeId, bindings)

    for h : idx in [:sortedSteps.size] do
      let step := sortedSteps[idx]

      -- Find parent: node with subset of bindings
      let mut parentId : Option Nat := none
      let mut parentBindings : List ParsedBinding := []

      for (pid, pbindings) in parentStack do
        -- Parent should have fewer or equal bindings
        if pbindings.length <= step.bindings.length then
          parentId := some pid
          parentBindings := pbindings
          break

      let newBindingIndices := computeNewBindings parentBindings step.bindings

      let node : FunctionalDagNode := {
        id := idx
        expression := .plain step.expression
        bindingsBefore := (parentBindings.map (·.binding)).toArray
        bindingsAfter := (step.bindings.map (·.binding)).toArray
        newBindingIndices := newBindingIndices
        expectedType := step.expectedType.map AnnotatedTextTree.plain
        position := step.position
        children := #[] -- Will be filled in second pass
        parent := parentId
        depth := parentStack.length
      }
      nodes := nodes.push node
      parentStack := (idx, step.bindings) :: parentStack

    -- Second pass: fill in children
    let mut nodesWithChildren := nodes
    for node in nodes do
      if let some pid := node.parent then
        if let some parent := nodesWithChildren[pid]? then
          nodesWithChildren := nodesWithChildren.set! pid
            { parent with children := parent.children.push node.id }

    -- Find root and current node
    let rootNodeId := if nodesWithChildren.isEmpty then none else some 0
    let nodesIndexed : List (FunctionalDagNode × Nat) := nodesWithChildren.toList.zipIdx
    let currentNodeId := nodesIndexed.findSome? fun (node, idx) =>
      if node.position.line <= position.line then some idx else none

    -- Get initial bindings from first node's bindingsBefore
    let initialBindings := nodesWithChildren[0]?.map (·.bindingsBefore) |>.getD #[]

    -- Get definition type from first step's expected type
    let definitionType := sortedSteps[0]?.bind (·.expectedType) |>.map AnnotatedTextTree.plain

    return {
      nodes := nodesWithChildren
      rootNodeId := rootNodeId
      currentNodeId := currentNodeId
      initialBindings := initialBindings
      definitionName := definitionName
      definitionType := definitionType
      orphans := #[]
    }

/-! ## Main Entry Point -/

/-- Check if a tactic is from a `by` proof block (not internal `do` elaboration). -/
def isByProofTactic (tacticInfo : Elab.TacticInfo) : Bool :=
  -- Check the syntax to see if it's a real proof tactic
  match tacticInfo.stx with
  | .node _ kind _ =>
    let kindStr := kind.toString
    -- Proof tactics live in Lean.Parser.Tactic namespace
    -- `do` notation uses Lean.Parser.Term.do* and similar
    kindStr.startsWith "Lean.Parser.Tactic" ||
    -- Also check for common tactic commands
    kindStr == "Lean.Parser.Command.declaration"
  | .atom _ val =>
    -- Atom-based tactics like `trivial`, `assumption`, etc.
    val == "trivial" || val == "assumption" || val == "rfl" || val == "decide"
  | _ => false

/-- Check if InfoTree contains term-mode code (not a `by` proof block). -/
def isTermModeTree (infoTree : InfoTree) : Bool :=
  -- A tree is term-mode if it has TermInfo but no real `by` proof tactics
  -- (`do` notation generates TacticInfo internally, but those aren't user proof tactics)
  let hasByProofTactic := infoTree.foldInfo (init := false) fun _ info acc =>
    match info with
    | .ofTacticInfo tacticInfo => acc || isByProofTactic tacticInfo
    | _ => acc
  let hasTermInfo := infoTree.foldInfo (init := false) fun _ info acc =>
    acc || info matches .ofTermInfo _
  hasTermInfo && !hasByProofTactic

/-- Parse term-mode InfoTree and build functional DAG. -/
def computeFunctionalDag (snap : Snapshots.Snapshot) (position : Lsp.Position) : RequestM (Option CompleteFunctionalDag) := do
  let doc ← RequestM.readDoc
  let text := doc.meta.text

  -- Check if this is term-mode
  unless isTermModeTree snap.infoTree do return none

  let pctx : TermParserContext := {
    binderCache := buildBinderCache snap.infoTree text
    fileUri := doc.meta.uri
    text := text
  }

  let steps ← collectTermInfos pctx snap.infoTree
  if steps.isEmpty then return none

  -- Get definition name from InfoTree
  let definitionName := getDefinitionName snap.infoTree

  return some (buildDag steps position definitionName)

end LeanDag.FunctionalDagBuilder
