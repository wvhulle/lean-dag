import Lean
import Lean.Meta.Basic
import Lean.Meta.CollectMVars
import LeanDag.Types

open Lean Elab Server Lean.Elab

namespace LeanDag.InfoTreeParser

/-! ## Tactic Substring Extraction -/

def getTacticSubstring (tInfo : Elab.TacticInfo) : Option Substring.Raw :=
  tInfo.stx.getSubstring?.join

/-! ## Goals At Position -/

partial def goalsAt? (t : InfoTree) (text : FileMap) (hoverPos : String.Pos.Raw) : List GoalsAtResult :=
  let gs := t.collectNodesBottomUp fun ctx i cs gs => Id.run do
    let .ofTacticInfo ti := i | return gs
    let some pos := i.pos? | return gs
    let some tailPos := i.tailPos? | return gs
    let trailSize := i.stx.getTrailingSize
    let atEOF := tailPos.byteIdx + trailSize == text.source.rawEndPos.byteIdx
    unless pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + max 1 trailSize || atEOF) do return gs
    let isClosingBracket := ti.stx.getAtomVal == "]"
    unless (gs.isEmpty || (hoverPos ≥ tailPos && gs.all (·.indented))) && !isClosingBracket do return gs
    return [{
      ctxInfo := ctx
      tacticInfo := ti
      useAfter := hoverPos > pos && !cs.any (hasNestedTactic pos tailPos)
      indented := (text.toPosition pos).column > (text.toPosition hoverPos).column && !isEmptyBy ti.stx
      priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1
    }]
  let maxPrio? := gs.map (·.priority) |>.max?
  gs.filter (some ·.priority == maxPrio?)
where
  hasNestedTactic (pos tailPos) : InfoTree → Bool
    | .node i@(.ofTacticInfo _) cs => Id.run do
      if let `(by $_) := i.stx then return false
      let some pos' := i.pos? | return cs.any (hasNestedTactic pos tailPos)
      let some tailPos' := i.tailPos? | return cs.any (hasNestedTactic pos tailPos)
      if tailPos' > hoverPos && (pos', tailPos') != (pos, tailPos) then return true
      cs.any (hasNestedTactic pos tailPos)
    | .node (.ofMacroExpansionInfo _) cs => cs.any (hasNestedTactic pos tailPos)
    | _ => false
  isEmptyBy (stx : Syntax) : Bool :=
    stx.getNumArgs == 2 && stx[0].isToken "by" && stx[1].getNumArgs == 1 && stx[1][0].isMissing

/-! ## Theorem Extraction -/

structure ArgumentInfo where
  name : String
  type : String
  deriving Inhabited, FromJson, ToJson

structure TheoremSignature where
  name            : String
  instanceArgs    : List ArgumentInfo := []
  implicitArgs    : List ArgumentInfo := []
  explicitArgs    : List ArgumentInfo := []
  type            : String := ""
  declarationType : String := ""
  body            : Option String := none
  deriving Inhabited, FromJson, ToJson

def extractArgsWithTypes (expr : Expr) : MetaM (List ArgumentInfo × List ArgumentInfo × List ArgumentInfo × String) := do
  Meta.forallTelescope expr fun args body => do
    let mut lctx := LocalContext.empty
    for arg in args do
      lctx := lctx.addDecl (← arg.fvarId!.getDecl)
    let ppCtx : PPContext := {
      env := ← getEnv, mctx := ← getMCtx, lctx
      opts := (← getOptions).setBool `pp.fullNames true
    }
    let mut instanceArgs := []
    let mut implicitArgs := []
    let mut explicitArgs := []
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      let typeStr := (← ppExprWithInfos ppCtx decl.type).fmt.pretty
      let argInfo : ArgumentInfo := { name := decl.userName.toString, type := typeStr }
      match decl.binderInfo with
      | .instImplicit => instanceArgs := instanceArgs ++ [argInfo]
      | .implicit | .strictImplicit => implicitArgs := implicitArgs ++ [argInfo]
      | .default => explicitArgs := explicitArgs ++ [argInfo]
    let bodyStr := (← ppExprWithInfos ppCtx body).fmt.pretty
    return (instanceArgs, implicitArgs, explicitArgs, bodyStr)

def declarationKind : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

def formatDeclaration (name : Name) (ctx : ContextInfo) (goalDecl : MetavarDecl) : MetaM (Option TheoremSignature) := do
  let constInfo ← getConstInfo name
  let declType := declarationKind constInfo
  unless declType ∈ ["theorem", "axiom", "def"] do return none
  let sanitizedLctx := goalDecl.lctx.sanitizeNames.run' {options := {}}
  let ppCtx := { ctx.toPPContext sanitizedLctx with
    opts := (ctx.toPPContext goalDecl.lctx).opts.setBool `pp.fullNames true }
  let nameStr := (← ppExprWithInfos ppCtx (mkConst constInfo.name)).fmt.pretty
  let (instanceArgs, implicitArgs, explicitArgs, typeStr) ← extractArgsWithTypes constInfo.type
  let declBody ← match declType, constInfo.value? with
    | "def", some expr => pure <| some (← ppExprWithInfos ppCtx expr).fmt.pretty
    | _, _ => pure none
  return some { name := nameStr, instanceArgs, implicitArgs, explicitArgs, type := typeStr, declarationType := declType, body := declBody }

def extractConstName (expr : Expr) (lctx : LocalContext) : Option Name := do
  guard (!expr.isSyntheticSorry)
  let cleanExpr := expr.consumeMData
  match cleanExpr with
  | .const name _ => name
  | .app .. => expr.getAppFn.consumeMData.constName?
  | .fvar .. =>
    let ldecl ← lctx.findFVar? cleanExpr
    let val ← ldecl.value?
    val.getAppFn.consumeMData.constName?
  | _ => none

def findTheoremsInRange (tree : InfoTree) (startPos stopPos : String.Pos.Raw) (ctx : ContextInfo) (goalDecl : MetavarDecl) : MetaM (List TheoremSignature) := do
  let mut theoremNames : NameSet := {}
  let mut pos := startPos
  while pos < stopPos do
    if let some info ← tree.hoverableInfoAtM? pos then
      if let .ofTermInfo termInfo := info.info then
        if let some name := extractConstName termInfo.expr termInfo.lctx then
          theoremNames := theoremNames.insert name
    pos := ⟨pos.byteIdx + 3⟩
  theoremNames.toList.filterMapM fun name => do
    formatDeclaration (← resolveGlobalConstNoOverloadCore name) ctx goalDecl

def getTheorems (infoTree : InfoTree) (tacticInfo : Elab.TacticInfo) (ctx : ContextInfo) : RequestM (List TheoremSignature) := do
  let some goalDecl := ctx.mctx.findDecl? tacticInfo.goalsBefore.head!
    | throwThe RequestError ⟨.invalidParams, "noGoalDecl"⟩
  let some sub := getTacticSubstring tacticInfo
    | throwThe RequestError ⟨.invalidParams, "noTacticSubstring"⟩
  ctx.runMetaM goalDecl.lctx do
    findTheoremsInRange infoTree sub.startPos sub.stopPos ctx goalDecl

/-! ## Parsed Proof Types (intermediate representation) -/

structure ParsedHypothesis where
  username : String
  type     : String
  value    : Option String
  id       : String
  isProof  : String
  gotoLocations : LeanDag.GotoLocations := {}
  deriving Inhabited, ToJson, FromJson

structure ParsedGoal where
  username : String
  type     : String
  hyps     : List ParsedHypothesis
  id       : MVarId
  gotoLocations : LeanDag.GotoLocations := {}
  deriving Inhabited, ToJson, FromJson

instance : BEq ParsedGoal where beq g1 g2 := g1.id == g2.id
instance : Hashable ParsedGoal where hash g := hash g.id

structure SourceRange where
  start : Lsp.Position
  stop  : Lsp.Position
  deriving Inhabited, ToJson, FromJson

structure ParsedStep where
  tacticString    : String
  goalBefore      : ParsedGoal
  goalsAfter      : List ParsedGoal
  tacticDependsOn : List String
  spawnedGoals    : List ParsedGoal
  position        : SourceRange
  theorems        : List TheoremSignature
  deriving Inhabited, ToJson, FromJson

structure ParseResult where
  steps    : List ParsedStep
  allGoals : Std.HashSet ParsedGoal

/-! ## Parsing Helpers -/

def findUsedHypotheses (goalId : MVarId) (goalDecl : MetavarDecl) (mctxAfter : MetavarContext) : MetaM (List String) := do
  let some expr := mctxAfter.eAssignment.find? goalId | return []
  let fullExpr ← instantiateExprMVars expr
  let fvarIds := (collectFVars {} fullExpr).fvarIds
  return (fvarIds.filterMap goalDecl.lctx.find?).map (·.fvarId.name.toString) |>.toList

def findAssignedMVars (goalId : MVarId) (mctxAfter : MetavarContext) : MetaM (List MVarId) := do
  let some expr := mctxAfter.eAssignment.find? goalId | return []
  let (_, s) ← (Meta.collectMVars expr).run {}
  return s.result.toList

def exprKind (expr : Expr) : MetaM String := do
  if ← Meta.isProof expr then return "proof"
  if (← Meta.inferType expr).isSort then return "universe"
  return "data"

/-! ## Goto Location Resolution -/

/-- Find the binder location for a free variable in the InfoTree.
    Returns the source position where the variable was introduced. -/
def findBinderLocation (infoTree : InfoTree) (fvarId : FVarId) (text : FileMap) : Option LeanDag.GotoLocation :=
  let binderInfo? := infoTree.findInfo? fun
    | .ofTermInfo { isBinder := true, expr := .fvar id .., .. } => id == fvarId
    | _ => false
  binderInfo?.bind fun info =>
    info.range?.map fun range =>
      let lspPos := text.utf8PosToLspPos range.start
      { uri := "", position := lspPos }  -- URI will be filled in by caller

/-- Debug version that logs what it's doing. -/
def findBinderLocationDebug (infoTree : InfoTree) (fvarId : FVarId) (text : FileMap) : IO (Option LeanDag.GotoLocation) := do
  IO.eprintln s!"[goto] Looking for binder of fvarId={fvarId.name}"
  let result := findBinderLocation infoTree fvarId text
  IO.eprintln s!"[goto] Binder location result: {result.isSome}"
  return result

/-- Get the primary constant name from a type expression for goto definition. -/
partial def getTypeConstName (type : Expr) : Option Name :=
  let type := type.consumeMData
  match type with
  | .const n _ => some n
  | .app fn _ => getTypeConstName fn
  | .forallE _ _ body _ => getTypeConstName body
  | .mdata _ e => getTypeConstName e
  | _ => none

/-- Resolve the definition location of a constant.
    Returns the source file URI and position. -/
def resolveConstLocation (name : Name) : MetaM (Option LeanDag.GotoLocation) := do
  IO.eprintln s!"[goto] resolveConstLocation: name={name}"
  let env ← getEnv
  if !env.contains name then
    IO.eprintln s!"[goto] resolveConstLocation: {name} not in env"
    return none
  let some ranges ← findDeclarationRanges? name |
    IO.eprintln s!"[goto] resolveConstLocation: no ranges for {name}"
    return none
  let some modName ← findModuleOf? name |
    IO.eprintln s!"[goto] resolveConstLocation: no module for {name}"
    return none
  let some modUri ← Server.documentUriFromModule? modName |
    IO.eprintln s!"[goto] resolveConstLocation: no URI for module {modName}"
    return none
  let r := ranges.selectionRange
  IO.eprintln s!"[goto] resolveConstLocation: resolved {name} to {modUri} @ {r.pos.line - 1}:{r.charUtf16}"
  return some {
    uri := modUri
    position := ⟨r.pos.line - 1, r.charUtf16⟩
  }

/-- Try to resolve a constant location without logging.
    Returns Some if the constant has a resolvable URI, None otherwise. -/
def tryResolveConstLocation (name : Name) : MetaM (Option LeanDag.GotoLocation) := do
  let env ← getEnv
  if !env.contains name then return none
  let some ranges ← findDeclarationRanges? name | return none
  let some modName ← findModuleOf? name | return none
  let some modUri ← Server.documentUriFromModule? modName | return none
  let r := ranges.selectionRange
  return some { uri := modUri, position := ⟨r.pos.line - 1, r.charUtf16⟩ }

/-- Find the first resolvable constant in an expression.
    Prioritizes term arguments over type arguments:
    1. Check the head constant (e.g., Eq, And, Inter.inter)
    2. Check term arguments (from end of arg list, as type args come first)
    3. Fall back to type arguments if no term arg resolves -/
partial def findFirstResolvableConst (type : Expr) (depth : Nat := 0) : MetaM (Option Name) := do
  let indent := String.mk (List.replicate (depth * 2) ' ')
  let type := type.consumeMData
  IO.eprintln s!"{indent}[findConst] expr kind={type.ctorName}"
  match type with
  | .const n _ =>
    let resolved ← tryResolveConstLocation n
    IO.eprintln s!"{indent}[findConst] const {n} resolvable={resolved.isSome}"
    if resolved.isSome then return some n else return none
  | .app .. =>
    let fn := type.getAppFn.consumeMData
    let args := type.getAppArgs
    IO.eprintln s!"{indent}[findConst] app head={fn.ctorName} numArgs={args.size}"
    -- First try the head constant
    if let .const n _ := fn then
      let resolved ← tryResolveConstLocation n
      IO.eprintln s!"{indent}[findConst] head const {n} resolvable={resolved.isSome}"
      if resolved.isSome then return some n
    -- Then try arguments in reverse order (term args are typically at the end)
    for i in [:args.size] do
      let arg := args[args.size - 1 - i]!
      IO.eprintln s!"{indent}[findConst] trying arg {i} (reverse)"
      if let some n ← findFirstResolvableConst arg (depth + 1) then
        return some n
    -- Fall back to checking the function if it's not a simple constant
    if !fn.isConst then
      findFirstResolvableConst fn (depth + 1)
    else
      return none
  | .forallE _ dom body _ =>
    IO.eprintln s!"{indent}[findConst] forallE"
    if let some n ← findFirstResolvableConst body (depth + 1) then return some n
    findFirstResolvableConst dom (depth + 1)
  | .mdata _ e => findFirstResolvableConst e depth
  | _ =>
    IO.eprintln s!"{indent}[findConst] unhandled expr kind"
    return none

/-- Find the first free variable in an expression and return its type's first resolvable constant. -/
def findFirstVarTypeConst (type : Expr) (lctx : LocalContext) : MetaM (Option Name) := do
  let fvarIds := (collectFVars {} type).fvarIds
  match fvarIds[0]? with
  | some fvarId =>
    match lctx.find? fvarId with
    | some decl => findFirstResolvableConst decl.type
    | none => return none
  | none => return none

def formatGoal (ctx : ContextInfo) (id : MVarId) (infoTree : InfoTree) (text : FileMap) (fileUri : String) : RequestM ParsedGoal := do
  IO.eprintln s!"[goto] formatGoal: id={id.name}, fileUri={fileUri}"
  let some decl := ctx.mctx.findDecl? id
    | throwThe RequestError ⟨.invalidParams, "goalNotFoundInMctx"⟩
  let lctx := decl.lctx.sanitizeNames.run' {options := {}}
  let ppCtx := ctx.toPPContext lctx
  let hyps ← lctx.foldrM (init := []) fun hypDecl acc => do
    if hypDecl.isAuxDecl || hypDecl.isImplementationDetail then return acc
    let type := (← ppExprWithInfos ppCtx hypDecl.type).fmt.pretty
    let value ← hypDecl.value?.mapM fun v => do pure (← ppExprWithInfos ppCtx v).fmt.pretty
    let isProof ← ctx.runMetaM decl.lctx (exprKind hypDecl.toExpr)
    -- Resolve goto locations for the hypothesis:
    -- 'd' (definition): find first resolvable constant in the hypothesis type
    -- 't' (typeDef): find the type of the first variable in the hypothesis type
    let hypDefinition ← ctx.runMetaM decl.lctx do
      let name? ← findFirstResolvableConst hypDecl.type
      IO.eprintln s!"[goto] hyp {hypDecl.userName} definition: firstResolvableConst={name?}"
      match name? with
      | some name => resolveConstLocation name
      | none => pure none
    let hypTypeDef ← ctx.runMetaM decl.lctx do
      let name? ← findFirstVarTypeConst hypDecl.type decl.lctx
      IO.eprintln s!"[goto] hyp {hypDecl.userName} typeDef: firstVarTypeConst={name?}"
      match name? with
      | some name => resolveConstLocation name
      | none => pure none
    let gotoLocations : LeanDag.GotoLocations := {
      definition := hypDefinition
      typeDef := hypTypeDef
    }
    IO.eprintln s!"[goto] hyp {hypDecl.userName}: def={gotoLocations.definition.isSome}, typeDef={gotoLocations.typeDef.isSome}"
    return { username := hypDecl.userName.toString, type, value, id := hypDecl.fvarId.name.toString, isProof, gotoLocations } :: acc
  let type := (← ppExprWithInfos ppCtx decl.type).fmt.pretty
  -- Resolve goto locations for the goal:
  -- 'd' (definition): find first resolvable constant in the goal type
  -- 't' (typeDef): find the type of the first variable in the goal
  let goalGotoLocations : LeanDag.GotoLocations := {
    definition := ← ctx.runMetaM decl.lctx do
      let name? ← findFirstResolvableConst decl.type
      IO.eprintln s!"[goto] goal definition: firstResolvableConst={name?}"
      match name? with
      | some name => resolveConstLocation name
      | none => pure none
    typeDef := ← ctx.runMetaM decl.lctx do
      let name? ← findFirstVarTypeConst decl.type decl.lctx
      IO.eprintln s!"[goto] goal typeDef: firstVarTypeConst={name?}"
      match name? with
      | some name => resolveConstLocation name
      | none => pure none
  }
  IO.eprintln s!"[goto] goal: def={goalGotoLocations.definition.isSome}, typeDef={goalGotoLocations.typeDef.isSome}"
  return { username := decl.userName.toString, type, hyps, id, gotoLocations := goalGotoLocations }

def filterUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : List MVarId :=
  goals.filter fun id =>
    (mctx.findDecl? id).isSome && !mctx.eAssignment.contains id && !mctx.dAssignment.contains id

def computeGoalChanges (ctx : ContextInfo) (tInfo : Elab.TacticInfo) (infoTree : InfoTree) : RequestM (List (List String × ParsedGoal × List ParsedGoal)) := do
  let doc ← RequestM.readDoc
  let text := doc.meta.text
  let fileUri := doc.meta.uri
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  let ppCtx := { ctx with mctx := tInfo.mctxAfter }
  let goalsBefore := filterUnassignedGoals goalMVars tInfo.mctxBefore
  let goalsAfter := filterUnassignedGoals goalMVars tInfo.mctxAfter
  let commonGoals := goalsBefore.filter goalsAfter.contains
  let uniqueBefore := goalsBefore.filter (!commonGoals.contains ·)
  let uniqueAfter := goalsAfter.filter (!commonGoals.contains ·)
  uniqueBefore.filterMapM fun goalBefore => do
    let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore | return none
    let assignedMVars ← ctx.runMetaM goalDecl.lctx (findAssignedMVars goalBefore tInfo.mctxAfter)
    let tacticDependsOn ← ctx.runMetaM goalDecl.lctx (findUsedHypotheses goalBefore goalDecl tInfo.mctxAfter)
    let formattedBefore ← formatGoal ppCtx goalBefore infoTree text fileUri
    let formattedAfter ← (uniqueAfter.filter assignedMVars.contains).mapM fun id => formatGoal ppCtx id infoTree text fileUri
    return some (tacticDependsOn, formattedBefore, formattedAfter)

def formatRewriteSteps (stx : Syntax) (steps : List ParsedStep) : List ParsedStep :=
  match stx with
  | `(tactic| rw [$args,*] $(_)?)
  | `(tactic| rewrite [$args,*] $(_)?) =>
    let rules := args.getElems.toList
    steps.zipWith (fun step rule =>
      let ruleStr := rule.raw.getSubstring?.map (·.toString.trim) |>.getD step.tacticString
      { step with tacticString := s!"rw [{ruleStr}]" }) rules
  | _ => steps

def compareNameNum : Name → Name → Bool
  | .num _ n₁, .num _ n₂ => n₁ < n₂
  | .num _ _, _ => true
  | _, _ => false

def formatTacticString (s : String) : String :=
  (s.splitOn "\n").headD "" |>.trim

def getSourceRange (sub : Substring.Raw) : RequestM SourceRange := do
  let text := (← RequestM.readDoc).meta.text
  return { start := text.utf8PosToLspPos sub.startPos, stop := text.utf8PosToLspPos sub.stopPos }

/-! ## Main Parser -/

partial def parseTacticInfo (infoTree : InfoTree) (ctx : ContextInfo) (info : Info) (steps : List ParsedStep) (allGoals : Std.HashSet ParsedGoal) (isSingleTacticMode : Bool) (forcedTacticString : String := "") : RequestM ParseResult := do
  let some ctx := info.updateContext? ctx | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info | return { steps, allGoals }
  let some sub := getTacticSubstring tInfo | return { steps, allGoals }
  let tacticString := if forcedTacticString.isEmpty then formatTacticString sub.toString else forcedTacticString
  let steps := formatRewriteSteps tInfo.stx steps
  let position ← getSourceRange sub
  let edges ← computeGoalChanges ctx tInfo infoTree
  let currentGoals := edges.flatMap fun (_, g, gs) => g :: gs
  let allGoals := allGoals.insertMany currentGoals
  let stepGoals := steps.flatMap fun s => s.goalsAfter ++ s.spawnedGoals
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (stepGoals.foldl Std.HashSet.erase allGoals)
    |>.toArray.insertionSort (compareNameNum ·.id.name ·.id.name) |>.toList
  let theorems ← if isSingleTacticMode then getTheorems infoTree tInfo ctx else pure []
  let existingGoals := steps.map (·.goalBefore)
  let newSteps := edges.filterMap fun (deps, goalBefore, goalsAfter) =>
    if existingGoals.elem goalBefore then none
    else some { tacticString, goalBefore, goalsAfter, tacticDependsOn := deps, spawnedGoals := orphanedGoals, position, theorems }
  return { steps := newSteps ++ steps, allGoals }

partial def visitNode (infoTree : InfoTree) (ctx : ContextInfo) (info : Info) (results : List (Option ParseResult)) : RequestM ParseResult := do
  let results := results.filterMap id
  let steps := results.flatMap (·.steps)
  let allGoals := Std.HashSet.ofList (results.flatMap (·.allGoals.toList))
  parseTacticInfo infoTree ctx info steps allGoals false

partial def parseInfoTree (infoTree : InfoTree) :=
  infoTree.visitM (postNode := fun ctx info _ results => visitNode infoTree ctx info results)

end LeanDag.InfoTreeParser
