import Lean
import Lean.Meta.Basic
import Lean.Meta.CollectMVars

open Lean Elab Server

namespace LeanAnalyzer.InfoTreeParser

/-! ## Tactic Substring Extraction -/

def getTacticSubstring (tInfo : TacticInfo) : Option Substring.Raw :=
  match tInfo.stx.getSubstring? with
  | .some substring => substring
  | .none => none

/-! ## Goals At Position -/

partial def goalsAt? (t : InfoTree) (text : FileMap) (hoverPos : String.Pos.Raw) : List GoalsAtResult :=
  let gs := t.collectNodesBottomUp fun ctx i cs gs => Id.run do
    if let Info.ofTacticInfo ti := i then
      if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
        let trailSize := i.stx.getTrailingSize
        let atEOF := tailPos.byteIdx + trailSize == text.source.rawEndPos.byteIdx
        if pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + max 1 trailSize || atEOF) then
          let isClosingBracketInRewriteSequence := ti.stx.getAtomVal == "]"
          if (gs.isEmpty || (hoverPos ≥ tailPos && gs.all (·.indented))) && !isClosingBracketInRewriteSequence then
            return [{
              ctxInfo := ctx
              tacticInfo := ti
              useAfter := hoverPos > pos && !cs.any (hasNestedTactic pos tailPos)
              indented := (text.toPosition pos).column > (text.toPosition hoverPos).column && !isEmptyBy ti.stx
              priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1
            }]
    return gs
  let maxPrio? := gs.map (·.priority) |>.max?
  gs.filter (some ·.priority == maxPrio?)
where
  hasNestedTactic (pos tailPos) : InfoTree → Bool
    | InfoTree.node i@(Info.ofTacticInfo _) cs => Id.run do
      if let `(by $_) := i.stx then
        return false
      if let (some pos', some tailPos') := (i.pos?, i.tailPos?) then
        if tailPos' > hoverPos && (pos', tailPos') != (pos, tailPos) then
          return true
      cs.any (hasNestedTactic pos tailPos)
    | InfoTree.node (Info.ofMacroExpansionInfo _) cs =>
      cs.any (hasNestedTactic pos tailPos)
    | _ => false
  isEmptyBy (stx : Syntax) : Bool :=
    stx.getNumArgs == 2 && stx[0].isToken "by" && stx[1].getNumArgs == 1 && stx[1][0].isMissing

/-! ## Theorem Extraction -/

structure ArgumentInfo where
  name : String
  type : String
  deriving Inhabited, FromJson, ToJson

structure TheoremSignature where
  name              : String
  instanceArgs      : List ArgumentInfo := []
  implicitArgs      : List ArgumentInfo := []
  explicitArgs      : List ArgumentInfo := []
  type              : String := ""
  declarationType   : String := ""
  body              : Option String := none
  deriving Inhabited, FromJson, ToJson

def extractArgsWithTypes (expr : Expr) : MetaM (List ArgumentInfo × List ArgumentInfo × List ArgumentInfo × String) := do
  Meta.forallTelescope expr fun args body => do
    let mut lctx := LocalContext.empty
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      lctx := lctx.addDecl decl
    let ppCtx : PPContext := { env := ← getEnv, mctx := ← getMCtx, lctx, opts := (← getOptions).setBool `pp.fullNames true }
    let mut instanceArgs := []
    let mut implicitArgs := []
    let mut explicitArgs := []
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      let typeStr ← ppExprWithInfos ppCtx decl.type
      let argInfo := { name := decl.userName.toString, type := typeStr.fmt.pretty : ArgumentInfo }
      match decl.binderInfo with
      | BinderInfo.instImplicit => instanceArgs := instanceArgs ++ [argInfo]
      | BinderInfo.implicit => implicitArgs := implicitArgs ++ [argInfo]
      | BinderInfo.strictImplicit => implicitArgs := implicitArgs ++ [argInfo]
      | BinderInfo.default => explicitArgs := explicitArgs ++ [argInfo]
    let bodyStr ← ppExprWithInfos ppCtx body
    return (instanceArgs, implicitArgs, explicitArgs, bodyStr.fmt.pretty)

def declarationKind (ci : ConstantInfo) : String :=
  match ci with
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
  unless (declType == "theorem" || declType == "axiom" || declType == "def") do
    return none
  let ppCtx := { (ctx.toPPContext (goalDecl.lctx |>.sanitizeNames.run' {options := {}})) with
    opts := (ctx.toPPContext goalDecl.lctx).opts.setBool `pp.fullNames true }
  let nameStr ← ppExprWithInfos ppCtx (mkConst constInfo.name)
  let (instanceArgs, implicitArgs, explicitArgs, typeStr) ← extractArgsWithTypes constInfo.type
  let declBody ←
    if declType == "def" then
      match constInfo.value? with
      | some expr => do
        let bodyStr ← ppExprWithInfos ppCtx expr
        pure (some bodyStr.fmt.pretty)
      | none => pure none
    else
      pure none
  return some { name := nameStr.fmt.pretty, instanceArgs, implicitArgs, explicitArgs, type := typeStr, declarationType := declType, body := declBody }

def extractConstName (expr : Expr) (lctx : LocalContext) : Option Name := do
  guard (!expr.isSyntheticSorry)
  let cleanExpr := expr.consumeMData
  match cleanExpr with
  | .const name _ => some name
  | .app .. => expr.getAppFn.consumeMData.constName?
  | .fvar .. => do
    let ldecl ← lctx.findFVar? cleanExpr
    let val ← ldecl.value?
    val.getAppFn.consumeMData.constName?
  | _ => none

def findTheoremsInRange (tree : Elab.InfoTree) (startPos stopPos : String.Pos.Raw) (ctx : ContextInfo) (goalDecl : MetavarDecl) : MetaM (List TheoremSignature) := do
  let mut theoremNames : NameSet := {}
  let mut currentPos := startPos
  let step : Nat := 3
  while currentPos < stopPos do
    if let some infoWithCtx ← tree.hoverableInfoAtM? currentPos then
      match infoWithCtx.info with
      | .ofTermInfo termInfo =>
        if let some name := extractConstName termInfo.expr termInfo.lctx then
          theoremNames := theoremNames.insert name
      | _ => pure ()
    currentPos := ⟨currentPos.byteIdx + step⟩
  let theoremSignatures ← theoremNames.toList.filterMapM fun name => do
    let resolvedName ← resolveGlobalConstNoOverloadCore name
    formatDeclaration resolvedName ctx goalDecl
  pure theoremSignatures

def getTheorems (infoTree : InfoTree) (tacticInfo : TacticInfo) (ctx : ContextInfo) : RequestM (List TheoremSignature) := do
  let some goalDecl := ctx.mctx.findDecl? tacticInfo.goalsBefore.head!
    | throwThe RequestError ⟨.invalidParams, "noGoalDecl"⟩
  let some tacticSubstring := getTacticSubstring tacticInfo
    | throwThe RequestError ⟨.invalidParams, "noTacticSubstring"⟩
  ctx.runMetaM goalDecl.lctx do
    findTheoremsInRange infoTree tacticSubstring.startPos tacticSubstring.stopPos ctx goalDecl

/-! ## Parsed Proof Types (intermediate representation) -/

structure ParsedHypothesis where
  username : String
  type : String
  value : Option String
  id : String
  isProof : String
  deriving Inhabited, ToJson, FromJson

structure ParsedGoal where
  username : String
  type : String
  hyps : List ParsedHypothesis
  id : MVarId
  deriving Inhabited, ToJson, FromJson

instance : BEq ParsedGoal where
  beq g1 g2 := g1.id == g2.id

instance : Hashable ParsedGoal where
  hash g := hash g.id

structure SourceRange where
  start : Lsp.Position
  stop : Lsp.Position
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
  steps : List ParsedStep
  allGoals : Std.HashSet ParsedGoal

/-! ## Parsing Helpers -/

def stepGoalsAfter (step : ParsedStep) : List ParsedGoal := step.goalsAfter ++ step.spawnedGoals

def goalsWithoutInEdges (allGoals : Std.HashSet ParsedGoal) (steps : List ParsedStep) : Std.HashSet ParsedGoal :=
  (steps.flatMap stepGoalsAfter).foldl Std.HashSet.erase allGoals

def findUsedHypotheses (goalId: MVarId) (goalDecl : MetavarDecl) (mctxAfter : MetavarContext) : MetaM (List String) := do
  let some expr := mctxAfter.eAssignment.find? goalId | return []
  let fullExpr ← instantiateExprMVars expr
  let fvarIds := (collectFVars {} fullExpr).fvarIds
  let fvars := fvarIds.filterMap goalDecl.lctx.find?
  return fvars.map (fun x => x.fvarId.name.toString) |>.toList

def findAssignedMVars (goalId : MVarId) (mctxAfter : MetavarContext) : MetaM (List MVarId) := do
  let some expr := mctxAfter.eAssignment.find? goalId | return []
  let (_, s) ← (Meta.collectMVars expr).run {}
  return s.result.toList

def exprKind (expr : Expr) : MetaM String := do
  let type : Expr ← Lean.Meta.inferType expr
  if ← Meta.isProof expr then return "proof"
  if type.isSort then return "universe"
  else return "data"

def formatGoal (ctx : ContextInfo) (id : MVarId) : RequestM ParsedGoal := do
  let some decl := ctx.mctx.findDecl? id
    | throwThe RequestError ⟨.invalidParams, "goalNotFoundInMctx"⟩
  let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
  let ppContext := ctx.toPPContext lctx
  let hyps ← lctx.foldrM (init := []) (fun hypDecl acc => do
    if hypDecl.isAuxDecl || hypDecl.isImplementationDetail then return acc
    let type ← liftM (ppExprWithInfos ppContext hypDecl.type)
    let value ← liftM (hypDecl.value?.mapM (ppExprWithInfos ppContext))
    let isProof : String ← ctx.runMetaM decl.lctx (exprKind hypDecl.toExpr)
    return ({ username := hypDecl.userName.toString, type := type.fmt.pretty, value := value.map (·.fmt.pretty), id := hypDecl.fvarId.name.toString, isProof } : ParsedHypothesis) :: acc)
  return { username := decl.userName.toString, type := (← ppExprWithInfos ppContext decl.type).fmt.pretty, hyps, id }

def filterUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : RequestM (List MVarId) := do
  goals.filterMapM fun id => do
    if let none := mctx.findDecl? id then return none
    if mctx.eAssignment.contains id || mctx.dAssignment.contains id then return none
    return some id

def computeGoalChanges (ctx : ContextInfo) (tInfo : TacticInfo) : RequestM (List (List String × ParsedGoal × List ParsedGoal)) := do
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  let ppCtx := {ctx with mctx := tInfo.mctxAfter}
  let mut goalsBefore ← filterUnassignedGoals goalMVars tInfo.mctxBefore
  let mut goalsAfter ← filterUnassignedGoals goalMVars tInfo.mctxAfter
  let commonGoals := goalsBefore.filter fun g => goalsAfter.contains g
  goalsBefore := goalsBefore.filter (!commonGoals.contains ·)
  goalsAfter := goalsAfter.filter (!commonGoals.contains ·)
  let mut result : List (List String × ParsedGoal × List ParsedGoal) := []
  for goalBefore in goalsBefore do
    if let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore then
      let assignedMVars ← ctx.runMetaM goalDecl.lctx (findAssignedMVars goalBefore tInfo.mctxAfter)
      let tacticDependsOn ← ctx.runMetaM goalDecl.lctx (findUsedHypotheses goalBefore goalDecl tInfo.mctxAfter)
      result := (tacticDependsOn, ← formatGoal ppCtx goalBefore, ← goalsAfter.filter assignedMVars.contains |>.mapM (formatGoal ppCtx)) :: result
  return result

def formatRewriteSteps (stx : Syntax) (steps : List ParsedStep) : List ParsedStep := Id.run do
  match stx with
  | `(tactic| rw [$_,*] $(_)?)
  | `(tactic| rewrite [$_,*] $(_)?) =>
    let format (tStr : String) :=
      let res := tStr.trim.dropRightWhile (· == ',')
      if res == "]" then "rfl" else res
    return steps.map fun a => { a with tacticString := s!"rw [{format a.tacticString}]" }
  | _ => return steps

def compareNameNum (n1 n2 : Name) : Bool :=
  match n1, n2 with
  | .num _ n₁, .num _ n₂ => n₁ < n₂
  | .num _ _,  _ => true
  | _, _ => false

def formatTacticString (tacticString: String) : String :=
  (tacticString.splitOn "\n").head!.trim

def getSourceRange (tacticSubstring: Substring.Raw) : RequestM SourceRange := do
  let doc ← Lean.Server.RequestM.readDoc
  let text : FileMap := doc.meta.text
  return { start := Lean.FileMap.utf8PosToLspPos text tacticSubstring.startPos, stop := Lean.FileMap.utf8PosToLspPos text tacticSubstring.stopPos }

/-! ## Main Parser -/

partial def parseTacticInfo (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (steps : List ParsedStep) (allGoals : Std.HashSet ParsedGoal) (isSingleTacticMode : Bool) (forcedTacticString : String := "") : RequestM ParseResult := do
  let .some ctx := info.updateContext? ctx | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info | return { steps, allGoals }
  let .some tacticSubstring := getTacticSubstring tInfo | return { steps, allGoals }
  let mut tacticString := if forcedTacticString.length > 0 then forcedTacticString else formatTacticString (Substring.Raw.toString tacticSubstring)
  let steps := formatRewriteSteps tInfo.stx steps
  let position ← getSourceRange tacticSubstring
  let proofTreeEdges ← computeGoalChanges ctx tInfo
  let currentGoals := proofTreeEdges.map (fun ⟨ _, g₁, gs ⟩ => g₁ :: gs) |>.flatten
  let allGoals := allGoals.insertMany $ currentGoals
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (goalsWithoutInEdges allGoals steps)
    |>.toArray.insertionSort (compareNameNum ·.id.name ·.id.name) |>.toList
  let theorems ← if isSingleTacticMode then getTheorems infoTree tInfo ctx else pure []
  let newSteps := proofTreeEdges.filterMap fun ⟨ tacticDependsOn, goalBefore, goalsAfter ⟩ =>
    if steps.map (·.goalBefore) |>.elem goalBefore then none
    else some { tacticString, goalBefore, goalsAfter, tacticDependsOn, spawnedGoals := orphanedGoals, position, theorems }
  return { steps := newSteps ++ steps, allGoals }

partial def visitNode (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (results : List (Option ParseResult)) : RequestM ParseResult := do
  let results : List ParseResult := results.filterMap id
  let steps : List ParsedStep := (results.map (λ result => result.steps)).flatten
  let allGoals : Std.HashSet ParsedGoal := Std.HashSet.ofList ((results.map (λ result => result.allGoals.toList)).flatten)
  parseTacticInfo infoTree ctx info steps allGoals (isSingleTacticMode := false)

partial def parseInfoTree (infoTree : InfoTree) := infoTree.visitM (postNode := λ ctx info _ results => visitNode infoTree ctx info results)

end LeanAnalyzer.InfoTreeParser
