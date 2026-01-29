import Lean
import LeanAnalyzer.Types
import LeanAnalyzer.Conversion
import LeanAnalyzer.TreeBuilder
import LeanAnalyzer.ProofDag
import Services.BetterParser
import Services.GetTheorems

open Lean Elab Paperproof.Services

namespace LeanAnalyzer

inductive TacticMode | tree | singleTactic

def dummyPosition : ProofStepPosition :=
  { start := { line := 0, character := 0 }, stop := { line := 0, character := 0 } }

def staticPrintGoalInfo (printCtx : ContextInfo) (id : MVarId) : MetaM Paperproof.Services.GoalInfo := do
  let some decl := printCtx.mctx.findDecl? id | throwError "Goal not found"
  let lctx := decl.lctx |>.sanitizeNames.run' { options := {} }
  let ppCtx := printCtx.toPPContext lctx
  let hyps ← lctx.foldrM (init := []) fun h acc => do
    if h.isAuxDecl || h.isImplementationDetail then return acc
    let type ← ppExprWithInfos ppCtx h.type
    let value ← match h.value? with | some v => some <$> ppExprWithInfos ppCtx v | none => pure none
    let isProof ← printCtx.runMetaM decl.lctx (mayBeProof h.toExpr)
    return { username := h.userName.toString, type := type.fmt.pretty
             value := value.map (·.fmt.pretty), id := h.fvarId.name.toString, isProof } :: acc
  return { username := decl.userName.toString, type := (← ppExprWithInfos ppCtx decl.type).fmt.pretty, hyps, id }

def staticGetUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : List MVarId :=
  goals.filter fun id => (mctx.findDecl? id).isSome && !mctx.eAssignment.contains id && !mctx.dAssignment.contains id

def staticGetGoalsChange (ctx : ContextInfo) (tInfo : Elab.TacticInfo) :
    MetaM (List (List String × Paperproof.Services.GoalInfo × List Paperproof.Services.GoalInfo)) := do
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  let printCtx := { ctx with mctx := tInfo.mctxAfter }
  let goalsBefore := staticGetUnassignedGoals goalMVars tInfo.mctxBefore
  let goalsAfter := staticGetUnassignedGoals goalMVars tInfo.mctxAfter
  let common := goalsBefore.filter goalsAfter.contains
  let goalsBefore := goalsBefore.filter (!common.contains ·)
  let goalsAfter := goalsAfter.filter (!common.contains ·)

  goalsBefore.filterMapM fun goalBefore => do
    let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore | return none
    let assignedMVars ← ctx.runMetaM goalDecl.lctx (findMVarsAssigned goalBefore tInfo.mctxAfter)
    let tacticDependsOn ← ctx.runMetaM goalDecl.lctx (findHypsUsedByTactic goalBefore goalDecl tInfo.mctxAfter)
    let goalInfoBefore ← staticPrintGoalInfo printCtx goalBefore
    let goalsInfoAfter ← goalsAfter.filter assignedMVars.contains |>.mapM (staticPrintGoalInfo printCtx)
    return some (tacticDependsOn, goalInfoBefore, goalsInfoAfter)

def findTheoremsForTactic (infoTree : InfoTree) (ctx : ContextInfo) (tInfo : Elab.TacticInfo) : MetaM (List TheoremSignature) :=
  match ctx.mctx.findDecl? tInfo.goalsBefore.head!, getTacticSubstring tInfo with
  | some goalDecl, some sub => ctx.runMetaM goalDecl.lctx (findTheoremsLikeHover infoTree sub.startPos sub.stopPos ctx goalDecl)
  | _, _ => pure []

partial def staticParseTacticCore (infoTree : InfoTree) (ctx : ContextInfo) (tInfo : Elab.TacticInfo)
    (existingSteps : List ProofStep) : MetaM Result := do
  let some tacticSubstring := getTacticSubstring tInfo | return { steps := existingSteps, allGoals := ∅ }
  let tacticString := prettifyTacticString tacticSubstring.toString
  let steps := prettifySteps tInfo.stx existingSteps
  let proofTreeEdges ← staticGetGoalsChange ctx tInfo
  let currentGoals := proofTreeEdges.flatMap fun ⟨_, g₁, gs⟩ => g₁ :: gs
  let allGoals := Std.HashSet.ofList currentGoals |>.insertMany (steps.flatMap stepGoalsAfter)
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals steps)
    |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList
  let theorems ← findTheoremsForTactic infoTree ctx tInfo
  let newSteps := proofTreeEdges.filterMap fun ⟨tacticDependsOn, goalBefore, goalsAfter⟩ =>
    if existingSteps.any (·.goalBefore == goalBefore) then none
    else some { tacticString, goalBefore, goalsAfter, tacticDependsOn, spawnedGoals := orphanedGoals, position := dummyPosition, theorems }
  return { steps := newSteps ++ steps, allGoals }

partial def staticPostNode (infoTree : InfoTree) (ctx : ContextInfo) (info : Info)
    (results : List (Option Result)) : MetaM Result := do
  let some ctx := info.updateContext? ctx | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info | return { steps := [], allGoals := ∅ }
  let filteredResults := results.filterMap id
  let existingSteps := filteredResults.flatMap (·.steps)
  staticParseTacticCore infoTree ctx tInfo existingSteps

partial def staticBetterParser (infoTree : InfoTree) :=
  infoTree.visitM (postNode := fun ctx info _ results => staticPostNode infoTree ctx info results)

def findInfoTreeAtPosition (trees : Array InfoTree) (fileMap : FileMap) (line col : Nat) : Option InfoTree :=
  let pos := fileMap.lspPosToUtf8Pos ⟨line, col⟩
  trees.find? fun tree => tree.collectNodesBottomUp (fun _ info _ acc =>
    match info with
    | .ofTacticInfo _ =>
      match info.pos?, info.tailPos? with
      | some s, some e => if s <= pos && pos < e then true :: acc else acc
      | _, _ => acc
    | _ => acc) |>.any id

private structure GoalsAtInternal where
  ctxInfo : ContextInfo
  tacticInfo : Elab.TacticInfo
  indented : Bool
  priority : Nat

partial def staticGoalsAt? (t : InfoTree) (fileMap : FileMap) (hoverPos : String.Pos.Raw) : Option (ContextInfo × Elab.TacticInfo) :=
  let hasNestedTactic (cs : PersistentArray InfoTree) (pos tailPos : String.Pos.Raw) : Bool := cs.any fun
    | .node j@(.ofTacticInfo _) _ =>
      if let `(by $_) := j.stx then false
      else match j.pos?, j.tailPos? with
        | some p', some t' => t' > hoverPos && (p', t') != (pos, tailPos)
        | _, _ => false
    | _ => false
  let isEmptyBy (stx : Syntax) := stx.getNumArgs == 2 && stx[0].isToken "by" && stx[1].getNumArgs == 1 && stx[1][0].isMissing
  let gs : List GoalsAtInternal := t.collectNodesBottomUp fun ctx i cs gs => Id.run do
    let .ofTacticInfo ti := i | return gs
    let (some pos, some tailPos) := (i.pos?, i.tailPos?) | return gs
    let trailSize := i.stx.getTrailingSize
    let atEOF := tailPos.byteIdx + trailSize == fileMap.source.rawEndPos.byteIdx
    if !(pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + max 1 trailSize || atEOF)) then return gs
    if ti.stx.getAtomVal == "]" then return gs
    let indented := (fileMap.toPosition pos).column > (fileMap.toPosition hoverPos).column
    if !(gs.isEmpty || (hoverPos ≥ tailPos && gs.all (·.indented))) then return gs
    if (hoverPos > pos && hasNestedTactic cs pos tailPos) || isEmptyBy i.stx then return gs
    return [{ ctxInfo := ctx, tacticInfo := ti, indented, priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1 }]
  let maxPrio? := gs.map (·.priority) |>.max?
  gs.filter (some ·.priority == maxPrio?) |>.head?.map fun r => (r.ctxInfo, r.tacticInfo)

unsafe def processAllCommands : Frontend.FrontendM (List (Environment × InfoState)) := do
  let done ← Frontend.processCommand
  let st ← get
  let result := (st.commandState.env, st.commandState.infoState)
  set { st with commandState := { st.commandState with infoState := {} } }
  if done then return [result] else return result :: (← processAllCommands)

def runInCoreM (ctx : Core.Context) (env : Environment) (x : MetaM α) : IO α := do
  let state : Core.State := { env, messages := MessageLog.empty }
  let ((result, _), _) ← (x.run {} {}).toIO ctx state
  return result

structure ProcessedFile where
  steps : List (Environment × InfoState)
  trees : Array InfoTree
  fileMap : FileMap
  lastEnv : Environment
  filePath : System.FilePath

unsafe def loadFile (filePath : System.FilePath) : IO (Except String ProcessedFile) := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile filePath) filePath.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header {} messages inputCtx
  if messages.hasErrors then return .error "Errors during import"
  let env := env.setMainModule (← moduleNameOfFileName filePath none)
  let (steps, _) ← (processAllCommands.run { inputCtx }).run
    { commandState := { Command.mkState env messages {} with infoState.enabled := true }, parserState, cmdPos := parserState.pos }
  let some ⟨lastEnv, _⟩ := steps.getLast? | return .error "No commands processed"
  return .ok { steps, trees := steps.foldl (fun acc ⟨_, s⟩ => acc ++ s.trees.toArray) #[], fileMap := inputCtx.fileMap, lastEnv, filePath }

unsafe def queryProofSteps (pf : ProcessedFile) (line col : Nat) (mode : TacticMode) : IO (List ProofStep) := do
  let some tree := findInfoTreeAtPosition pf.trees pf.fileMap line col | return []
  let ctx : Core.Context := { fileName := pf.filePath.toString, fileMap := pf.fileMap, options := {} }
  match mode with
  | .tree => match ← runInCoreM ctx pf.lastEnv (staticBetterParser tree) with
    | some r => return r.steps
    | none => return []
  | .singleTactic =>
    let some (ctxInfo, tacticInfo) := staticGoalsAt? tree pf.fileMap (pf.fileMap.lspPosToUtf8Pos ⟨line, col⟩)
      | return []
    let r ← runInCoreM ctx pf.lastEnv (staticParseTacticCore tree ctxInfo tacticInfo [])
    return r.steps

unsafe def queryProofDag (pf : ProcessedFile) (line col : Nat) (mode : TacticMode := .tree) : IO ProofDag := do
  let steps ← queryProofSteps pf line col mode
  return buildProofDag steps line col

end LeanAnalyzer
