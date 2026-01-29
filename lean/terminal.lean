/-
  # Paperproof CLI

  Static extraction of proof structures to JSON for AI applications and VS Code extension fallback.

  ## Usage

  ### By Position (for VS Code extension / lean-tui)
  ```shell
  lake exe paperproof-cli --by-position FILE LINE COLUMN MODE
  ```
  Outputs JSON to stdout. LINE and COLUMN are 0-indexed. MODE is 'tree' or 'single_tactic'.

  ### By Constant Name
  ```shell
  lake exe paperproof-cli --by-name FILE CONSTANT_NAME OUTPUT_PATH
  ```
  Saves the proof structure of a theorem to a JSON file.
-/
import Lean
import Services.BetterParser
import Services.GetTheorems

open Lean Elab Paperproof.Services

/-! ## Configuration -/

inductive TacticMode | tree | singleTactic
  deriving Repr

inductive LookupMode
  | byName (constName : Name) (outputPath : System.FilePath)
  | byPosition (line column : Nat) (mode : TacticMode)

structure Config where
  filePath : System.FilePath
  lookupMode : LookupMode

/-! ## Argument Parsing -/

def parseMode : String → Option TacticMode
  | "tree" => some .tree
  | "single_tactic" => some .singleTactic
  | _ => none

def parseArgs : List String → Except String Config
  | ["--by-name", file, name, output] =>
    .ok { filePath := ⟨file⟩, lookupMode := .byName name.toName ⟨output⟩ }
  | ["--by-position", file, lineStr, colStr, modeStr] =>
    match lineStr.toNat?, colStr.toNat?, parseMode modeStr with
    | some line, some col, some mode =>
      .ok { filePath := ⟨file⟩, lookupMode := .byPosition line col mode }
    | none, _, _ => .error s!"Invalid line: {lineStr}"
    | _, none, _ => .error s!"Invalid column: {colStr}"
    | _, _, none => .error s!"Invalid mode: {modeStr}. Use 'tree' or 'single_tactic'"
  | _ => .error "Usage: paperproof-cli [--by-name FILE NAME OUTPUT | --by-position FILE LINE COL MODE]"

/-! ## Static Proof Extraction (MetaM versions of RequestM functions) -/

def dummyPosition : ProofStepPosition :=
  { start := { line := 0, character := 0 }, stop := { line := 0, character := 0 } }

def staticPrintGoalInfo (printCtx : ContextInfo) (id : MVarId) : MetaM GoalInfo := do
  let some decl := printCtx.mctx.findDecl? id | throwError "Goal not found"
  let lctx := decl.lctx |>.sanitizeNames.run' { options := {} }
  let ppCtx := printCtx.toPPContext lctx
  let hyps ← lctx.foldrM (init := []) fun hypDecl acc => do
    if hypDecl.isAuxDecl || hypDecl.isImplementationDetail then return acc
    let type ← ppExprWithInfos ppCtx hypDecl.type
    let value ← match hypDecl.value? with
      | some v => some <$> ppExprWithInfos ppCtx v
      | none => pure none
    let isProof ← printCtx.runMetaM decl.lctx (mayBeProof hypDecl.toExpr)
    return { username := hypDecl.userName.toString
             type := type.fmt.pretty
             value := value.map (·.fmt.pretty)
             id := hypDecl.fvarId.name.toString
             isProof } :: acc
  let targetType ← ppExprWithInfos ppCtx decl.type
  return { username := decl.userName.toString
           type := targetType.fmt.pretty
           hyps, id }

def staticGetUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : List MVarId :=
  goals.filter fun id =>
    (mctx.findDecl? id).isSome &&
    !(mctx.eAssignment.contains id) &&
    !(mctx.dAssignment.contains id)

def staticGetGoalsChange (ctx : ContextInfo) (tInfo : TacticInfo) :
    MetaM (List (List String × GoalInfo × List GoalInfo)) := do
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

partial def staticParseTacticInfo (infoTree : InfoTree) (ctx : ContextInfo) (info : Info)
    (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo) : MetaM Result := do
  let some ctx := info.updateContext? ctx | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info | return { steps, allGoals }
  let some tacticSubstring := getTacticSubstring tInfo | return { steps, allGoals }

  let tacticString := prettifyTacticString tacticSubstring.toString
  let steps := prettifySteps tInfo.stx steps
  let proofTreeEdges ← staticGetGoalsChange ctx tInfo
  let currentGoals := proofTreeEdges.flatMap fun ⟨_, g₁, gs⟩ => g₁ :: gs
  let allGoals := allGoals.insertMany currentGoals
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals steps)
    |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList

  let theorems ← match ctx.mctx.findDecl? tInfo.goalsBefore.head!, getTacticSubstring tInfo with
    | some goalDecl, some sub =>
      ctx.runMetaM goalDecl.lctx (findTheoremsLikeHover infoTree sub.startPos sub.stopPos ctx goalDecl)
    | _, _ => pure []

  let newSteps := proofTreeEdges.filterMap fun ⟨tacticDependsOn, goalBefore, goalsAfter⟩ =>
    if steps.any (·.goalBefore == goalBefore) then none
    else some { tacticString, goalBefore, goalsAfter, tacticDependsOn
                spawnedGoals := orphanedGoals, position := dummyPosition, theorems }
  return { steps := newSteps ++ steps, allGoals }

partial def staticPostNode (infoTree : InfoTree) (ctx : ContextInfo) (info : Info)
    (results : List (Option Result)) : MetaM Result := do
  let results := results.filterMap id
  let steps := results.flatMap (·.steps)
  let allGoals := Std.HashSet.ofList (results.flatMap (·.allGoals.toList))
  staticParseTacticInfo infoTree ctx info steps allGoals

partial def staticBetterParser (infoTree : InfoTree) :=
  infoTree.visitM (postNode := fun ctx info _ results => staticPostNode infoTree ctx info results)

/-! ## Position-based Lookup -/

def positionInRange (pos startPos endPos : String.Pos.Raw) : Bool :=
  startPos <= pos && pos < endPos

def findInfoTreeAtPosition (trees : Array InfoTree) (fileMap : FileMap) (line col : Nat) : Option InfoTree :=
  let pos := fileMap.lspPosToUtf8Pos ⟨line, col⟩
  trees.find? fun tree =>
    let found := tree.collectNodesBottomUp fun _ info _ acc => Id.run do
      if let .ofTacticInfo _ := info then
        if let (some s, some e) := (info.pos?, info.tailPos?) then
          if positionInRange pos s e then return true :: acc
      return acc
    found.any id

/-! ## Single Tactic Mode -/

private structure GoalsAtInternal where
  ctxInfo : ContextInfo
  tacticInfo : TacticInfo
  useAfter : Bool
  indented : Bool
  priority : Nat

structure StaticGoalsAtResult where
  ctxInfo : ContextInfo
  tacticInfo : TacticInfo

partial def staticGoalsAt? (t : InfoTree) (fileMap : FileMap) (hoverPos : String.Pos.Raw) : List StaticGoalsAtResult :=
  let gs : List GoalsAtInternal := t.collectNodesBottomUp fun ctx i cs gs => Id.run do
    if let .ofTacticInfo ti := i then
      if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
        let trailSize := i.stx.getTrailingSize
        let atEOF := tailPos.byteIdx + trailSize == fileMap.source.rawEndPos.byteIdx
        if pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + max 1 trailSize || atEOF) then
          let isClosingBracket := ti.stx.getAtomVal == "]"
          if (gs.isEmpty || (hoverPos ≥ tailPos && gs.all (·.indented))) && !isClosingBracket then
            return [{ ctxInfo := ctx, tacticInfo := ti
                      useAfter := hoverPos > pos && !cs.any (hasNestedTactic pos tailPos)
                      indented := (fileMap.toPosition pos).column > (fileMap.toPosition hoverPos).column && !isEmptyBy ti.stx
                      priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1 }]
    return gs
  let maxPrio? := gs.map (·.priority) |>.max?
  gs.filter (some ·.priority == maxPrio?) |>.map fun r => ⟨r.ctxInfo, r.tacticInfo⟩
where
  hasNestedTactic (pos tailPos) : InfoTree → Bool
    | .node i@(.ofTacticInfo _) cs => Id.run do
      if let `(by $_) := i.stx then return false
      if let (some pos', some tailPos') := (i.pos?, i.tailPos?) then
        if tailPos' > hoverPos && (pos', tailPos') != (pos, tailPos) then return true
      cs.any (hasNestedTactic pos tailPos)
    | .node (.ofMacroExpansionInfo _) cs => cs.any (hasNestedTactic pos tailPos)
    | _ => false
  isEmptyBy (stx : Syntax) : Bool :=
    stx.getNumArgs == 2 && stx[0].isToken "by" && stx[1].getNumArgs == 1 && stx[1][0].isMissing

partial def staticParseSingleTactic (infoTree : InfoTree) (ctx : ContextInfo) (info : Info) : MetaM Result := do
  let .ofTacticInfo tInfo := info | return { steps := [], allGoals := ∅ }
  let some tacticSubstring := getTacticSubstring tInfo | return { steps := [], allGoals := ∅ }

  let tacticString := prettifyTacticString tacticSubstring.toString
  let proofTreeEdges ← staticGetGoalsChange ctx tInfo
  let currentGoals := proofTreeEdges.flatMap fun ⟨_, g₁, gs⟩ => g₁ :: gs
  let allGoals := Std.HashSet.ofList currentGoals
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals [])
    |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList

  let theorems ← match ctx.mctx.findDecl? tInfo.goalsBefore.head!, getTacticSubstring tInfo with
    | some goalDecl, some sub =>
      ctx.runMetaM goalDecl.lctx (findTheoremsLikeHover infoTree sub.startPos sub.stopPos ctx goalDecl)
    | _, _ => pure []

  let newSteps := proofTreeEdges.map fun ⟨tacticDependsOn, goalBefore, goalsAfter⟩ =>
    { tacticString, goalBefore, goalsAfter, tacticDependsOn
      spawnedGoals := orphanedGoals, position := dummyPosition, theorems }
  return { steps := newSteps, allGoals }

/-! ## JSON Output -/

instance : ToJson Result where
  toJson r := Json.mkObj [("steps", toJson r.steps), ("allGoals", toJson r.allGoals.toList)]

def outputJson (r : Result) (version : Nat := 4) : IO Unit :=
  IO.println <| Json.compress <| Json.mkObj [("steps", toJson r.steps), ("version", toJson version)]

def outputError (msg : String) : IO Unit :=
  IO.println <| Json.compress <| Json.mkObj [("error", toJson msg)]

def saveResult (r : Result) (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path (Json.pretty (toJson r))

/-! ## Frontend Processing -/

unsafe def processAllCommands : Frontend.FrontendM (List (Environment × InfoState)) := do
  let done ← Frontend.processCommand
  let st ← get
  let result := (st.commandState.env, st.commandState.infoState)
  set { st with commandState := { st.commandState with infoState := {} } }
  if done then return [result]
  else return result :: (← processAllCommands)

def runInCoreM (ctx : Core.Context) (env : Environment) (x : MetaM α) : IO α := do
  let state : Core.State := { env, messages := MessageLog.empty }
  let ((result, _), _) ← (x.run {} {}).toIO ctx state
  return result

/-! ## Main Logic -/

unsafe def processFile (config : Config) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let input ← IO.FS.readFile config.filePath
  Lean.enableInitializersExecution

  let inputCtx := Parser.mkInputContext input config.filePath.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header {} messages inputCtx

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then IO.eprintln s!"ERROR: {← msg.toString}"
    match config.lookupMode with
    | .byPosition .. => outputError "Errors during import"
    | .byName .. => throw <| IO.userError "Errors during import"
    return

  let env := env.setMainModule (← moduleNameOfFileName config.filePath none)
  let fileMap := inputCtx.fileMap
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }
  let (steps, _) ← (processAllCommands.run { inputCtx }).run
    { commandState, parserState, cmdPos := parserState.pos }

  match config.lookupMode with
  | .byName constName outputPath => processConstant steps env constName outputPath
  | .byPosition line col mode => processPosition steps fileMap config.filePath line col mode

where
  processConstant (steps : List (Environment × InfoState)) (origEnv : Environment)
      (constName : Name) (outputPath : System.FilePath) : IO Unit := do
    if origEnv.contains constName then
      throw <| IO.userError s!"{constName} already exists in base environment"
    for ⟨env', s⟩ in steps do
      if env'.contains constName then
        for tree in s.trees do
          let ctx : Core.Context := { fileName := "", fileMap := default, options := {} }
          match ← runInCoreM ctx env' (staticBetterParser tree) with
          | some r => saveResult r outputPath
          | none => IO.eprintln "Failed to parse proof tree"
        return

  processPosition (steps : List (Environment × InfoState)) (fileMap : FileMap)
      (filePath : System.FilePath) (line col : Nat) (mode : TacticMode) : IO Unit := do
    let trees := steps.foldl (fun acc ⟨_, s⟩ => acc ++ s.trees.toArray) #[]
    let some tree := findInfoTreeAtPosition trees fileMap line col
      | outputError "No proof found at position"
    let some ⟨lastEnv, _⟩ := steps.getLast?
      | outputError "No commands processed"
    let ctx : Core.Context := { fileName := filePath.toString, fileMap, options := {} }

    match mode with
    | .tree =>
      match ← runInCoreM ctx lastEnv (staticBetterParser tree) with
      | some r => if r.steps.isEmpty then outputError "zeroProofSteps" else outputJson r
      | none => outputError "Failed to parse proof tree"
    | .singleTactic =>
      let hoverPos := fileMap.lspPosToUtf8Pos ⟨line, col⟩
      let some goalsAt := (staticGoalsAt? tree fileMap hoverPos).head?
        | outputError "No tactic at position"
      let info := Info.ofTacticInfo goalsAt.tacticInfo
      let result ← runInCoreM ctx lastEnv (staticParseSingleTactic tree goalsAt.ctxInfo info)
      outputJson result

unsafe def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error msg => IO.eprintln msg
  | .ok config => processFile config
