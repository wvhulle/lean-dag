/-
  # Terminal Output
  Paperproof supports static extraction of its proof structures to JSON files via terminal execution.
  This feature is useful for data processing in AI applications and for the VS Code extension fallback.

  ## Usage Modes

  ### By Constant Name (original mode)
  ```shell
  lake exe paperproof-cli --by-name LEAN_FILE_PATH CONSTANT_NAME OUTPUT_PATH
  ```
  Saves the proof structure of a theorem to a JSON file.

  ### By Position (new mode for VS Code extension)
  ```shell
  lake exe paperproof-cli --by-position LEAN_FILE_PATH LINE COLUMN MODE
  ```
  Outputs JSON to stdout. LINE and COLUMN are 0-indexed. MODE is 'tree' or 'single_tactic'.

  ## Setup
  In your `lakefile.lean`, add:
    ```lean
    require Paperproof from git "https://github.com/Paper-Proof/paperproof" @ "main" / "lean"
    ```

  Then run `lake exe paperproof-cli`.
-/
import Lean
import Services.BetterParser
import Services.GetTheorems

open Lean Elab Paperproof.Services

def dummyPosition : ProofStepPosition := {
  start := { line := 0, character := 0 },
  stop := { line := 0, character := 0 }
}

-- Add ToJson instance for Result (original doesn't have one)
instance : ToJson Result where
  toJson r := Json.mkObj [
    ("steps", toJson r.steps),
    ("allGoals", toJson (r.allGoals.toList))
  ]

-- Static version of printGoalInfo for MetaM (not RequestM)
def static_printGoalInfo (printCtx : ContextInfo) (id : MVarId) : MetaM GoalInfo := do
  let some decl := printCtx.mctx.findDecl? id
    | throwError "Goal not found in mctx"
  let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
  let ppContext := printCtx.toPPContext lctx
  let hyps ← lctx.foldrM (init := []) (fun hypDecl acc => do
    if hypDecl.isAuxDecl || hypDecl.isImplementationDetail then
      return acc
    let type ← ppExprWithInfos ppContext hypDecl.type
    let value ← hypDecl.value?.mapM (fun expr => ppExprWithInfos ppContext expr)
    let isProof : String ← printCtx.runMetaM decl.lctx (mayBeProof hypDecl.toExpr)
    return ({
      username := hypDecl.userName.toString,
      type     := type.fmt.pretty,
      value    := value.map (fun x => x.fmt.pretty),
      id       := hypDecl.fvarId.name.toString,
      isProof  := isProof
    } : Hypothesis) :: acc)
  return {
    username := decl.userName.toString
    type     := (← ppExprWithInfos ppContext decl.type).fmt.pretty
    hyps     := hyps
    id       := id
  }

-- Static version of getUnassignedGoals for MetaM
def static_getUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : MetaM (List MVarId) := do
  goals.filterMapM fun id => do
    if let none := mctx.findDecl? id then
      return none
    if mctx.eAssignment.contains id || mctx.dAssignment.contains id then
      return none
    return some id

-- Static version of getGoalsChange for MetaM
def static_getGoalsChange (ctx : ContextInfo) (tInfo : TacticInfo) : MetaM (List (List String × GoalInfo × List GoalInfo)) := do
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  let printCtx := {ctx with mctx := tInfo.mctxAfter}
  let mut goalsBefore ← static_getUnassignedGoals goalMVars tInfo.mctxBefore
  let mut goalsAfter ← static_getUnassignedGoals goalMVars tInfo.mctxAfter
  let commonGoals := goalsBefore.filter fun g => goalsAfter.contains g
  goalsBefore := goalsBefore.filter (!commonGoals.contains ·)
  goalsAfter := goalsAfter.filter (!commonGoals.contains ·)

  let mut result : List (List String × GoalInfo × List GoalInfo) := []
  for goalBefore in goalsBefore do
    if let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore then
      let assignedMVars ← ctx.runMetaM goalDecl.lctx (findMVarsAssigned goalBefore tInfo.mctxAfter)
      let tacticDependsOn ← ctx.runMetaM goalDecl.lctx (findHypsUsedByTactic goalBefore goalDecl tInfo.mctxAfter)

      result := (
        tacticDependsOn,
        ← static_printGoalInfo printCtx goalBefore,
        ← goalsAfter.filter assignedMVars.contains |>.mapM (static_printGoalInfo printCtx)
      ) :: result
  return result

-- Static version of parseTacticInfo using original ProofStep structure
partial def static_parseTacticInfo (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (steps : List ProofStep) (allGoals : Std.HashSet GoalInfo) : MetaM Result := do
  let .some ctx := info.updateContext? ctx | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info          | return { steps, allGoals }
  let .some tacticSubstring := getTacticSubstring tInfo | return { steps, allGoals }

  let tacticString := prettifyTacticString tacticSubstring.toString
  let steps := prettifySteps tInfo.stx steps

  let proofTreeEdges ← static_getGoalsChange ctx tInfo
  let currentGoals := proofTreeEdges.map (fun ⟨ _, g₁, gs ⟩ => g₁ :: gs)  |>.flatten
  let allGoals := allGoals.insertMany $ currentGoals

  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals steps)
    |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList

  let theorems ←
    match ctx.mctx.findDecl? tInfo.goalsBefore.head!, getTacticSubstring tInfo with
    | some goalDecl, some tacticSubstring =>
      ctx.runMetaM goalDecl.lctx do
        findTheoremsLikeHover infoTree tacticSubstring.startPos tacticSubstring.stopPos ctx goalDecl
    | _, _ => pure []
  let newSteps := proofTreeEdges.filterMap fun ⟨ tacticDependsOn, goalBefore, goalsAfter ⟩ =>
    if steps.map (·.goalBefore) |>.elem goalBefore then
      none
    else
      some {
        tacticString,
        goalBefore,
        goalsAfter,
        tacticDependsOn,
        spawnedGoals := orphanedGoals,
        position := dummyPosition,
        theorems := theorems
      }

  return { steps := newSteps ++ steps, allGoals }

partial def static_postNode (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) (results : List (Option Result)) : MetaM Result := do
  let results : List Result := results.filterMap id
  let steps : List ProofStep := (results.map (λ result => result.steps)).flatten
  let allGoals : Std.HashSet GoalInfo := Std.HashSet.ofList ((results.map (λ result => result.allGoals.toList)).flatten)

  static_parseTacticInfo infoTree ctx info steps allGoals

partial def static_BetterParser (infoTree : InfoTree) := infoTree.visitM (postNode :=
  λ ctx info _ results => static_postNode infoTree ctx info results
)

------------------------------------------------------------------
-- Config and argument parsing

inductive LookupMode where
  | byName (const_name : Lean.Name) (output_path : System.FilePath)
  | byPosition (line : Nat) (column : Nat) (tactic_mode : String)

structure Config where
  file_path : System.FilePath := "."
  lookup_mode : LookupMode := .byName `Unknown "."

def parseArgs (args : Array String) : IO Config := do
  if args.size < 2 then
    throw <| IO.userError "usage: lake exe paperproof-cli [--by-name FILE_PATH CONST_NAME OUTPUT_PATH | --by-position FILE_PATH LINE COLUMN MODE]"
  let mode_flag := args[0]!
  match mode_flag with
  | "--by-name" =>
    if args.size < 4 then
      throw <| IO.userError "usage: lake exe paperproof-cli --by-name FILE_PATH CONST_NAME OUTPUT_PATH"
    let file_path : System.FilePath := ⟨args[1]!⟩
    let const_name := args[2]!.toName
    let output_path : System.FilePath := ⟨args[3]!⟩
    IO.eprintln s!"File: {file_path}"
    IO.eprintln s!"Constant: {const_name}"
    IO.eprintln s!"Output: {output_path}"
    return { file_path, lookup_mode := .byName const_name output_path }
  | "--by-position" =>
    if args.size < 5 then
      throw <| IO.userError "usage: lake exe paperproof-cli --by-position FILE_PATH LINE COLUMN MODE"
    let file_path : System.FilePath := ⟨args[1]!⟩
    let some line := args[2]!.toNat?
      | throw <| IO.userError s!"Invalid line number: {args[2]!}"
    let some column := args[3]!.toNat?
      | throw <| IO.userError s!"Invalid column number: {args[3]!}"
    let tactic_mode := args[4]!
    if tactic_mode != "tree" && tactic_mode != "single_tactic" then
      throw <| IO.userError s!"Invalid mode: {tactic_mode}. Expected 'tree' or 'single_tactic'"
    IO.eprintln s!"File: {file_path}"
    IO.eprintln s!"Position: line {line}, column {column}"
    IO.eprintln s!"Mode: {tactic_mode}"
    return { file_path, lookup_mode := .byPosition line column tactic_mode }
  | _ =>
    -- Backward compatibility: if no flag, assume old format
    if args.size < 3 then
      throw <| IO.userError "usage: lake exe paperproof-cli FILE_PATH CONST_NAME OUTPUT_PATH (or use --by-name/--by-position flags)"
    let file_path : System.FilePath := ⟨args[0]!⟩
    let const_name := args[1]!.toName
    let output_path : System.FilePath := ⟨args[2]!⟩
    IO.eprintln s!"File: {file_path}"
    IO.eprintln s!"Constant: {const_name}"
    IO.eprintln s!"Output: {output_path}"
    return { file_path, lookup_mode := .byName const_name output_path }

unsafe def processCommands : Frontend.FrontendM (List (Lean.Environment × InfoState)) := do
  let done ← Lean.Elab.Frontend.processCommand
  let st := ← get
  let infoState := st.commandState.infoState
  let env' := st.commandState.env

  -- clear the infostate
  set {st with commandState := {st.commandState with infoState := {}}}
  if done
  then return [(env', infoState)]
  else
    return (env', infoState) :: (←processCommands)

------------------------------------------------------------------
-- Position-based lookup helpers

/-- Check if a position is within a given range -/
def positionInRange (pos : String.Pos.Raw) (startPos endPos : String.Pos.Raw) : Bool :=
  startPos <= pos && pos < endPos

/-- Find InfoTree containing tactics at the given position -/
def findInfoTreeAtPosition (trees : Array InfoTree) (text : FileMap) (line column : Nat) : Option InfoTree := Id.run do
  let pos := text.lspPosToUtf8Pos ⟨line, column⟩
  for tree in trees do
    let found := tree.collectNodesBottomUp fun _ctx info _ acc => Id.run do
      if let Info.ofTacticInfo _ := info then
        if let (some startPos, some endPos) := (info.pos?, info.tailPos?) then
          if positionInRange pos startPos endPos then
            return true :: acc
      return acc
    if found.any id then
      return some tree
  return none

------------------------------------------------------------------
-- Static version of goalsAt for single_tactic mode (no RequestM)

structure StaticGoalsAtResult where
  ctxInfo : ContextInfo
  tacticInfo : TacticInfo

-- Intermediate structure used during goalsAt? traversal
private structure GoalsAtInternal where
  ctxInfo : ContextInfo
  tacticInfo : TacticInfo
  useAfter : Bool
  indented : Bool
  priority : Nat

/-- Static version of goalsAt? that works in MetaM -/
partial def static_goalsAt? (t : InfoTree) (text : FileMap) (hoverPos : String.Pos.Raw) : List StaticGoalsAtResult :=
  let gs := t.collectNodesBottomUp fun ctx i cs gs => Id.run do
    if let Info.ofTacticInfo ti := i then
      if let (some pos, some tailPos) := (i.pos?, i.tailPos?) then
        let trailSize := i.stx.getTrailingSize
        let atEOF := tailPos.byteIdx + trailSize == text.source.rawEndPos.byteIdx
        if pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + max 1 trailSize || atEOF) then
          let isClosingBracketInRewriteSequence := ti.stx.getAtomVal == "]"
          if (gs.isEmpty || (hoverPos ≥ tailPos && gs.all (·.indented))) && !isClosingBracketInRewriteSequence then
            return [({
              ctxInfo := ctx
              tacticInfo := ti
              useAfter := hoverPos > pos && !cs.any (hasNestedTactic pos tailPos)
              indented := (text.toPosition pos).column > (text.toPosition hoverPos).column && !isEmptyBy ti.stx
              priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1
            } : GoalsAtInternal)]
    return gs
  let maxPrio? := gs.map (·.priority) |>.max?
  gs.filter (some ·.priority == maxPrio?) |>.map fun r => { ctxInfo := r.ctxInfo, tacticInfo := r.tacticInfo }
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

/-- Static version of parseTacticInfo for single tactic mode -/
partial def static_parseSingleTactic (infoTree: InfoTree) (ctx : ContextInfo) (info : Info) : MetaM Result := do
  let .ofTacticInfo tInfo := info | return { steps := [], allGoals := ∅ }
  let .some tacticSubstring := getTacticSubstring tInfo | return { steps := [], allGoals := ∅ }
  let tacticString := prettifyTacticString tacticSubstring.toString
  let proofTreeEdges ← static_getGoalsChange ctx tInfo
  let currentGoals := proofTreeEdges.map (fun ⟨ _, g₁, gs ⟩ => g₁ :: gs)  |>.flatten
  let allGoals : Std.HashSet GoalInfo := Std.HashSet.ofList currentGoals
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals [])
    |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList
  let theorems ←
    match ctx.mctx.findDecl? tInfo.goalsBefore.head!, getTacticSubstring tInfo with
    | some goalDecl, some tacticSubstring =>
      ctx.runMetaM goalDecl.lctx do
        findTheoremsLikeHover infoTree tacticSubstring.startPos tacticSubstring.stopPos ctx goalDecl
    | _, _ => pure []
  let newSteps := proofTreeEdges.filterMap fun ⟨ tacticDependsOn, goalBefore, goalsAfter ⟩ =>
    some {
      tacticString,
      goalBefore,
      goalsAfter,
      tacticDependsOn,
      spawnedGoals := orphanedGoals,
      position := dummyPosition,
      theorems := theorems
    }
  return { steps := newSteps, allGoals }

------------------------------------------------------------------
-- Output functions

def writeGoalInfo (goal : Paperproof.Services.GoalInfo) : IO Unit := do
  IO.println s!"Goal: {goal.type}"
  if goal.hyps.isEmpty then
    IO.println "\nNo hypotheses"
  else
    IO.println "\nHypotheses:"
    for hyp in goal.hyps do
      IO.println s!"{hyp.username}:{hyp.type}"
  IO.println "---"

def writeProofStep (step : ProofStep) (stepNumber : Nat) : IO Unit := do
  IO.println s!"\n=== Step {stepNumber} ==="
  IO.println s!"Tactic: {step.tacticString}"
  IO.println s!"\nGoals Before:{step.goalBefore.type}"
  if step.goalsAfter.isEmpty then
    IO.println "\nGoals After: No goals (proof completed)"
  else
    IO.println s!"\nGoals After: {step.goalsAfter.length} goal(s)"
    for (goal, i) in step.goalsAfter.zipIdx do
      IO.println s!"Goal {i + 1}:"
      writeGoalInfo goal
  if !step.spawnedGoals.isEmpty then
    IO.println s!"Spawned goals: {step.spawnedGoals.length}"
    for (goal, i) in step.spawnedGoals.zipIdx do
      IO.println s!"Spawned goal {i + 1}:"
      writeGoalInfo goal

def saveResultToFile (r : Result) (filePath : System.FilePath) : IO Unit := do
  let json := toJson r
  let jsonStr := Json.pretty json
  IO.FS.writeFile filePath jsonStr

def printresult (r : Result)(filePath : System.FilePath) : IO Unit := do
  IO.println "Proof Tree:"
  IO.println "==========="

  if r.steps.isEmpty then
    IO.println "No proof steps"
    return

  let mut stepNumber := 1
  for step in r.steps do
    writeProofStep step stepNumber
    stepNumber := stepNumber + 1

  IO.println "\n=== Summary ==="
  IO.println s!"Total steps: {r.steps.length}"
  IO.println s!"Total goals in proof state: {r.allGoals.size}"

  if !r.allGoals.isEmpty then
    IO.println "\nAll unique goals encountered:"
    for goal in r.allGoals.toList do
      IO.println s!"- {goal.username} : {goal.type}"

  saveResultToFile r filePath

/-- Output result as JSON to stdout -/
def outputJsonToStdout (r : Result) (version : Nat := 4) : IO Unit := do
  let output := Json.mkObj [
    ("steps", toJson r.steps),
    ("version", toJson version)
  ]
  IO.println (Json.compress output)

/-- Output error as JSON to stdout -/
def outputErrorJson (error : String) : IO Unit := do
  let output := Json.mkObj [
    ("error", toJson error)
  ]
  IO.println (Json.compress output)

------------------------------------------------------------------
-- Main

unsafe def main (args : List String) : IO Unit := do
  IO.eprintln "running.."
  let config ← parseArgs args.toArray
  Lean.initSearchPath (← Lean.findSysroot)
  let input ← IO.FS.readFile config.file_path
  Lean.enableInitializersExecution
  let inputCtx := Lean.Parser.mkInputContext input config.file_path.toString
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let (env, messages) ← Lean.Elab.processHeader header {} messages inputCtx

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        IO.eprintln s!"ERROR: {← msg.toString}"
    match config.lookup_mode with
    | .byPosition .. => outputErrorJson "Errors during import"
    | .byName .. => throw <| IO.userError "Errors during import; aborting"
    return

  let env := env.setMainModule (← Lean.moduleNameOfFileName config.file_path none)
  let fileMap := inputCtx.fileMap
  let commandState := { Lean.Elab.Command.mkState env messages {} with infoState.enabled := true }

  let (steps, _frontendState) ← (processCommands.run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

  match config.lookup_mode with
  | .byName const_name output_path =>
    if env.contains const_name then
      throw <| IO.userError s!"constant of name {const_name} is already in environment"
    for ⟨env', s⟩ in steps do
      if env'.contains const_name then
        for tree in s.trees do
          let ctx : Lean.Core.Context := { fileName := "", fileMap := default, options := {} }
          let state : Lean.Core.State := { env := env', messages := Lean.MessageLog.empty }
          let ioComputation := ((static_BetterParser tree).run {} {}).toIO ctx state
          let ((result, _), _) ← ioComputation
          match result with
          | some r => printresult r output_path
          | none => IO.eprintln "Error: failed to parse proof tree"
        break

  | .byPosition line column tactic_mode =>
    -- Collect all info trees from all steps
    let trees : Array InfoTree := steps.foldl (fun acc ⟨_, s⟩ => acc ++ s.trees.toArray) #[]

    -- Find the info tree containing tactics at the given position
    match findInfoTreeAtPosition trees fileMap line column with
    | none =>
      outputErrorJson "No proof found at position"
    | some tree =>
      let some ⟨lastEnv, _⟩ := steps.getLast?
        | outputErrorJson "No commands processed"
          return
      let ctx : Lean.Core.Context := { fileName := config.file_path.toString, fileMap := fileMap, options := {} }
      let state : Lean.Core.State := { env := lastEnv, messages := Lean.MessageLog.empty }

      match tactic_mode with
      | "tree" =>
        let ioComputation := ((static_BetterParser tree).run {} {}).toIO ctx state
        let ((result, _), _) ← ioComputation
        match result with
        | some r =>
          if r.steps.isEmpty then
            outputErrorJson "zeroProofSteps"
          else
            outputJsonToStdout r
        | none => outputErrorJson "Failed to parse proof tree"
      | "single_tactic" =>
        let hoverPos := fileMap.lspPosToUtf8Pos ⟨line, column⟩
        match (static_goalsAt? tree fileMap hoverPos).head? with
        | none => outputErrorJson "No tactic at position"
        | some goalsAtResult =>
          let info : Info := Elab.Info.ofTacticInfo goalsAtResult.tacticInfo
          let ioComputation := ((static_parseSingleTactic tree goalsAtResult.ctxInfo info).run {} {}).toIO ctx state
          let ((result, _), _) ← ioComputation
          outputJsonToStdout result
      | _ => outputErrorJson s!"Unknown mode: {tactic_mode}"
