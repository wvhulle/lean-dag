/-
  # Paperproof CLI

  Static extraction of proof structures to JSON for AI applications and VS Code extension fallback.

  ## Usage

  ### Server Mode (default)
  ```shell
  lake exe paperproof-cli
  ```
  Starts a JSON-RPC server on stdin/stdout using LSP-style Content-Length headers.

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

inductive LookupMode
  | byName (constName : Name) (outputPath : System.FilePath)
  | byPosition (line column : Nat) (mode : TacticMode)
  | serve

structure Config where
  filePath : Option System.FilePath := none
  lookupMode : LookupMode

/-! ## Argument Parsing -/

def parseMode : String → Option TacticMode
  | "tree" => some .tree
  | "single_tactic" => some .singleTactic
  | _ => none

def parseArgs : List String → Except String Config
  | [] => .ok { lookupMode := .serve }
  | ["--serve"] => .ok { lookupMode := .serve }
  | ["--by-name", file, name, output] =>
    .ok { filePath := some ⟨file⟩, lookupMode := .byName name.toName ⟨output⟩ }
  | ["--by-position", file, lineStr, colStr, modeStr] =>
    match lineStr.toNat?, colStr.toNat?, parseMode modeStr with
    | some line, some col, some mode =>
      .ok { filePath := some ⟨file⟩, lookupMode := .byPosition line col mode }
    | none, _, _ => .error s!"Invalid line: {lineStr}"
    | _, none, _ => .error s!"Invalid column: {colStr}"
    | _, _, none => .error s!"Invalid mode: {modeStr}. Use 'tree' or 'single_tactic'"
  | _ => .error "Usage: paperproof-cli [--serve | --by-name FILE NAME OUTPUT | --by-position FILE LINE COL MODE]"

/-! ## Static Proof Extraction -/

def dummyPosition : ProofStepPosition :=
  { start := { line := 0, character := 0 }, stop := { line := 0, character := 0 } }

def staticPrintGoalInfo (printCtx : ContextInfo) (id : MVarId) : MetaM GoalInfo := do
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

/-! ## Static Tactic Parsing (shared by tree and single-tactic modes) -/

def findTheoremsForTactic (infoTree : InfoTree) (ctx : ContextInfo) (tInfo : TacticInfo) : MetaM (List TheoremSignature) :=
  match ctx.mctx.findDecl? tInfo.goalsBefore.head!, getTacticSubstring tInfo with
  | some goalDecl, some sub => ctx.runMetaM goalDecl.lctx (findTheoremsLikeHover infoTree sub.startPos sub.stopPos ctx goalDecl)
  | _, _ => pure []

partial def staticParseTacticCore (infoTree : InfoTree) (ctx : ContextInfo) (tInfo : TacticInfo)
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

/-! ## Position-based Lookup -/

def findInfoTreeAtPosition (trees : Array InfoTree) (fileMap : FileMap) (line col : Nat) : Option InfoTree :=
  let pos := fileMap.lspPosToUtf8Pos ⟨line, col⟩
  trees.find? fun tree => tree.collectNodesBottomUp (fun _ info _ acc =>
    match info with
    | .ofTacticInfo _ =>
      match info.pos?, info.tailPos? with
      | some s, some e => if s <= pos && pos < e then true :: acc else acc
      | _, _ => acc
    | _ => acc) |>.any id

/-! ## Single Tactic Mode -/

private structure GoalsAtInternal where
  ctxInfo : ContextInfo
  tacticInfo : TacticInfo
  indented : Bool
  priority : Nat

partial def staticGoalsAt? (t : InfoTree) (fileMap : FileMap) (hoverPos : String.Pos.Raw) : Option (ContextInfo × TacticInfo) :=
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

/-! ## JSON Output -/

instance : ToJson Result where
  toJson r := Json.mkObj [("steps", toJson r.steps), ("allGoals", toJson r.allGoals.toList)]

def resultToJson (r : Result) (version : Nat := 4) : Json :=
  Json.mkObj [("steps", toJson r.steps), ("version", toJson version)]

def errorJson (msg : String) : Json :=
  Json.mkObj [("error", toJson msg)]

/-! ## Frontend Processing -/

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

/-- Processed file state containing everything needed for queries. -/
structure ProcessedFile where
  steps : List (Environment × InfoState)
  trees : Array InfoTree
  fileMap : FileMap
  lastEnv : Environment
  filePath : System.FilePath

/-- Load and process a Lean file, returning the processed state. -/
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

/-- Query proof data at a position from a processed file. -/
unsafe def queryPosition (pf : ProcessedFile) (line col : Nat) (mode : TacticMode) : IO Json := do
  let some tree := findInfoTreeAtPosition pf.trees pf.fileMap line col | return errorJson "No proof found at position"
  let ctx : Core.Context := { fileName := pf.filePath.toString, fileMap := pf.fileMap, options := {} }
  match mode with
  | .tree => match ← runInCoreM ctx pf.lastEnv (staticBetterParser tree) with
    | some r => return if r.steps.isEmpty then errorJson "zeroProofSteps" else resultToJson r
    | none => return errorJson "Failed to parse proof tree"
  | .singleTactic =>
    let some (ctxInfo, tacticInfo) := staticGoalsAt? tree pf.fileMap (pf.fileMap.lspPosToUtf8Pos ⟨line, col⟩)
      | return errorJson "No tactic at position"
    return resultToJson (← runInCoreM ctx pf.lastEnv (staticParseTacticCore tree ctxInfo tacticInfo []))

/-! ## One-shot CLI Mode -/

unsafe def processConstant (pf : ProcessedFile) (constName : Name) (outputPath : System.FilePath) : IO Unit := do
  for ⟨env', s⟩ in pf.steps do
    if env'.contains constName then
      for tree in s.trees do
        match ← runInCoreM { fileName := "", fileMap := default, options := {} } env' (staticBetterParser tree) with
        | some r => IO.FS.writeFile outputPath (Json.pretty (toJson r))
        | none => IO.eprintln "Failed to parse proof tree"
      return

unsafe def processFile (config : Config) : IO Unit := do
  let some filePath := config.filePath | throw <| IO.userError "File path required"
  match ← loadFile filePath with
  | .error msg => match config.lookupMode with
    | .byPosition .. => IO.println <| Json.compress (errorJson msg)
    | .byName .. => throw <| IO.userError msg
    | .serve => pure ()
  | .ok pf => match config.lookupMode with
    | .byName constName outputPath => processConstant pf constName outputPath
    | .byPosition line col mode => IO.println (Json.compress (← queryPosition pf line col mode))
    | .serve => pure ()

/-! ## JSON-RPC Server Mode -/

structure JsonRpcRequest where
  jsonrpc : String := "2.0"
  id : Nat
  method : String
  params : Json
  deriving FromJson, ToJson

structure JsonRpcResponse where
  jsonrpc : String := "2.0"
  id : Nat
  result : Json
  deriving ToJson

structure GetSnapshotParams where
  file : String
  line : Nat
  column : Nat
  mode : String := "tree"
  deriving FromJson, ToJson

partial def readContentLength (stdin : IO.FS.Stream) : IO Nat := do
  repeat
    let line ← stdin.getLine
    let trimmed := line.trim
    if trimmed.startsWith "Content-Length:" then
      let lenStr := trimmed.drop "Content-Length:".length |>.trim
      match lenStr.toNat? with
      | some n => return n
      | none => throw (IO.userError s!"Invalid Content-Length: {lenStr}")
    if trimmed.isEmpty then continue
  throw (IO.userError "No Content-Length header found")

partial def readExact (stdin : IO.FS.Stream) (n : Nat) : IO String := do
  let mut result := ""
  let mut remaining := n
  while remaining > 0 do
    let chunk ← stdin.read (remaining.toUSize)
    if chunk.isEmpty then throw (IO.userError "Unexpected EOF")
    let str := String.fromUTF8! chunk
    result := result ++ str
    remaining := remaining - str.length
  return result

def readMessage (stdin : IO.FS.Stream) : IO JsonRpcRequest := do
  let contentLength ← readContentLength stdin
  let _ ← stdin.getLine
  let content ← readExact stdin contentLength
  match Json.parse content >>= FromJson.fromJson? with
  | .ok req => return req
  | .error e => throw (IO.userError s!"Failed to parse request: {e}")

def writeResponse (stdout : IO.FS.Stream) (response : JsonRpcResponse) : IO Unit := do
  let content := Json.compress (toJson response)
  stdout.putStr s!"Content-Length: {content.utf8ByteSize}\r\n\r\n{content}"
  stdout.flush

unsafe def handleRequest (method : String) (params : Json) : IO Json := do
  match method with
  | "paperproof/getSnapshotData" => match FromJson.fromJson? params with
    | .ok (p : GetSnapshotParams) => match ← loadFile ⟨p.file⟩ with
      | .ok pf => queryPosition pf p.line p.column (parseMode p.mode |>.getD .tree)
      | .error msg => return errorJson msg
    | .error e => return errorJson s!"Invalid params: {e}"
  | "initialize" => return Json.mkObj [("capabilities", Json.mkObj [])]
  | "shutdown" => return Json.null
  | _ => return errorJson s!"Unknown method: {method}"

unsafe def runServer : IO Unit := do
  let (stdin, stdout) := (← IO.getStdin, ← IO.getStdout)
  let rec loop : IO Unit := do
    let req ← readMessage stdin
    writeResponse stdout { id := req.id, result := ← handleRequest req.method req.params }
    loop
  loop

/-! ## Main Entry Point -/

unsafe def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error msg => IO.eprintln msg
  | .ok config =>
    match config.lookupMode with
    | .serve => runServer
    | _ => processFile config
