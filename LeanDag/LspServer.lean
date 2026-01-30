import Lean
import Lean.Server.FileWorker
import Lean.Server.Watchdog
import Lean.Server.Requests
import LeanDag.Types
import LeanDag.InfoTreeParser

open Lean Server Lsp JsonRpc
open Lean.Server.FileWorker Lean.Server.Snapshots
open LeanDag.InfoTreeParser

namespace LeanDag

/-! ## Name Filtering -/

def containsSubstr (s pattern : String) : Bool :=
  (s.splitOn pattern).length > 1

def isHygienicName (s : String) : Bool :=
  containsSubstr s "._hyg." || containsSubstr s "._@."

def isUserVisibleName (s : String) : Bool :=
  !s.isEmpty && s != "[anonymous]" && !isHygienicName s

def filterName (s : String) : String :=
  if isUserVisibleName s then s else ""

def filterNameOpt (s : String) : Option String :=
  if isUserVisibleName s then some s else none

/-! ## RPC Types -/

structure GetProofDagParams where
  textDocument : TextDocumentIdentifier
  position     : Lsp.Position
  mode         : String := "tree"
  deriving FromJson, ToJson

structure GetProofDagResult where
  proofDag : ProofDag
  version  : Nat := 5
  deriving FromJson, ToJson

/-! ## Conversion -/

def convertGoalInfo (g : ParsedGoal) : GoalInfo where
  type := g.type
  username := filterNameOpt g.username
  id := g.id.name.toString

def convertHypothesis (h : ParsedHypothesis) : HypothesisInfo where
  name := filterName h.username
  type := h.type
  value := h.value
  id := h.id
  isProof := h.isProof == "proof"
  isInstance := false

def buildProofDag (steps : List ParsedStep) : ProofDag :=
  if steps.isEmpty then {} else
  let stepsArray := steps.toArray
  -- Build goal ID to step index map: which step produces which goals
  -- goalsAfter are the goals that result from applying the tactic
  let goalToProducer : Std.HashMap String Nat := Id.run do
    let mut m : Std.HashMap String Nat := {}
    for h : idx in [:stepsArray.size] do
      let step := stepsArray[idx]
      for goal in step.goalsAfter do
        m := m.insert goal.id.name.toString idx
    return m
  -- For each step, find parent (the step whose goalsAfter contains this step's goalBefore)
  let parentOf : Array (Option Nat) := stepsArray.map fun step =>
    goalToProducer.get? step.goalBefore.id.name.toString
  -- Compute children from parent relationships
  let childrenOf : Array (List Nat) := Id.run do
    let mut result : Array (List Nat) := stepsArray.map (fun _ => [])
    for h : childIdx in [:parentOf.size] do
      if let some parentIdx := parentOf[childIdx] then
        if parentIdx < result.size then
          result := result.modify parentIdx (childIdx :: ·)
    return result
  -- Compute depth: count steps to root
  let depths : Array Nat := Id.run do
    let mut result := stepsArray.map (fun _ => 0)
    for h : idx in [:stepsArray.size] do
      let mut depth := 0
      let mut current := idx
      let mut visited : Std.HashSet Nat := {}
      while true do
        if visited.contains current then break
        visited := visited.insert current
        match parentOf[current]? with
        | some (some p) =>
          depth := depth + 1
          current := p
        | _ => break
      result := result.set! idx depth
    return result
  -- Build nodes with computed relationships
  let nodes := stepsArray.mapIdx fun idx step =>
    let goalBefore := convertGoalInfo step.goalBefore
    let goalsAfter := step.goalsAfter.map convertGoalInfo
    let hyps := step.goalBefore.hyps.map convertHypothesis |>.filter (·.name != "")
    { id := idx
      tactic := { text := step.tacticString, dependsOn := step.tacticDependsOn, theoremsUsed := step.theorems.map (·.name) }
      position := step.position.start
      stateBefore := { goals := [goalBefore], hypotheses := hyps }
      stateAfter := { goals := goalsAfter, hypotheses := hyps }
      children := childrenOf[idx]?.getD []
      parent := parentOf[idx]?.join
      depth := depths[idx]?.getD 0 }
  -- Find all nodes with no parent (potential roots/orphans)
  let rootCandidates := nodes.toList.filterMap fun n =>
    if n.parent.isNone then some n.id else none
  -- First rootless node is the main root, rest are orphans (disconnected components)
  let (root, orphans) := match rootCandidates with
    | [] => (none, [])
    | r :: rest => (some r, rest)
  { nodes, root, orphans, currentNode := some (nodes.size - 1), initialState := nodes[0]!.stateBefore }

/-! ## RPC Handler -/

def handleGetProofDag (params : GetProofDagParams) : RequestM (RequestTask GetProofDagResult) := do
  let doc ← RequestM.readDoc
  let utf8Pos := doc.meta.text.lspPosToUtf8Pos params.position
  IO.eprintln s!"[RPC] getProofDag mode={params.mode} pos={params.position} utf8={utf8Pos} uri={doc.meta.uri}"
  RequestM.withWaitFindSnapAtPos params.position fun snap => do
    IO.eprintln s!"[RPC] snapshot found endPos={snap.endPos}"
    let text := doc.meta.text
    let hoverPos := text.lspPosToUtf8Pos params.position
    match params.mode with
    | "tree" =>
      match ← parseInfoTree snap.infoTree with
      | some result =>
        IO.eprintln s!"[RPC] tree mode: {result.steps.length} steps"
        return { proofDag := buildProofDag result.steps }
      | none =>
        IO.eprintln "[RPC] tree mode: no result"
        return { proofDag := {} }
    | "single_tactic" =>
      match goalsAt? snap.infoTree text hoverPos with
      | r :: _ =>
        let result ← parseTacticInfo snap.infoTree r.ctxInfo (.ofTacticInfo r.tacticInfo) [] ∅ true
        IO.eprintln s!"[RPC] single_tactic mode: {result.steps.length} steps"
        return { proofDag := buildProofDag result.steps }
      | [] =>
        IO.eprintln "[RPC] single_tactic mode: no goals at position"
        return { proofDag := {} }
    | _ =>
      IO.eprintln s!"[RPC] unknown mode: {params.mode}"
      return { proofDag := {} }

builtin_initialize
  try
    Lean.Server.registerBuiltinRpcProcedure `LeanDag.getProofDag GetProofDagParams GetProofDagResult handleGetProofDag
  catch e =>
    IO.eprintln s!"[LeanDag] RPC registration failed: {e}"

def watchdogMain (args : List String) : IO UInt32 :=
  Lean.Server.Watchdog.watchdogMain args

def workerMain (opts : Lean.Options := {}) : IO UInt32 :=
  Lean.Server.FileWorker.workerMain opts

end LeanDag
