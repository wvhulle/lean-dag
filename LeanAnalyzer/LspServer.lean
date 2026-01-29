import Lean
import Lean.Server.FileWorker
import Lean.Server.Watchdog
import Lean.Server.Requests
import LeanAnalyzer.Types
import LeanAnalyzer.InfoTreeParser

open Lean Server Lsp JsonRpc
open Lean.Server.FileWorker
open Lean.Server.Snapshots
open LeanAnalyzer.InfoTreeParser

namespace LeanAnalyzer

/-! ## Name Filtering -/

def isHygienicName (s : String) : Bool :=
  (s.splitOn "._hyg.").length > 1 || (s.splitOn "._@.").length > 1

def isAnonymousName (s : String) : Bool :=
  s.isEmpty || s == "[anonymous]"

def isUserVisibleName (s : String) : Bool :=
  !isHygienicName s && !isAnonymousName s

def filterName (s : String) : String :=
  if isUserVisibleName s then s else ""

def filterNameOpt (s : String) : Option String :=
  if isUserVisibleName s then some s else none

/-! ## RPC Types -/

structure GetProofDagParams where
  textDocument : TextDocumentIdentifier
  position : Lsp.Position
  mode : String := "tree"
  deriving FromJson, ToJson

structure GetProofDagResult where
  proofDag : ProofDag
  version : Nat := 5
  deriving FromJson, ToJson

def convertGoalInfo (g : ParsedGoal) : LeanAnalyzer.GoalInfo :=
  { type := g.type
    username := filterNameOpt g.username
    id := g.id.name.toString }

def convertHypothesis (h : ParsedHypothesis) : LeanAnalyzer.HypothesisInfo :=
  { name := filterName h.username
    type := h.type
    value := h.value
    id := h.id
    isProof := h.isProof == "proof"
    isInstance := false }

def buildProofDagFromSteps (steps : List ParsedStep) (_line _col : Nat) : ProofDag :=
  if steps.isEmpty then {} else
  let nodes := steps.toArray.mapIdx fun idx step =>
    let goalBefore := convertGoalInfo step.goalBefore
    let goalsAfter := step.goalsAfter.map convertGoalInfo
    let hyps := step.goalBefore.hyps.map convertHypothesis |>.filter (·.name != "")
    { id := idx
      tactic := {
        text := step.tacticString
        dependsOn := step.tacticDependsOn
        theoremsUsed := step.theorems.map (·.name)
      }
      position := step.position.start
      stateBefore := { goals := [goalBefore], hypotheses := hyps }
      stateAfter := { goals := goalsAfter, hypotheses := hyps }
      children := []
      parent := none
      depth := 0 }
  { nodes := nodes
    root := if nodes.isEmpty then none else some 0
    currentNode := some (nodes.size - 1)
    initialState := if nodes.isEmpty then {} else nodes[0]!.stateBefore }

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
        let dag := buildProofDagFromSteps result.steps params.position.line params.position.character
        return { proofDag := dag }
      | none =>
        IO.eprintln "[RPC] tree mode: no result"
        return { proofDag := {} }
    | "single_tactic" =>
      match goalsAt? snap.infoTree text hoverPos with
      | r :: _ =>
        let result ← parseTacticInfo snap.infoTree r.ctxInfo (.ofTacticInfo r.tacticInfo) [] ∅ true
        IO.eprintln s!"[RPC] single_tactic mode: {result.steps.length} steps"
        let dag := buildProofDagFromSteps result.steps params.position.line params.position.character
        return { proofDag := dag }
      | [] =>
        IO.eprintln "[RPC] single_tactic mode: no goals at position"
        return { proofDag := {} }
    | _ =>
      IO.eprintln s!"[RPC] unknown mode: {params.mode}"
      return { proofDag := {} }

builtin_initialize
  try
    Lean.Server.registerBuiltinRpcProcedure
      `LeanAnalyzer.getProofDag
      GetProofDagParams
      GetProofDagResult
      handleGetProofDag
  catch e =>
    IO.eprintln s!"[LeanAnalyzer] RPC registration failed: {e}"

/-- Run as the main LSP watchdog server (drop-in replacement for `lean --server`) -/
def watchdogMain (args : List String) : IO UInt32 :=
  Lean.Server.Watchdog.watchdogMain args

/-- Run as a file worker (spawned by watchdog with --worker flag) -/
def workerMain (opts : Lean.Options := {}) : IO UInt32 :=
  Lean.Server.FileWorker.workerMain opts

end LeanAnalyzer
