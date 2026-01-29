import Lean
import LeanAnalyzer.Types
import LeanAnalyzer.Parser
import LeanAnalyzer.ProofDag
import Services.BetterParser

open Lean Paperproof.Services

namespace LeanAnalyzer

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

structure GetProofVisualizationParams where
  file : String
  line : Nat
  column : Nat
  mode : String := "tree"
  deriving FromJson, ToJson

def errorJson (msg : String) : Json :=
  Json.mkObj [("error", toJson msg)]

def tuiResponseToJson (dag : ProofDag) (version : Nat := 5) : Json :=
  Json.mkObj [("proofDag", toJson dag), ("version", toJson version)]

def resultToJson (r : Result) (version : Nat := 4) : Json :=
  Json.mkObj [("steps", toJson r.steps), ("version", toJson version)]

def parseMode : String → Option TacticMode
  | "tree" => some .tree
  | "single_tactic" => some .singleTactic
  | _ => none

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

unsafe def queryPositionJson (pf : ProcessedFile) (line col : Nat) (mode : TacticMode) : IO Json := do
  let steps ← queryProofSteps pf line col mode
  if steps.isEmpty then return errorJson "zeroProofSteps"
  return resultToJson { steps, allGoals := ∅ }

unsafe def queryProofVisualizationJson (pf : ProcessedFile) (line col : Nat) (mode : TacticMode) : IO Json := do
  let dag ← queryProofDag pf line col mode
  return tuiResponseToJson dag

unsafe def handleRequest (method : String) (params : Json) : IO Json := do
  match method with
  | "paperproof/getSnapshotData" => match FromJson.fromJson? params with
    | .ok (p : GetSnapshotParams) => match ← loadFile ⟨p.file⟩ with
      | .ok pf => queryPositionJson pf p.line p.column (parseMode p.mode |>.getD .tree)
      | .error msg => return errorJson msg
    | .error e => return errorJson s!"Invalid params: {e}"
  | "tuiRpc/getProofVisualization" => match FromJson.fromJson? params with
    | .ok (p : GetProofVisualizationParams) => match ← loadFile ⟨p.file⟩ with
      | .ok pf => queryProofVisualizationJson pf p.line p.column (parseMode p.mode |>.getD .tree)
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

end LeanAnalyzer
