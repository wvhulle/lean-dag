import LeanDag.LspServer
import Lean.Util.Path

def initializeSearchPath : IO Unit := do
  let sysroot ← IO.getEnv "LEAN_SYSROOT"
  let leanPath ← IO.getEnv "LEAN_PATH"
  match sysroot with
  | some sr =>
    let sp := match leanPath with
      | some lp => System.SearchPath.parse lp
      | none => []
    let libDir : System.FilePath := ⟨sr⟩ / "lib" / "lean"
    Lean.searchPathRef.set (sp ++ [libDir])
  | none => pure ()

def main (args : List String) : IO UInt32 := do
  IO.eprintln s!"[LeanDag] Starting with args: {args}"
  IO.eprintln s!"[LeanDag] Current directory: {← IO.currentDir}"
  IO.eprintln s!"[LeanDag] LEAN_PATH: {← IO.getEnv "LEAN_PATH"}"
  initializeSearchPath
  match args with
  | "--worker" :: _ =>
    IO.eprintln "[LeanDag] Starting as worker"
    let result ← LeanDag.workerMain
    IO.eprintln s!"[LeanDag] Worker exited with: {result}"
    return result
  | _ =>
    IO.eprintln "[LeanDag] Starting as watchdog"
    LeanDag.watchdogMain args
