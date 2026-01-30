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
  initializeSearchPath
  match args with
  | "--worker" :: _ => LeanDag.workerMain
  | _ => LeanDag.watchdogMain args
