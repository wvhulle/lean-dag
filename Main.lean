import LeanDag.LspServer
import LeanDag.Environment

def main (args : List String) : IO UInt32 := do
  IO.eprintln s!"[LeanDag] Starting with args: {args}"
  IO.eprintln s!"[LeanDag] Current directory: {← IO.currentDir}"
  LeanDag.Environment.initEnvironment
  match args with
  | "--worker" :: _ =>
    IO.eprintln "[LeanDag] Starting as worker"
    let result ← LeanDag.workerMain
    IO.eprintln s!"[LeanDag] Worker exited with: {result}"
    return result
  | _ =>
    IO.eprintln "[LeanDag] Starting as watchdog"
    LeanDag.watchdogMain args
