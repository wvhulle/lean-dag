import LeanDag.LspServer
import LeanDag.Environment

def main (args : List String) : IO UInt32 := do
  IO.eprintln s!"[LeanDag] Starting with args: {args}"
  IO.eprintln s!"[LeanDag] Current directory: {← IO.currentDir}"
  LeanDag.Environment.initEnvironment
  match args with
  | "--watchdog" :: rest =>
    IO.eprintln "[LeanDag] Starting as watchdog"
    LeanDag.watchdogMain rest
  | _ =>
    -- Default: direct worker mode (single-file, no watchdog overhead)
    IO.eprintln "[LeanDag] Starting as worker (direct mode)"
    let result ← LeanDag.workerMain
    IO.eprintln s!"[LeanDag] Worker exited with: {result}"
    return result
