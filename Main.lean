import LeanDag.LspServer
import LeanDag.Environment

def main (args : List String) : IO UInt32 := do
  IO.eprintln s!"[LeanDag] Starting with args: {args}"
  LeanDag.Environment.initEnvironment
  match args with
  | "--worker" :: _ =>
    IO.eprintln "[LeanDag] Starting as worker"
    LeanDag.workerMain
  | _ =>
    IO.eprintln "[LeanDag] Starting as watchdog"
    LeanDag.watchdogMain args
