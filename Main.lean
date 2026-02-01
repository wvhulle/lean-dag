import LeanDag.LspServer
import LeanDag.Environment
import LeanDag.TuiServer.TcpServer

open LeanDag.TuiServer

/-- Default TCP port for TUI server. -/
def defaultTcpPort : UInt16 := 9742

/-- Check if --no-tcp flag is present. -/
def hasFlagNoTcp (args : List String) : Bool :=
  args.any (· == "--no-tcp")

/-- Parse --tcp-port=PORT from command line args or LEAN_DAG_TCP_PORT env var.
    Returns the default port if not specified. -/
def parseTcpPort (args : List String) : IO UInt16 := do
  -- Check command line args first
  for arg in args do
    if arg.startsWith "--tcp-port=" then
      let portStr := arg.drop 11
      if let some n := portStr.toNat? then
        if n > 0 && n < 65536 then
          return n.toUInt16
  -- Check environment variable
  if let some portStr ← IO.getEnv "LEAN_DAG_TCP_PORT" then
    if let some n := portStr.toNat? then
      if n > 0 && n < 65536 then
        return n.toUInt16
  -- Return default
  return defaultTcpPort

/-- Filter out TCP-related args to pass clean args to watchdog/worker. -/
def filterTcpArgs (args : List String) : List String :=
  args.filter (fun arg => !arg.startsWith "--tcp-port=" && arg != "--no-tcp")

def main (args : List String) : IO UInt32 := do
  IO.eprintln s!"[LeanDag] Starting with args: {args}"
  IO.eprintln s!"[LeanDag] Current directory: {← IO.currentDir}"
  LeanDag.Environment.initEnvironment

  let cleanArgs := filterTcpArgs args
  match cleanArgs with
  | "--worker" :: rest =>
    -- Worker mode: for internal use by watchdog (no TCP server)
    IO.eprintln "[LeanDag] Starting as worker"
    LeanDag.workerMain
  | _ =>
    -- Watchdog mode: LSP server that editors connect to
    -- Start TCP server for TUI clients (unless --no-tcp is specified)
    unless hasFlagNoTcp args do
      let port ← parseTcpPort args
      IO.eprintln s!"[LeanDag] Starting TCP server on port {port}"
      let srv ← TcpServer.create port .standalone
      srv.start
      LeanDag.setTuiServer srv
    IO.eprintln "[LeanDag] Starting as watchdog (LSP server)"
    LeanDag.watchdogMain cleanArgs
