import LeanAnalyzer.LspServer
import Std.Internal.UV.System
import Lean.Util.Path

/-!
# LeanAnalyzer LSP Server

A drop-in replacement for `lean --server` that includes the `LeanAnalyzer.getProofDag` RPC method.

Usage:
  lean-analyzer [args...]

The server accepts the same arguments as `lean --server`.
When spawned with --worker, runs as a file worker process.
-/

def loadLakeEnvironment : IO Unit := do
  let leanPath ← IO.getEnv "LEAN_PATH"
  let leanSysroot ← IO.getEnv "LEAN_SYSROOT"
  if leanPath.isSome && leanSysroot.isSome then return
  let result ← IO.Process.output { cmd := "lake", args := #["env", "printenv"] }
  if result.exitCode != 0 then return
  for line in result.stdout.splitOn "\n" do
    match line.splitOn "=" with
    | key :: rest =>
      let value := "=".intercalate rest
      if key.startsWith "LEAN" || key == "PATH" || key == "LD_LIBRARY_PATH" then
        Std.Internal.UV.System.osSetenv key value
    | _ => pure ()

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
  loadLakeEnvironment
  initializeSearchPath
  match args with
  | "--worker" :: _ => LeanAnalyzer.workerMain
  | _ => LeanAnalyzer.watchdogMain args
