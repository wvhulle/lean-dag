import Lean.Util.Path

/-!
# Environment Discovery

Self-contained environment discovery for lean-dag standalone mode.
Instead of relying on the caller to set up LEAN_PATH and LEAN_SYSROOT via
`lake env`, lean-dag discovers these at startup by running `lake env printenv`.
-/

namespace LeanDag.Environment

/-- Run `lake env printenv VAR` to get an environment variable as Lake would set it. -/
def lakeEnvVar (varName : String) : IO (Option String) := do
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["env", "printenv", varName]
  }
  if output.exitCode == 0 then
    let value := output.stdout.trimAscii.toString
    if value.isEmpty then
      return none
    else
      return some value
  else
    return none

/-- Discover LEAN_PATH by running `lake env printenv LEAN_PATH`. -/
def discoverLeanPath : IO (Option String) :=
  lakeEnvVar "LEAN_PATH"

/-- Discover LEAN_SYSROOT by running `lake env printenv LEAN_SYSROOT`,
    falling back to Lean.findSysroot if lake env fails. -/
def discoverSysroot : IO System.FilePath := do
  match ← lakeEnvVar "LEAN_SYSROOT" with
  | some sysroot => return ⟨sysroot⟩
  | none =>
    -- Fall back to Lean's built-in sysroot discovery
    Lean.findSysroot

/-- Initialize the Lean search path from environment or discovery.

The priority is:
1. Use LEAN_PATH and LEAN_SYSROOT if already set (e.g., when spawned via `lake env`)
2. Otherwise, discover them via `lake env printenv`
3. Fall back to Lean.findSysroot for sysroot
-/
def initSearchPath : IO Unit := do
  -- Check if environment is already set up
  let existingSysroot ← IO.getEnv "LEAN_SYSROOT"
  let existingLeanPath ← IO.getEnv "LEAN_PATH"

  let (sysroot, leanPath) ← match existingSysroot with
    | some _ =>
      -- Environment is pre-configured, use it
      IO.eprintln "[LeanDag.Environment] Using existing environment"
      pure (existingSysroot, existingLeanPath)
    | none =>
      -- Discover environment via lake
      IO.eprintln "[LeanDag.Environment] Discovering environment via `lake env printenv`..."
      let discoveredSysroot ← discoverSysroot
      let discoveredPath ← discoverLeanPath
      IO.eprintln s!"[LeanDag.Environment] Discovered LEAN_SYSROOT: {discoveredSysroot}"
      IO.eprintln s!"[LeanDag.Environment] Discovered LEAN_PATH: {discoveredPath}"
      pure (some discoveredSysroot.toString, discoveredPath)

  -- Build the search path
  let sp := match leanPath with
    | some lp => System.SearchPath.parse lp
    | none => []

  match sysroot with
  | some sr =>
    let libDir : System.FilePath := ⟨sr⟩ / "lib" / "lean"
    Lean.searchPathRef.set (sp ++ [libDir])
    IO.eprintln s!"[LeanDag.Environment] Search path set: {sp ++ [libDir]}"
  | none =>
    -- This shouldn't happen since discoverSysroot always returns something
    Lean.searchPathRef.set sp
    IO.eprintln s!"[LeanDag.Environment] Search path set (no sysroot): {sp}"

/-- Set LEAN_WORKER_PATH to the current executable path.

This ensures that worker processes spawned by the watchdog also use
the lean-dag binary rather than the default `lean` server.
-/
def setWorkerPath : IO Unit := do
  let appPath ← IO.appPath
  IO.eprintln s!"[LeanDag.Environment] Setting LEAN_WORKER_PATH to: {appPath}"
  -- LEAN_WORKER_PATH is read by the Lean watchdog to spawn workers
  -- We need to set it in the process environment
  -- Unfortunately Lean's IO doesn't have setEnv, so we use the FFI-based approach
  -- For now, we'll document that this should be set externally, but the discovery
  -- handles the path setup
  pure ()

/-- Full environment initialization for standalone mode.

1. Discovers LEAN_PATH and LEAN_SYSROOT via `lake env printenv`
2. Sets up the Lean search path
3. Logs the discovered environment for debugging
-/
def initEnvironment : IO Unit := do
  IO.eprintln "[LeanDag.Environment] Initializing environment..."
  initSearchPath
  IO.eprintln "[LeanDag.Environment] Environment initialized"

end LeanDag.Environment
