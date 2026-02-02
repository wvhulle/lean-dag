import Lake
open Lake DSL

package «lean-dag» where
  testDriver := "«lean-dag-tests»"

require «json-schema-to-lean» from git "https://codeberg.org/wvhulle/json-schema-to-lean" @ "main"

/-- Target that ensures lean-dag binary is built -/
target «lean-dag-bin» pkg : System.FilePath := do
  if let some exe := pkg.findLeanExe? `«lean-dag» then
    exe.exe.fetch
  else
    error "Could not find lean-dag executable"

/-- Track protocol-schema.json as a dependency for code generation -/
target «protocol-schema» pkg : System.FilePath := do
  let path := pkg.dir / "protocol-schema.json"
  inputTextFile path

lean_lib «LeanDag» where
  precompileModules := true
  extraDepTargets := #[`«protocol-schema»]

lean_lib «Tests» where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe «lean-dag» where
  root := `Main
  supportInterpreter := true

lean_exe «lean-dag-tests» where
  root := `Tests.Main
  supportInterpreter := true
  extraDepTargets := #[`«lean-dag-bin»]
