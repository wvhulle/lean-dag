import Lake
open System Lake DSL

package Paperproof

@[default_target]
lean_lib Paperproof

lean_lib Services

/-- CLI tool for extracting proof structures. Used by VS Code extension as fallback. -/
lean_exe «paperproof-cli» where
  root := `terminal
  supportInterpreter := true
