import Lake
open Lake DSL

package «lean-analyzer» where

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.26.0-rc2"

lean_lib «LeanAnalyzer» where

lean_lib «Tests» where
  roots := #[`Tests.Helpers, `Tests.SemanticTableau, `Tests.ProofStateChanges, `Tests.LspClient, `Tests.LspIntegration, `Tests.SemanticTableauRpc, `Tests.LspEdgeCases]

lean_exe «lean-analyzer» where
  root := `Main
  supportInterpreter := true

@[test_driver]
lean_exe «lean-analyzer-tests» where
  root := `Tests.Main
  supportInterpreter := true
