import Lake
open Lake DSL

-- TODO: this is an «examples» repo - the real «paperproof» library is in /lean subfolder.
-- We're only naming it "paperproof" here to accommodate to lean reservoir, see https://github.com/Paper-Proof/paperproof/pull/42.
-- Note that we're naming it lowercase paperproof to avoid circular dependency error.
-- In general, this should still be called «example», let's see how to deal with it when https://reservoir.lean-lang.org is more mature.
package «paperproof» {
  -- add package configuration options here
}

lean_lib «paperproof» {
  -- add library configuration options here
}

-- If you're developing locally, this imports paperproof from a local "./lean" folder
require Paperproof from "lean"

-- require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.26.0-rc2"

/-! ## Lean Analyzer - Proof DAG construction for TUI/visualization -/

lean_lib «LeanAnalyzer» where
  srcDir := "analyzer"

lean_lib «LeanAnalyzerTests» where
  srcDir := "analyzer"
  roots := #[`Tests.Helpers, `Tests.SemanticTableau, `Tests.ProofStateChanges, `Tests.TacticSplitting, `Tests.Integration, `Tests.LspClient, `Tests.LspIntegration, `Tests.SemanticTableauRpc]

lean_exe «lean-analyzer» where
  srcDir := "analyzer"
  root := `Main
  supportInterpreter := true

@[test_driver]
lean_exe «lean-analyzer-tests» where
  srcDir := "analyzer"
  root := `Tests.Main
  supportInterpreter := true
