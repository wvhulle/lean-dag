import Tests.SemanticTableau
import Tests.ProofStateChanges
import Tests.TacticSplitting
import Tests.LspIntegration
import Tests.SemanticTableauRpc

unsafe def main : IO Unit := do
  IO.println "LeanAnalyzer Feature Tests"
  Tests.SemanticTableau.runTests
  Tests.ProofStateChanges.runTests
  Tests.TacticSplitting.runTests
  Tests.LspIntegration.runTests
  Tests.SemanticTableauRpc.runTests
  IO.println "\nAll tests passed"
