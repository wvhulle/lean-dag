import Tests.SemanticTableau
import Tests.ProofStateChanges
import Tests.LspIntegration
import Tests.SemanticTableauRpc
import Tests.LspEdgeCases

unsafe def main : IO Unit := do
  IO.println "LeanAnalyzer Feature Tests"
  Tests.SemanticTableau.runTests
  Tests.ProofStateChanges.runTests
  Tests.LspIntegration.runTests
  Tests.SemanticTableauRpc.runTests
  Tests.LspEdgeCases.runTests
  IO.println "\nAll tests passed"
