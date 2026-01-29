import Tests.UnitProofDag
import Tests.UnitProofState
import Tests.RpcBasic
import Tests.RpcProofDag
import Tests.RpcEdgeCases

unsafe def main : IO Unit := do
  IO.println "LeanAnalyzer Tests"

  -- Unit tests (no external dependencies)
  Tests.UnitProofDag.runTests
  Tests.UnitProofState.runTests

  -- RPC integration tests (require lean-analyzer binary)
  Tests.RpcBasic.runTests
  Tests.RpcProofDag.runTests
  Tests.RpcEdgeCases.runTests

  IO.println "\nAll tests passed"
