import Tests.UnitProofDag
import Tests.UnitProofState
import Tests.UnitGotoLocation
import Tests.RpcBasic
import Tests.RpcProofDag
import Tests.RpcBoundary
import Tests.RpcTactics
import Tests.RpcUnicode

unsafe def main : IO Unit := do
  IO.println "LeanDag Tests"

  -- Unit tests (no external dependencies)
  Tests.UnitProofDag.runTests
  Tests.UnitProofState.runTests
  Tests.UnitGotoLocation.runTests

  -- RPC integration tests (require lean-dag binary)
  Tests.RpcBasic.runTests
  Tests.RpcProofDag.runTests
  Tests.RpcBoundary.runTests
  Tests.RpcTactics.runTests
  Tests.RpcUnicode.runTests

  IO.println "\nAll tests passed"
