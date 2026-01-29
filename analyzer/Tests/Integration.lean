import Lean
import Tests.LspClient
import Tests.Helpers

namespace Tests.Integration

open Lean Tests.LspClient Tests.Helpers

unsafe def runTests : IO Unit := do
  IO.println ""
  IO.println "══════════════════════════════════════════════════════════════"
  IO.println "  Integration Tests"
  IO.println "══════════════════════════════════════════════════════════════"
  
  skipTest "LSP integration tests" "requires running LSP server - use lake test or manual testing"
  
  IO.println ""
  IO.println "  Integration tests require LSP server mode."
  IO.println "  Run manually with: lake serve --lsp"
  IO.println "  Or use VS Code extension to test RPC calls."

end Tests.Integration
