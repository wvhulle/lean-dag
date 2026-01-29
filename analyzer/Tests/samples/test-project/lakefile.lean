import Lake
open Lake DSL

package «test-project» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib «TestProject» where
  roots := #[`Basic]
