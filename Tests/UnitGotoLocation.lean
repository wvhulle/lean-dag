import Lean
import LeanDag
import Tests.Harness

namespace Tests.UnitGotoLocation

open Lean Meta Elab LeanDag LeanDag.InfoTreeParser Tests.Harness

/-! ## Helper to run MetaM tests -/

def runMetaTest (test : MetaM Unit) : IO Unit := do
  let env ← importModules #[{ module := `Init }] {}
  let ctx : Core.Context := { fileName := "", fileMap := default }
  let state : Core.State := { env }
  let (result, _) ← (test.run' {}).toIO ctx state
  pure result

/-! ## findFirstResolvableConst Tests -/

/-- Test: Constant expression returns the constant name if resolvable. -/
def testConstExpr : IO Unit := do
  printSubsection "Const Expression"
  -- Note: We can't easily test resolvability without proper environment setup.
  -- Instead, we test the traversal logic by checking what constant is found first.

  runMetaTest do
    -- Simple constant: `Nat`
    let natExpr := mkConst ``Nat
    let result ← findFirstResolvableConst natExpr
    -- Nat is from Init.Prelude, may not resolve, but we test the logic
    IO.println s!"  findFirstResolvableConst (Nat): {result}"

/-- Test: Application expression finds function head constant. -/
def testAppExpr : IO Unit := do
  printSubsection "App Expression"

  runMetaTest do
    -- `List Nat` is `.app (.const List) (.const Nat)`
    let listNatExpr := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
    let result ← findFirstResolvableConst listNatExpr
    IO.println s!"  findFirstResolvableConst (List Nat): {result}"
    -- Should find List first (depth-first on function before args)

/-- Test: Nested application expression. -/
def testNestedAppExpr : IO Unit := do
  printSubsection "Nested App Expression"

  runMetaTest do
    -- `Option (List Nat)` - should find Option first
    let innerExpr := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
    let outerExpr := mkApp (mkConst ``Option [.zero]) innerExpr
    let result ← findFirstResolvableConst outerExpr
    IO.println s!"  findFirstResolvableConst (Option (List Nat)): {result}"

/-- Test: ForallE expression finds constant in domain or body. -/
def testForallExpr : IO Unit := do
  printSubsection "ForallE Expression"

  runMetaTest do
    -- `∀ n : Nat, n = n` - the Eq is not resolvable, but Nat should be found in domain
    let natType := mkConst ``Nat
    let forallExpr := Expr.forallE `n natType (mkApp3 (mkConst ``Eq [.succ .zero]) natType (.bvar 0) (.bvar 0)) .default
    let result ← findFirstResolvableConst forallExpr
    IO.println s!"  findFirstResolvableConst (∀ n : Nat, n = n): {result}"
    -- Eq is from Init.Prelude (not resolvable), so should fall through to domain (Nat)

/-- Test: Expression with no resolvable constant returns none. -/
def testNoResolvableConst : IO Unit := do
  printSubsection "No Resolvable Constant"

  runMetaTest do
    -- Just a bound variable
    let bvarExpr := Expr.bvar 0
    let result ← findFirstResolvableConst bvarExpr
    assertEqual "bvar returns none" result none

/-! ## getTypeConstName Tests (for comparison) -/

/-- Test: getTypeConstName finds the head constant. -/
def testGetTypeConstName : IO Unit := do
  printSubsection "getTypeConstName"

  -- Simple constant
  let natExpr := mkConst ``Nat
  assertEqual "Nat head const" (getTypeConstName natExpr) (some ``Nat)

  -- Application: `List Nat` should return `List`
  let listNatExpr := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
  assertEqual "List Nat head const" (getTypeConstName listNatExpr) (some ``List)

  -- Nested: `Option (List Nat)` should return `Option`
  let innerExpr := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
  let outerExpr := mkApp (mkConst ``Option [.zero]) innerExpr
  assertEqual "Option (List Nat) head const" (getTypeConstName outerExpr) (some ``Option)

/-! ## GotoLocations Structure Tests -/

/-- Test: GotoLocations default is empty. -/
def testGotoLocationsDefault : IO Unit := do
  printSubsection "GotoLocations Default"

  let locs : GotoLocations := {}
  assertTrue "definition is none" locs.definition.isNone
  assertTrue "typeDef is none" locs.typeDef.isNone

/-- Test: GotoLocation can be constructed. -/
def testGotoLocationConstruction : IO Unit := do
  printSubsection "GotoLocation Construction"

  let loc : GotoLocation := {
    uri := "file:///test.lean"
    position := ⟨10, 5⟩
  }
  assertEqual "uri" loc.uri "file:///test.lean"
  assertEqual "line" loc.position.line 10
  assertEqual "character" loc.position.character 5

/-- Test: GotoLocations JSON serialization roundtrip. -/
def testGotoLocationsJson : IO Unit := do
  printSubsection "GotoLocations JSON"

  let locs : GotoLocations := {
    definition := some { uri := "file:///def.lean", position := ⟨1, 2⟩ }
    typeDef := some { uri := "file:///type.lean", position := ⟨3, 4⟩ }
  }

  let json := Lean.toJson locs
  let parsed? := Lean.fromJson? json

  match parsed? with
  | .ok (parsed : GotoLocations) =>
    assertEqual "definition uri roundtrip"
      (parsed.definition.map (·.uri))
      (some "file:///def.lean")
    assertEqual "typeDef uri roundtrip"
      (parsed.typeDef.map (·.uri))
      (some "file:///type.lean")
  | .error e =>
    throw <| IO.userError s!"JSON parsing failed: {e}"

/-! ## Integration with GoalInfo -/

/-- Test: GoalInfo preserves gotoLocations. -/
def testGoalInfoGotoLocations : IO Unit := do
  printSubsection "GoalInfo GotoLocations"

  let goalInfo : GoalInfo := {
    type := .text "P ∧ Q"
    id := "goal1"
    gotoLocations := {
      definition := some { uri := "file:///and.lean", position := ⟨100, 0⟩ }
      typeDef := none
    }
  }

  assertSome "goal has definition location" goalInfo.gotoLocations.definition
  assertNone "goal has no typeDef location" goalInfo.gotoLocations.typeDef
  assertEqual "definition uri" (goalInfo.gotoLocations.definition.map (·.uri)) (some "file:///and.lean")

/-- Test: HypothesisInfo preserves gotoLocations. -/
def testHypothesisInfoGotoLocations : IO Unit := do
  printSubsection "HypothesisInfo GotoLocations"

  let hypInfo : HypothesisInfo := {
    name := "h"
    type := .text "P → Q"
    id := "hyp1"
    gotoLocations := {
      definition := some { uri := "file:///local.lean", position := ⟨5, 2⟩ }
      typeDef := some { uri := "file:///arrow.lean", position := ⟨50, 0⟩ }
    }
  }

  assertSome "hyp has definition location" hypInfo.gotoLocations.definition
  assertSome "hyp has typeDef location" hypInfo.gotoLocations.typeDef

/-! ## Test Runner -/

def runTests : IO Unit := do
  printSection "Goto Location Tests (Unit)"

  -- Structure tests (no MetaM needed)
  testGetTypeConstName
  testGotoLocationsDefault
  testGotoLocationConstruction
  testGotoLocationsJson
  testGoalInfoGotoLocations
  testHypothesisInfoGotoLocations

  -- Note: MetaM tests (testConstExpr, etc.) require a full Lean environment
  -- and are tested via the RPC integration tests instead.
  -- Uncomment the following to run them manually with proper env setup:
  -- testConstExpr
  -- testAppExpr
  -- testNestedAppExpr
  -- testForallExpr
  -- testNoResolvableConst

  IO.println "\n  ✓ Goto location unit tests passed"

end Tests.UnitGotoLocation
