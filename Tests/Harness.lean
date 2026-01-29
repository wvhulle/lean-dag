import Lean

namespace Tests.Harness

def assertEqual [BEq α] [ToString α] (name : String) (actual expected : α) : IO Unit := do
  if actual == expected then
    IO.println s!"  ✓ {name}"
  else
    IO.println s!"  ✗ {name}"
    IO.println s!"    expected: {expected}"
    IO.println s!"    actual:   {actual}"
    throw <| IO.userError s!"Test failed: {name}"

def assertTrue (name : String) (condition : Bool) : IO Unit := do
  if condition then
    IO.println s!"  ✓ {name}"
  else
    IO.println s!"  ✗ {name}: condition was false"
    throw <| IO.userError s!"Test failed: {name}"

def assertSome (name : String) (opt : Option α) : IO Unit := do
  if opt.isSome then
    IO.println s!"  ✓ {name}"
  else
    IO.println s!"  ✗ {name}: expected Some, got None"
    throw <| IO.userError s!"Test failed: {name}"

def assertNone (name : String) (opt : Option α) : IO Unit := do
  if opt.isNone then
    IO.println s!"  ✓ {name}"
  else
    IO.println s!"  ✗ {name}: expected None, got Some"
    throw <| IO.userError s!"Test failed: {name}"

def assertNonEmpty [Inhabited α] (name : String) (arr : Array α) : IO Unit := do
  if arr.size > 0 then
    IO.println s!"  ✓ {name}"
  else
    IO.println s!"  ✗ {name}: expected non-empty array"
    throw <| IO.userError s!"Test failed: {name}"

def skipTest (name : String) (reason : String) : IO Unit := do
  IO.println s!"  ⊘ {name}: SKIPPED ({reason})"

def containsSubstring (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def printSection (title : String) : IO Unit := do
  IO.println ""
  IO.println "══════════════════════════════════════════════════════════════"
  IO.println s!"  {title}"
  IO.println "══════════════════════════════════════════════════════════════"

def printSubsection (title : String) : IO Unit := do
  IO.println s!"\n  [{title}]"

end Tests.Harness
