/-! ## Name Filtering -/

/-- Check if pattern is a substring of s by splitting. -/
private def containsSubstr (s pattern : String) : Bool :=
  (s.splitOn pattern).length > 1

def String.isHygienic (s : String) : Bool :=
  containsSubstr s "._hyg." || containsSubstr s "._@."

def String.isUserVisible (s : String) : Bool :=
  !s.isEmpty && s != "[anonymous]" && !s.isHygienic

def String.filterName (s : String) : String :=
  if s.isUserVisible then s else ""

def String.filterNameOpt (s : String) : Option String :=
  if s.isUserVisible then some s else none
