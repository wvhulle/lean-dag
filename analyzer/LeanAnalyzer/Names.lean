namespace LeanAnalyzer

def isHygienicName (s : String) : Bool :=
  (s.splitOn "._hyg.").length > 1 || (s.splitOn "._@.").length > 1

def isAnonymousName (s : String) : Bool :=
  s.isEmpty || s == "[anonymous]"

def isUserVisibleName (s : String) : Bool :=
  !isHygienicName s && !isAnonymousName s

def filterName (s : String) : String :=
  if isUserVisibleName s then s else ""

def filterNameOpt (s : String) : Option String :=
  if isUserVisibleName s then some s else none

end LeanAnalyzer
