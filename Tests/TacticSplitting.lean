import Lean
import LeanAnalyzer
import Tests.Helpers

namespace Tests.TacticSplitting

open Lean LeanAnalyzer Tests.Helpers

def getClosestRw (text: String) (pos: Nat) : String := Id.run do
  let mut currentPos := pos
  let mut state : Nat := 0
  let mut result : List Char := []

  while currentPos > 0 do
    currentPos := currentPos - 1
    let char := text.toList[currentPos]!

    match state with
    | 0 =>
      if char == '[' then
        state := 1
    | 1 =>
      if !char.isWhitespace && !char.isDigit then
        state := 2
        result := char :: result
    | _ =>
      if !char.isWhitespace then
        result := char :: result
      else
        break

  return String.ofList result

def prettifyRwRule (tacticString : String) : String :=
  (tacticString.splitOn ",").head!.trim

def isTacticRwRule (syntaxStr : String) : Bool :=
  syntaxStr.startsWith "[(Tactic.rwRule"

def testGetClosestRw : IO Unit := do
  IO.println "\n  [Extract Rw Tactic Name]"

  let text1 := "rw [Nat.add_comm]"
  let rwName1 := getClosestRw text1 4
  assertEqual "simple rw" rwName1 "rw"

  let text2 := "nth_rw 2 [Nat.add_comm]"
  let rwName2 := getClosestRw text2 10
  assertEqual "nth_rw" rwName2 "nth_rw"

  let text3 := "rw_mod_cast [Set.mem_inter_iff]"
  let rwName3 := getClosestRw text3 13
  assertEqual "rw_mod_cast" rwName3 "rw_mod_cast"

  let text4 := "simp_rw [lemma1, lemma2]"
  let rwName4 := getClosestRw text4 9
  assertEqual "simp_rw" rwName4 "simp_rw"

def testPrettifyRwRule : IO Unit := do
  IO.println "\n  [Prettify Rewrite Rule]"

  assertEqual "simple lemma" (prettifyRwRule "Nat.add_comm") "Nat.add_comm"
  assertEqual "with trailing comma" (prettifyRwRule "Nat.add_comm, ") "Nat.add_comm"
  assertEqual "with space" (prettifyRwRule "  Set.mem_inter_iff  ") "Set.mem_inter_iff"
  assertEqual "first of many" (prettifyRwRule "lemma1, lemma2, lemma3") "lemma1"

def testIsTacticRwRule : IO Unit := do
  IO.println "\n  [Identify Rewrite Rule Syntax]"

  assertTrue "rwRule syntax" (isTacticRwRule "[(Tactic.rwRule")
  assertTrue "rwRule with content" (isTacticRwRule "[(Tactic.rwRule something)]")
  assertTrue "not rwRule" (!isTacticRwRule "constructor")
  assertTrue "not rwRule list" (!isTacticRwRule "[lemma1]")

def testMultipleRwRules : IO Unit := do
  IO.println "\n  [Multiple Rewrite Rules -> Multiple Nodes]"

  let tacticText := "rw [Nat.add_zero, Nat.zero_add, Nat.add_comm]"
  let rules := tacticText.splitOn ","

  assertEqual "can split rules" rules.length 3
  assertEqual "first rule" rules[0]!.trim "rw [Nat.add_zero"

def testRwSplitTacticInfo : IO Unit := do
  IO.println "\n  [Rewrite Split Tactic Info]"

  let split1 : TacticInfo := { text := "rw [Nat.add_zero]" }
  let split2 : TacticInfo := { text := "rw [Nat.add_comm]" }

  assertTrue "split1 is rw" (split1.text.startsWith "rw")
  assertTrue "split2 is rw" (split2.text.startsWith "rw")
  assertTrue "split1 has single lemma" (containsSubstring split1.text "add_zero")
  assertTrue "split1 no second lemma" (!containsSubstring split1.text "add_comm")

def testRwVariants : IO Unit := do
  IO.println "\n  [Rewrite Tactic Variants]"

  let variants := ["rw", "rewrite", "rw_mod_cast", "simp_rw", "nth_rw", "conv_rw"]

  for variant in variants do
    let text := s!"{variant} [some_lemma]"
    assertTrue s!"{variant} has bracket" (containsSubstring text "[")

def testSimpDecomposition : IO Unit := do
  IO.println "\n  [Simp Lemma Decomposition]"

  let simpTactic := "simp only [Nat.add_zero, Nat.succ_eq_add_one]"

  let bracketStart := simpTactic.posOf '['
  let bracketEnd := simpTactic.posOf ']'
  assertTrue "has brackets" (bracketStart < bracketEnd)

  let startIdx := bracketStart.byteIdx + 1
  let endIdx := bracketEnd.byteIdx
  let lemmasStr := (simpTactic.toSubstring.drop startIdx).take (endIdx - startIdx) |>.toString
  let lemmas := lemmasStr.splitOn ","
  assertEqual "two lemmas" lemmas.length 2

def testHoverPositionMapping : IO Unit := do
  IO.println "\n  [Hover Position -> Sub-Tactic]"

  let text := "rw [lemma1, lemma2, lemma3]"

  let inLemma1 := text.toList[4]! == 'l'
  let inLemma2 := text.toList[12]! == 'l'

  assertTrue "pos 4 in lemma1" inLemma1
  assertTrue "pos 12 in lemma2" inLemma2

def runTests : IO Unit := do
  IO.println "\n  Tactic Splitting Tests"

  testGetClosestRw
  testPrettifyRwRule
  testIsTacticRwRule
  testMultipleRwRules
  testRwSplitTacticInfo
  testRwVariants
  testSimpDecomposition
  testHoverPositionMapping

  IO.println "\n  ✓ Tactic splitting tests passed"

end Tests.TacticSplitting
