/-
# GFCore.Repair — Dataset repair preprocessing

Pure functions that normalize dataset text before GF parsing.
Every repair is mechanical and auditable — no heuristics.
-/

namespace GFCore

/-- Replace slash alternatives with "or": "X / Y / Z" → "X or Y or Z".
    The dataset uses "/" to denote synonyms/alternatives.
    Replacing with "or" preserves meaning and is parseable by GF. -/
def repairSlash (s : String) : String :=
  s.replace " / " " or "

/-- Fix possessive tokenization: "earth 's" → "earth's", "it 's" → "it's". -/
def repairPossessive (s : String) : String :=
  s.replace " 's " "'s "
   |>.replace " 's" "'s"

/-- Strip trailing commas from words. -/
def repairTrailingComma (s : String) : String :=
  let words := s.splitOn " "
  let cleaned := words.map fun w =>
    if w.endsWith "," && w.length > 1 then (w.dropEnd 1).toString else w
  String.intercalate " " cleaned

/-- Known typo corrections for the entailment bank dataset. -/
def typoCorrections : List (String × String) :=
  [ ("someting", "something")
  , ("childern", "children")
  , ("gradens", "gardens")
  , ("abosorbing", "absorbing")
  , ("abosrb", "absorb")
  , ("accross", "across")
  , ("activites", "activities")
  , ("survivial", "survival")
  , ("bilogical", "biological")
  , ("vaccum", "vacuum")
  ]

/-- Apply known typo corrections. -/
def repairTypos (s : String) : String :=
  typoCorrections.foldl (fun acc (typo, fix) => acc.replace typo fix) s

/-- Apply all repairs to a sentence. -/
def repairSentence (s : String) : String :=
  s |> repairSlash
    |> repairPossessive
    |> repairTrailingComma
    |> repairTypos

-- ============================================================
-- Tests
-- ============================================================

#eval do
  -- Slash → "or" (preserves meaning)
  let r1 := repairSlash "a star is a kind of celestial object / celestial body"
  IO.println s!"slash1: \"{r1}\""
  assert! r1 == "a star is a kind of celestial object or celestial body"

  -- Multiple alternatives
  let r2 := repairSlash "emits / produces / generates that something"
  IO.println s!"slash2: \"{r2}\""
  assert! r2 == "emits or produces or generates that something"

  -- Mid-sentence slash
  let r3 := repairSlash "the earth rotation / revolution causes day"
  assert! r3 == "the earth rotation or revolution causes day"

  -- No slash
  let r4 := repairSlash "a bear is a kind of animal"
  assert! r4 == "a bear is a kind of animal"

  -- Possessive
  let r5 := repairPossessive "the earth 's axis"
  assert! r5 == "the earth's axis"
  IO.println s!"possessive: \"{r5}\""

  -- Trailing comma
  let r6 := repairTrailingComma "rock, soil, and sand"
  IO.println s!"comma: \"{r6}\""
  assert! r6 == "rock soil and sand"

  -- Typo
  let r7 := repairTypos "someting is wrong with the childern"
  assert! r7 == "something is wrong with the children"

  -- Full pipeline preserves continuation
  let r8 := repairSentence "the earth 's rotation / revolution causes day and night"
  IO.println s!"full: \"{r8}\""
  assert! r8 == "the earth's rotation or revolution causes day and night"

  IO.println "All repair tests passed"

end GFCore
