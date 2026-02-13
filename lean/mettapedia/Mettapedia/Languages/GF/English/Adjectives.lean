/-
# English Adjective Morphology

Adjective comparison paradigms ported from GF ParadigmsEng.gf and ResEng.gf.

English adjectives have 4 forms:
- Positive: "big", "beautiful"
- Comparative: "bigger", "more beautiful"
- Superlative: "biggest", "most beautiful"
- Adverb: "bigly", "beautifully"

Two comparison strategies:
- Synthetic: -er, -est for short adjectives (big → bigger → biggest)
- Analytic: more, most for longer adjectives (beautiful → more beautiful)

## References
- GF ParadigmsEng.gf: regADeg, compoundADeg, mkAdjective, adj2adv
- GF ResEng.gf: Adjective type, AForm, mkAdjective
-/

import Mettapedia.Languages.GF.English.Morphology

namespace Mettapedia.Languages.GF.English.Adjectives

open Mettapedia.Languages.GF.English

/-! ## Morphological Helpers -/

/-- Adjective-to-adverb conversion.
    Ported from ParadigmsEng.gf `adj2adv`:
    - "possible" → "possibly" (-ble → -bly)
    - "happy" → "happily" (-y → -ily)
    - "full" → "fully" (-ll → -lly)
    - default: "quick" → "quickly" (+ly) -/
def adj2Adv (adj : String) : String :=
  let end3 := strTakeEnd adj 3
  let end2 := strTakeEnd adj 2
  let end1 := strTakeEnd adj 1
  if end3 == "ble" then strDropEnd adj 1 ++ "y"
  else if end1 == "y" then strDropEnd adj 1 ++ "ily"
  else if end2 == "ll" then adj ++ "y"
  else adj ++ "ly"

/-- Form comparative/superlative stem.
    Ported from ParadigmsEng.gf `regADeg`:
    - "happy" → "happi" (-y → -ie for er/est)
    - "large" → "large" (-e stays, just add -r, -st)
    - "big" → "bigge" (would need duplication, simplified here) -/
def compStem (adj : String) : String :=
  let end1 := strTakeEnd adj 1
  if end1 == "y" then strDropEnd adj 1 ++ "ie"
  else if end1 == "e" then adj
  else adj ++ "e"

/-! ## Adjective Constructors -/

/-- Fully specified adjective: all 4 forms explicit.
    Ported from ResEng.gf `mkAdjective`. -/
def mkAdj (pos comp super adv : String) : EnglishAdj :=
  { s := fun af => match af with
      | .AAdj .Pos _ => pos
      | .AAdj .Comp _ => comp
      | .AAdj .Super _ => super
      | .AAdv => adv }

/-- Regular adjective with synthetic comparison (-er, -est).
    Ported from ParadigmsEng.gf `regADeg`. -/
def regA (adj : String) : EnglishAdj :=
  let stem := compStem adj
  mkAdj adj (stem ++ "r") (stem ++ "st") (adj2Adv adj)

/-- Compound adjective with analytic comparison (more/most).
    Ported from ParadigmsEng.gf `compoundADeg`. -/
def compoundA (adj : String) : EnglishAdj :=
  mkAdj adj ("more " ++ adj) ("most " ++ adj) (adj2Adv adj)

/-- Fully irregular adjective (all 4 forms given). -/
def irregA (pos comp super adv : String) : EnglishAdj :=
  mkAdj pos comp super adv

/-- Invariable adjective (no comparison, same form everywhere). -/
def invarA (s : String) : EnglishAdj :=
  { s := fun _ => s }

/-! ## Example Adjectives -/

-- Regular (er, est)
def big_A : EnglishAdj := mkAdj "big" "bigger" "biggest" "bigly"
def small_A : EnglishAdj := regA "small"
def old_A : EnglishAdj := regA "old"
def young_A : EnglishAdj := regA "young"
def warm_A : EnglishAdj := regA "warm"
def cold_A : EnglishAdj := regA "cold"
def happy_A : EnglishAdj := regA "happy"
def large_A : EnglishAdj := regA "large"

-- Compound (more/most)
def beautiful_A : EnglishAdj := compoundA "beautiful"
def important_A : EnglishAdj := compoundA "important"
def interesting_A : EnglishAdj := compoundA "interesting"

-- Irregular
def good_A : EnglishAdj := irregA "good" "better" "best" "well"
def bad_A : EnglishAdj := irregA "bad" "worse" "worst" "badly"
def far_A : EnglishAdj := irregA "far" "farther" "farthest" "far"

/-! ## Tests -/

-- Regular
#eval! big_A.s (.AAdj .Pos .Nom)    -- "big"
#eval! big_A.s (.AAdj .Comp .Nom)   -- "bigger"
#eval! big_A.s (.AAdj .Super .Nom)  -- "biggest"
#eval! big_A.s .AAdv                -- "bigly"

-- -y ending
#eval! happy_A.s (.AAdj .Comp .Nom)  -- "happier"
#eval! happy_A.s (.AAdj .Super .Nom) -- "happiest"
#eval! happy_A.s .AAdv               -- "happily"

-- -e ending
#eval! large_A.s (.AAdj .Comp .Nom)  -- "larger"
#eval! large_A.s (.AAdj .Super .Nom) -- "largest"

-- Compound
#eval! beautiful_A.s (.AAdj .Comp .Nom)  -- "more beautiful"
#eval! beautiful_A.s (.AAdj .Super .Nom) -- "most beautiful"
#eval! beautiful_A.s .AAdv               -- "beautifully"

-- Irregular
#eval! good_A.s (.AAdj .Comp .Nom)   -- "better"
#eval! good_A.s (.AAdj .Super .Nom)  -- "best"
#eval! good_A.s .AAdv                -- "well"

-- Adverb formation
#eval! adj2Adv "possible"    -- "possibly"
#eval! adj2Adv "happy"       -- "happily"
#eval! adj2Adv "full"        -- "fully"
#eval! adj2Adv "quick"       -- "quickly"

/-! ## Correctness Properties -/

/-- mkAdj is fully determined -/
theorem mkAdj_complete (a b c d : String) :
    (mkAdj a b c d).s (.AAdj .Pos .Nom) = a ∧
    (mkAdj a b c d).s (.AAdj .Comp .Nom) = b ∧
    (mkAdj a b c d).s (.AAdj .Super .Nom) = c ∧
    (mkAdj a b c d).s .AAdv = d :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Compound adjective preserves positive form -/
theorem compoundA_pos (s : String) :
    (compoundA s).s (.AAdj .Pos .Nom) = s := rfl

/-- Compound comparative prepends "more" -/
theorem compoundA_comp (s : String) :
    (compoundA s).s (.AAdj .Comp .Nom) = "more " ++ s := rfl

/-- Compound superlative prepends "most" -/
theorem compoundA_super (s : String) :
    (compoundA s).s (.AAdj .Super .Nom) = "most " ++ s := rfl

-- Concrete tests
theorem test_good_better : good_A.s (.AAdj .Comp .Nom) = "better" := by decide
theorem test_good_best : good_A.s (.AAdj .Super .Nom) = "best" := by decide
theorem test_good_well : good_A.s .AAdv = "well" := by decide
theorem test_happy_happier : happy_A.s (.AAdj .Comp .Nom) = "happier" := by decide
theorem test_happy_happiest : happy_A.s (.AAdj .Super .Nom) = "happiest" := by decide
theorem test_large_larger : large_A.s (.AAdj .Comp .Nom) = "larger" := by decide
theorem test_beautiful_more : beautiful_A.s (.AAdj .Comp .Nom) = "more beautiful" := by decide

end Mettapedia.Languages.GF.English.Adjectives
