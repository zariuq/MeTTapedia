/-
# English Noun Morphology

Noun paradigms ported from GF ParadigmsEng.gf and ResEng.gf.

English nouns have 4 forms: sg.nom, sg.gen, pl.nom, pl.gen.
- Regular: cat → cat's, cats, cats'
- Irregular plural: man → man's, men, men's
- Fully irregular: all 4 forms specified

## References
- GF ParadigmsEng.gf: add_s, regN, mk2N, mk4N
- GF ResEng.gf: mkNoun, genitiveS, regGenitiveS
-/

import Mettapedia.Languages.GF.English.Morphology

namespace Mettapedia.Languages.GF.English.Nouns

open Mettapedia.Languages.GF.English

/-! ## Morphological Helpers -/

/-- English pluralization rules (ported from ParadigmsEng.gf `add_s`).
    - "radio", "bamboo" → +s (io/oo ending)
    - "bus", "box", "flash", "church", "hero" → +es (s/z/x/sh/ch/o ending)
    - "boy", "day" → +s (vowel+y)
    - "fly", "city" → -y+ies (consonant+y)
    - default → +s -/
def addS (w : String) : String :=
  let cs := w.toList
  let len := cs.length
  if len < 1 then w
  else
    let end2 := strTakeEnd w 2
    let end1 := strTakeEnd w 1
    -- io/oo endings: radio → radios, bamboo → bamboos
    if end2 == "io" || end2 == "oo" then w ++ "s"
    -- sibilant/o endings: bus → buses, box → boxes, church → churches
    else if end1 == "s" || end1 == "z" || end1 == "x" then w ++ "es"
    else if end2 == "sh" || end2 == "ch" then w ++ "es"
    else if end1 == "o" then w ++ "es"
    -- vowel+y: boy → boys, day → days (check 2-char ending)
    else if end2 == "ay" || end2 == "ey" || end2 == "iy" ||
            end2 == "oy" || end2 == "uy" then w ++ "s"
    -- consonant+y: fly → flies, city → cities
    else if end1 == "y" then strDropEnd w 1 ++ "ies"
    -- default: car → cars
    else w ++ "s"

/-- English genitive formation (ported from ResEng.gf `genitiveS`).
    - "dogs" → "dogs'" (already ends in s)
    - "cat" → "cat's" -/
def genitiveS (s : String) : String :=
  match strLast s with
  | some 's' => s ++ "'"
  | _ => s ++ "'s"

/-- Case-dispatch for genitives (ported from ResEng.gf `regGenitiveS`) -/
def regGenitiveS (s : String) : Case → String
  | .Nom => s
  | .Gen => genitiveS s

/-! ## Noun Constructors -/

/-- Worst-case noun constructor: all 4 forms explicit.
    Ported from ResEng.gf `mkNoun`. -/
def mk4N (sgNom plNom sgGen plGen : String) (g : Gender := .Neutr) : EnglishNoun :=
  { s := fun n c => match n, c with
      | .Sg, .Nom => sgNom
      | .Sg, .Gen => sgGen
      | .Pl, .Nom => plNom
      | .Pl, .Gen => plGen
    g := g }

/-- Two-form noun: singular + plural (genitives derived).
    Ported from ParadigmsEng.gf `mk2N`. -/
def mk2N (sg pl : String) (g : Gender := .Neutr) : EnglishNoun :=
  mk4N sg pl (genitiveS sg) (genitiveS pl) g

/-- Regular noun: plural and genitives derived from singular.
    Ported from ParadigmsEng.gf `regN`. -/
def regN (sg : String) (g : Gender := .Neutr) : EnglishNoun :=
  mk2N sg (addS sg) g

/-- Change gender of an existing noun -/
def genderN (g : Gender) (n : EnglishNoun) : EnglishNoun :=
  { n with g := g }

/-- Compound noun: uninflected modifier + inflected head.
    E.g. compoundN "baby" (regN "boom") → "baby boom", "baby booms" -/
def compoundN (modifier : String) (n : EnglishNoun) : EnglishNoun :=
  { s := fun num cas => modifier ++ " " ++ n.s num cas
    g := n.g }

/-! ## Decline Helper -/

/-- Decline a noun to a surface form -/
def decline (n : EnglishNoun) (num : Number) (cas : Case) : String :=
  n.s num cas

/-! ## Example Nouns -/

def cat_N : EnglishNoun := regN "cat"
def dog_N : EnglishNoun := regN "dog"
def house_N : EnglishNoun := regN "house"
def car_N : EnglishNoun := regN "car"
def city_N : EnglishNoun := regN "city"
def bus_N : EnglishNoun := regN "bus"
def box_N : EnglishNoun := regN "box"
def church_N : EnglishNoun := regN "church"
def hero_N : EnglishNoun := regN "hero"
def radio_N : EnglishNoun := regN "radio"
def boy_N : EnglishNoun := regN "boy"
def fly_N : EnglishNoun := regN "fly"
def baby_N : EnglishNoun := regN "baby"
def kiss_N : EnglishNoun := regN "kiss"

-- Irregular nouns
def man_N : EnglishNoun := mk2N "man" "men" .Masc
def woman_N : EnglishNoun := mk2N "woman" "women" .Fem
def child_N : EnglishNoun := mk2N "child" "children"
def foot_N : EnglishNoun := mk2N "foot" "feet"
def tooth_N : EnglishNoun := mk2N "tooth" "teeth"
def mouse_N : EnglishNoun := mk2N "mouse" "mice"
def person_N : EnglishNoun := mk2N "person" "people"
def ox_N : EnglishNoun := mk2N "ox" "oxen"

-- Gendered nouns
def king_N : EnglishNoun := regN "king" .Masc
def queen_N : EnglishNoun := regN "queen" .Fem

-- Compound nouns
def babyBoom_N : EnglishNoun := compoundN "baby" (regN "boom")

/-! ## Tests -/

-- Regular pluralization
#eval! cat_N.s .Pl .Nom      -- "cats"
#eval! city_N.s .Pl .Nom     -- "cities"
#eval! bus_N.s .Pl .Nom      -- "buses"
#eval! box_N.s .Pl .Nom      -- "boxes"
#eval! church_N.s .Pl .Nom   -- "churches"
#eval! hero_N.s .Pl .Nom     -- "heroes"
#eval! radio_N.s .Pl .Nom    -- "radios"
#eval! boy_N.s .Pl .Nom      -- "boys"
#eval! fly_N.s .Pl .Nom      -- "flies"
#eval! baby_N.s .Pl .Nom     -- "babies"
#eval! kiss_N.s .Pl .Nom     -- "kisses"

-- Genitive forms
#eval! cat_N.s .Sg .Gen      -- "cat's"
#eval! cat_N.s .Pl .Gen      -- "cats'"
#eval! man_N.s .Sg .Gen      -- "man's"
#eval! man_N.s .Pl .Gen      -- "men's"
#eval! bus_N.s .Pl .Gen      -- "buses'"

-- Irregular nouns
#eval! man_N.s .Pl .Nom      -- "men"
#eval! child_N.s .Pl .Nom    -- "children"
#eval! woman_N.s .Pl .Nom    -- "women"

-- Compound nouns
#eval! babyBoom_N.s .Sg .Nom  -- "baby boom"
#eval! babyBoom_N.s .Pl .Nom  -- "baby booms"

/-! ## Correctness Properties -/

/-- Regular nouns: singular nominative = input lemma -/
theorem regN_sg_nom (s : String) (g : Gender) :
    (regN s g).s .Sg .Nom = s := rfl

/-- Regular nouns: plural nominative = addS of lemma -/
theorem regN_pl_nom (s : String) (g : Gender) :
    (regN s g).s .Pl .Nom = addS s := rfl

/-- mk2N preserves singular -/
theorem mk2N_sg_nom (sg pl : String) (g : Gender) :
    (mk2N sg pl g).s .Sg .Nom = sg := rfl

/-- mk2N uses given plural -/
theorem mk2N_pl_nom (sg pl : String) (g : Gender) :
    (mk2N sg pl g).s .Pl .Nom = pl := rfl

/-- mk4N is fully determined -/
theorem mk4N_complete (a b c d : String) (g : Gender) :
    (mk4N a b c d g).s .Sg .Nom = a ∧
    (mk4N a b c d g).s .Pl .Nom = b ∧
    (mk4N a b c d g).s .Sg .Gen = c ∧
    (mk4N a b c d g).s .Pl .Gen = d :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Compound noun preserves modifier -/
theorem compoundN_format (mod : String) (n : EnglishNoun) (num : Number) (cas : Case) :
    (compoundN mod n).s num cas = mod ++ " " ++ n.s num cas := rfl

-- Concrete test: "cat" → "cats" (regular -s)
theorem test_cat_pl : cat_N.s .Pl .Nom = "cats" := by decide
-- Concrete test: "city" → "cities" (y → ies)
theorem test_city_pl : city_N.s .Pl .Nom = "cities" := by decide
-- Concrete test: "bus" → "buses" (sibilant +es)
theorem test_bus_pl : bus_N.s .Pl .Nom = "buses" := by decide
-- Concrete test: "church" → "churches" (-ch +es)
theorem test_church_pl : church_N.s .Pl .Nom = "churches" := by decide
-- Concrete test: "boy" → "boys" (vowel+y +s)
theorem test_boy_pl : boy_N.s .Pl .Nom = "boys" := by decide
-- Concrete test: "fly" → "flies" (consonant+y → ies)
theorem test_fly_pl : fly_N.s .Pl .Nom = "flies" := by decide
-- Concrete test: "man" → "men" (irregular)
theorem test_man_pl : man_N.s .Pl .Nom = "men" := by decide
-- Concrete test: genitive "cat" → "cat's"
theorem test_cat_gen : cat_N.s .Sg .Gen = "cat's" := by decide
-- Concrete test: genitive "cats" → "cats'"
theorem test_cats_gen : cat_N.s .Pl .Gen = "cats'" := by decide

end Mettapedia.Languages.GF.English.Nouns
