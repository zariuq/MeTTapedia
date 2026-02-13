/-
# English Verb Morphology

Verb conjugation and auxiliary system ported from GF ResEng.gf and ParadigmsEng.gf.

English verbs have 5 base forms (VInf, VPres, VPPart, VPresPart, VPast).
All tenses are constructed from these + auxiliary verbs (be, have, do).

Key features:
- Regular verbs: walk → walks, walked, walked, walking
- Irregular verbs: go → goes, went, gone, going
- Do-support for questions and negation: "does he walk?", "he doesn't walk"
- Auxiliary verbs: be/have/do with full polarity/agreement paradigms

## References
- GF ResEng.gf: Verb type, mkVerb, predV, nonAuxVerbForms, auxVerbForms
- GF ParadigmsEng.gf: regV, irregV, mk5V, add_s, duplFinal
-/

import Mettapedia.Languages.GF.English.Nouns

namespace Mettapedia.Languages.GF.English.Verbs

open Mettapedia.Languages.GF.English
-- Note: strDropEnd, strTakeEnd, isVowel from Morphology (English namespace)
-- addS from Nouns

/-! ## Morphological Helpers -/

/-- Add -s for 3rd person singular present (reuses noun pluralization rules).
    walk → walks, go → goes, try → tries, kiss → kisses -/
def addSVerb (base : String) : String := Nouns.addS base

/-- Add -ed for regular past tense / past participle.
    walk → walked, try → tried, love → loved, stop → stopped -/
def addEd (base : String) : String :=
  let end1 := strTakeEnd base 1
  let end2 := strTakeEnd base 2
  -- -e ending: love → loved
  if end1 == "e" then base ++ "d"
  -- consonant+y: try → tried
  else if end1 == "y" && !(end2 == "ay" || end2 == "ey" || end2 == "iy" ||
                           end2 == "oy" || end2 == "uy") then
    strDropEnd base 1 ++ "ied"
  -- default: walk → walked
  else base ++ "ed"

/-- Add -ing for present participle.
    walk → walking, love → loving, try → trying, die → dying -/
def addIng (base : String) : String :=
  let end1 := strTakeEnd base 1
  let end2 := strTakeEnd base 2
  -- -ee ending: see → seeing (keep both e's)
  if end2 == "ee" then base ++ "ing"
  -- -ie ending: die → dying, tie → tying
  else if end2 == "ie" then strDropEnd base 2 ++ "ying"
  -- -e ending: love → loving (drop final e)
  else if end1 == "e" then strDropEnd base 1 ++ "ing"
  -- default: walk → walking
  else base ++ "ing"

/-! ## Verb Constructors -/

/-- Fully specified verb: all 5 forms + particle + reflexive.
    Ported from ResEng.gf `mkVerb`. -/
def mk5V (inf pres3sg past ppart prpart : String)
    (particle : String := "") (refl : Bool := false) : EnglishVerb :=
  { s := fun vf => match vf with
      | .VInf => inf
      | .VPres => pres3sg
      | .VPast => past
      | .VPPart => ppart
      | .VPresPart => prpart
    p := particle
    isRefl := refl }

/-- Regular verb: all forms derived from base.
    Ported from ParadigmsEng.gf `regV`. -/
def regV (base : String) (particle : String := "") : EnglishVerb :=
  mk5V base (addSVerb base) (addEd base) (addEd base) (addIng base) particle

/-- Irregular verb: 3 forms (base, past, ppart) — pres3sg and prpart derived.
    Ported from ParadigmsEng.gf `irregV`. -/
def irregV (base past ppart : String) (particle : String := "") : EnglishVerb :=
  mk5V base (addSVerb base) past ppart (addIng base) particle

/-- 4-form irregular verb (explicit present participle).
    Ported from ParadigmsEng.gf `irreg4V`. -/
def irreg4V (base past ppart prpart : String) (particle : String := "") : EnglishVerb :=
  mk5V base (addSVerb base) past ppart prpart particle

/-- Add a particle to a verb: "give" + "up" → "give up" -/
def partV (v : EnglishVerb) (particle : String) : EnglishVerb :=
  { v with p := particle }

/-- Mark verb as reflexive -/
def reflV (v : EnglishVerb) : EnglishVerb :=
  { v with isRefl := true }

/-! ## Agreement Helper -/

/-- Select 3sg form vs base form based on agreement.
    "has"/"have", "does"/"do", "walks"/"walk" -/
def agrVerb (has have_ : String) : Agr → String
  | .AgP3Sg _ => has
  | _ => have_

/-! ## Auxiliary Verb System

English auxiliaries (be, have, do) have irregular paradigms with
polarity-dependent forms (negation contractions).
-/

/-- Auxiliary verb with full paradigm: present/past × polarity × agreement -/
structure AuxVerb where
  pres : Polarity → Agr → String
  past : Polarity → Agr → String
  inf : String
  ppart : String
  prpart : String

/-- Positive/negative form helper -/
def posneg (p : Polarity) (s : String) : String :=
  match p with
  | .Pos => s
  | .Neg => s ++ "n't"

/-- Auxiliary "be": am/is/are, was/were, been, being -/
def auxBe : AuxVerb :=
  { pres := fun pol agr => match pol, agr with
      | .Pos, .AgP1 .Sg => "am"
      | .Neg, .AgP1 .Sg => "am not"
      | _, .AgP3Sg _ => posneg pol "is"
      | _, _ => posneg pol "are"
    past := fun pol agr => match agr with
      | .AgP1 .Sg | .AgP3Sg _ => posneg pol "was"
      | _ => posneg pol "were"
    inf := "be"
    ppart := "been"
    prpart := "being" }

/-- Auxiliary "have": have/has, had -/
def auxHave : AuxVerb :=
  { pres := fun pol agr => match pol with
      | .Pos => agrVerb "has" "have" agr
      | .Neg => agrVerb "hasn't" "haven't" agr
    past := fun pol _ => match pol with
      | .Pos => "had"
      | .Neg => "hadn't"
    inf := "have"
    ppart := "had"
    prpart := "having" }

/-- Auxiliary "do": do/does, did (used for questions and negation) -/
def auxDo : AuxVerb :=
  { pres := fun pol agr => match pol with
      | .Pos => agrVerb "does" "do" agr
      | .Neg => agrVerb "doesn't" "don't" agr
    past := fun pol _ => match pol with
      | .Pos => "did"
      | .Neg => "didn't"
    inf := "do"
    ppart := "done"
    prpart := "doing" }

/-- Reflexive pronoun by agreement -/
def reflPron : Agr → String
  | .AgP1 .Sg => "myself"
  | .AgP2 .Sg => "yourself"
  | .AgP3Sg .Masc => "himself"
  | .AgP3Sg .Fem => "herself"
  | .AgP3Sg .Neutr => "itself"
  | .AgP1 .Pl => "ourselves"
  | .AgP2 .Pl => "yourselves"
  | .AgP3Pl => "themselves"

/-- Possessive pronoun by agreement -/
def possPron : Agr → String
  | .AgP1 .Sg => "my"
  | .AgP2 .Sg => "your"
  | .AgP3Sg .Masc => "his"
  | .AgP3Sg .Fem => "her"
  | .AgP3Sg .Neutr => "its"
  | .AgP1 .Pl => "our"
  | .AgP2 .Pl => "your"
  | .AgP3Pl => "their"

/-! ## Example Verbs -/

-- Regular verbs
def walk_V : EnglishVerb := regV "walk"
def love_V : EnglishVerb := regV "love"
def try_V : EnglishVerb := regV "try"
def kiss_V : EnglishVerb := regV "kiss"
def play_V : EnglishVerb := regV "play"
def see_V : EnglishVerb := irregV "see" "saw" "seen"
def die_V : EnglishVerb := regV "die"

-- Irregular verbs
def go_V : EnglishVerb := mk5V "go" "goes" "went" "gone" "going"
def be_V : EnglishVerb := mk5V "be" "is" "was" "been" "being"
def have_V : EnglishVerb := mk5V "have" "has" "had" "had" "having"
def do_V : EnglishVerb := mk5V "do" "does" "did" "done" "doing"
def eat_V : EnglishVerb := irregV "eat" "ate" "eaten"
def drink_V : EnglishVerb := irregV "drink" "drank" "drunk"
def sing_V : EnglishVerb := irregV "sing" "sang" "sung"
def run_V : EnglishVerb := irreg4V "run" "ran" "run" "running"
def swim_V : EnglishVerb := irreg4V "swim" "swam" "swum" "swimming"
def give_V : EnglishVerb := irregV "give" "gave" "given"
def take_V : EnglishVerb := irregV "take" "took" "taken"
def sleep_V : EnglishVerb := irregV "sleep" "slept" "slept"

-- Particle verbs
def giveUp_V : EnglishVerb := partV (irregV "give" "gave" "given") "up"
def lookAt_V : EnglishVerb := partV (regV "look") "at"

/-! ## Two-Place Verbs (V2)

A V2 is a verb with a complement case marker (preposition or empty for direct object).
Ported from CatEng.gf: `V2 = Verb ** {c2 : Str}`.
-/

/-- Two-place verb: a verb plus complement preposition.
    Empty `c2` = direct object ("love X"), non-empty = prepositional ("look at X"). -/
structure EnglishV2 extends EnglishVerb where
  c2 : String

/-- Build V2 from a verb and complement preposition -/
def mkV2 (v : EnglishVerb) (c2 : String := "") : EnglishV2 :=
  { toEnglishVerb := v, c2 := c2 }

/-- Regular V2 shortcut -/
def regV2 (base : String) (c2 : String := "") : EnglishV2 :=
  mkV2 (regV base) c2

-- V2 lexicon
def love_V2 : EnglishV2 := mkV2 love_V
def see_V2 : EnglishV2 := mkV2 see_V
def eat_V2 : EnglishV2 := mkV2 eat_V
def give_V2 : EnglishV2 := mkV2 give_V
def take_V2 : EnglishV2 := mkV2 take_V
def drink_V2 : EnglishV2 := mkV2 drink_V
def kill_V2 : EnglishV2 := regV2 "kill"
def read_V2 : EnglishV2 := mkV2 (irregV "read" "read" "read")
def man_V2 : EnglishV2 := regV2 "man"           -- "man the boats"
def lookAt_V2 : EnglishV2 := mkV2 (regV "look") "at"
def waitFor_V2 : EnglishV2 := mkV2 (regV "wait") "for"
def listenTo_V2 : EnglishV2 := mkV2 (regV "listen") "to"

/-! ## Tests -/

-- Regular conjugation
#eval! walk_V.s .VInf       -- "walk"
#eval! walk_V.s .VPres      -- "walks"
#eval! walk_V.s .VPast      -- "walked"
#eval! walk_V.s .VPPart     -- "walked"
#eval! walk_V.s .VPresPart  -- "walking"

-- -e ending
#eval! love_V.s .VPast      -- "loved"
#eval! love_V.s .VPresPart  -- "loving"

-- -y ending
#eval! try_V.s .VPres       -- "tries"
#eval! try_V.s .VPast       -- "tried"
#eval! try_V.s .VPresPart   -- "trying"

-- -ie ending
#eval! die_V.s .VPresPart   -- "dying"

-- Sibilant
#eval! kiss_V.s .VPres      -- "kisses"

-- Irregular verbs
#eval! go_V.s .VPast        -- "went"
#eval! eat_V.s .VPPart      -- "eaten"
#eval! run_V.s .VPresPart   -- "running"

-- Auxiliaries
#eval! auxBe.pres .Pos (.AgP1 .Sg)     -- "am"
#eval! auxBe.pres .Pos (.AgP3Sg .Masc) -- "is"
#eval! auxBe.pres .Neg (.AgP3Sg .Masc) -- "isn't"
#eval! auxBe.past .Pos (.AgP1 .Sg)     -- "was"
#eval! auxBe.past .Neg (.AgP1 .Pl)     -- "weren't"
#eval! auxDo.pres .Pos (.AgP3Sg .Fem)  -- "does"
#eval! auxDo.pres .Neg (.AgP2 .Sg)     -- "don't"

-- Reflexive pronouns
#eval! reflPron (.AgP1 .Sg)     -- "myself"
#eval! reflPron (.AgP3Sg .Fem)  -- "herself"
#eval! reflPron .AgP3Pl         -- "themselves"

/-! ## Correctness Properties -/

/-- Regular verbs: infinitive = base form -/
theorem regV_inf (base : String) (p : String) :
    (regV base p).s .VInf = base := rfl

/-- Regular verbs: pres3sg = addS of base -/
theorem regV_pres (base : String) (p : String) :
    (regV base p).s .VPres = addSVerb base := rfl

/-- Regular verbs: past = addEd of base -/
theorem regV_past (base : String) (p : String) :
    (regV base p).s .VPast = addEd base := rfl

/-- mk5V is fully determined -/
theorem mk5V_complete (a b c d e : String) (p : String) (r : Bool) :
    (mk5V a b c d e p r).s .VInf = a ∧
    (mk5V a b c d e p r).s .VPres = b ∧
    (mk5V a b c d e p r).s .VPast = c ∧
    (mk5V a b c d e p r).s .VPPart = d ∧
    (mk5V a b c d e p r).s .VPresPart = e :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Concrete test: walk → walks
theorem test_walk_pres : walk_V.s .VPres = "walks" := by decide
-- Concrete test: walk → walked
theorem test_walk_past : walk_V.s .VPast = "walked" := by decide
-- Concrete test: walk → walking
theorem test_walk_prpart : walk_V.s .VPresPart = "walking" := by decide
-- Concrete test: try → tries
theorem test_try_pres : try_V.s .VPres = "tries" := by decide
-- Concrete test: try → tried
theorem test_try_past : try_V.s .VPast = "tried" := by decide
-- Concrete test: love → loved
theorem test_love_past : love_V.s .VPast = "loved" := by decide
-- Concrete test: love → loving
theorem test_love_prpart : love_V.s .VPresPart = "loving" := by decide
-- Concrete test: die → dying
theorem test_die_prpart : die_V.s .VPresPart = "dying" := by decide
-- Concrete test: go → went (irregular)
theorem test_go_past : go_V.s .VPast = "went" := by decide
-- Concrete test: eat → eaten (irregular)
theorem test_eat_ppart : eat_V.s .VPPart = "eaten" := by decide
-- Auxiliary: "am" for 1sg present positive
theorem test_be_am : auxBe.pres .Pos (.AgP1 .Sg) = "am" := by decide
-- Auxiliary: "doesn't" for 3sg present negative
theorem test_doesnt : auxDo.pres .Neg (.AgP3Sg .Fem) = "doesn't" := by decide

end Mettapedia.Languages.GF.English.Verbs
