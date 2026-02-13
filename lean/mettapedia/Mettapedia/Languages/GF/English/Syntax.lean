/-
# English Syntax Construction

Core linearization: word order, do-support, tense/aspect/polarity
combinations, and key GF abstract-to-concrete mappings.

Ported from GF ResEng.gf (mkClause, nonAuxVerbForms, predV)
and SentenceEng.gf, NounEng.gf, AdjectiveEng.gf.

## Key Architecture

English clause construction follows GF's two-pronged strategy:
1. **Non-auxiliary verbs**: use do-support for questions and negation
   - "he walks" (positive declarative: just finite verb)
   - "does he walk?" (question: do + subject + infinitive)
   - "he doesn't walk" (negative: do+n't + infinitive)
2. **Auxiliary verbs**: invert directly, negate with -n't
   - "he is walking" / "is he walking?" / "he isn't walking"

## References
- GF ResEng.gf: mkClause, nonAuxVerbForms, auxVerbForms, predV
- GF SentenceEng.gf: PredVP, UseCl
- GF NounEng.gf: DetCN, UseN, MassNP
-/

import Mettapedia.Languages.GF.English.Nouns
import Mettapedia.Languages.GF.English.Verbs
import Mettapedia.Languages.GF.English.Adjectives

namespace Mettapedia.Languages.GF.English.Syntax

open Mettapedia.Languages.GF.English
open Nouns Verbs Adjectives

/-! ## Concrete Types

Type abbreviations for GF abstract categories mapped to English concrete types.
-/

/-- English common noun in concrete syntax -/
abbrev EnglishCN := EnglishNoun

/-- English NP: a function from NPCase to surface form + agreement -/
structure EnglishNP where
  s : NPCase → String
  agr : Agr

/-- English determiner: carries string form, number, and whether it's definite -/
structure EnglishDet where
  s : String
  n : Number
  isDef : Bool

/-- English AP: adjective phrase (may be pre-nominal or post-nominal) -/
structure EnglishAP where
  s : Agr → String
  isPre : Bool  -- true = prenominal ("big cat"), false = postnominal ("something big")

/-! ## Verb Phrase

Simplified VP type: stores the verb's key forms and complement.
-/

/-- English VP: verb forms + complement + adverb.
    Simplified from ResEng.gf's complex VP record. -/
structure EnglishVP where
  inf : String        -- infinitive: "walk"
  pres : Agr → String -- present tense: "walks"/"walk"
  past : String       -- past tense: "walked"
  ppart : String      -- past participle: "walked"
  prpart : String     -- present participle: "walking"
  particle : String   -- verb particle: "up" in "give up"
  compl : Agr → String -- complement/object
  adv : String        -- adverb

/-- Build VP from a verb (no complement) -/
def predV (v : EnglishVerb) : EnglishVP :=
  { inf := v.s .VInf
    pres := fun agr => agrVerb (v.s .VPres) (v.s .VInf) agr
    past := v.s .VPast
    ppart := v.s .VPPart
    prpart := v.s .VPresPart
    particle := v.p
    compl := fun agr => if v.isRefl then reflPron agr else ""
    adv := "" }

/-- Add a direct object NP to a VP -/
def complVP (vp : EnglishVP) (obj : EnglishNP) : EnglishVP :=
  { vp with compl := fun _ => obj.s .NPAcc }

/-- Add an adverb to a VP -/
def advVP (vp : EnglishVP) (adv : String) : EnglishVP :=
  { vp with adv := if vp.adv == "" then adv else vp.adv ++ " " ++ adv }

/-! ## VP Slash (Two-Place Verbs)

A VPSlash is a VP with a missing NP argument.
Ported from ResEng.gf: `SlashVP = VP ** {c2 : Str}`.
-/

/-- VP with a missing NP complement (slash category) -/
structure EnglishVPSlash extends EnglishVP where
  c2 : String  -- complement preposition

/-- Build VPSlash from a V2 -/
def slashV2a (v : EnglishV2) : EnglishVPSlash :=
  { (predV v.toEnglishVerb) with c2 := v.c2 }

/-- Fill the slash: VPSlash + NP → VP.
    Adds the object (with preposition if any) as complement. -/
def complSlash (vps : EnglishVPSlash) (obj : EnglishNP) : EnglishVP :=
  let objStr := if vps.c2 == "" then obj.s .NPAcc
                else vps.c2 ++ " " ++ obj.s .NPAcc
  { vps.toEnglishVP with compl := fun _ => objStr }

/-- Shortcut: V2 + NP → VP (combines slashV2a and complSlash) -/
def complV2 (v : EnglishV2) (obj : EnglishNP) : EnglishVP :=
  complSlash (slashV2a v) obj

/-! ## Clause Construction

The heart of English syntax: assembles subject, verb forms, and complements
with correct word order for declaratives and questions.
-/

/-- Helper: concatenate non-empty strings with spaces -/
def joinWords (parts : List String) : String :=
  (parts.filter (· ≠ "")).intersperse " " |>.foldl (· ++ ·) ""

/-- Construct a declarative clause (SVO order).
    "he walks", "he has walked", "he doesn't walk", "he will walk" -/
def mkDeclClause (subj : String) (vp : EnglishVP) (agr : Agr)
    (t : Tense) (ant : Anteriority) (pol : CPolarity) : String :=
  match t, ant, pol with
  -- Present simple positive: "he walks"
  | .Pres, .Simul, .CPos =>
    joinWords [subj, vp.pres agr, vp.particle, vp.compl agr, vp.adv]
  -- Present simple negative: "he doesn't walk" / "he does not walk"
  | .Pres, .Simul, .CNeg contracted =>
    let aux := if contracted then auxDo.pres .Neg agr else auxDo.pres .Pos agr
    let neg := if contracted then "" else "not"
    joinWords [subj, aux, neg, vp.inf, vp.particle, vp.compl agr, vp.adv]
  -- Present perfect positive: "he has walked"
  | .Pres, .Anter, .CPos =>
    joinWords [subj, agrVerb "has" "have" agr, vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Present perfect negative: "he hasn't walked"
  | .Pres, .Anter, .CNeg contracted =>
    let aux := if contracted then agrVerb "hasn't" "haven't" agr
               else agrVerb "has" "have" agr
    let neg := if contracted then "" else "not"
    joinWords [subj, aux, neg, vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Past simple positive: "he walked"
  | .Past, .Simul, .CPos =>
    joinWords [subj, vp.past, vp.particle, vp.compl agr, vp.adv]
  -- Past simple negative: "he didn't walk"
  | .Past, .Simul, .CNeg contracted =>
    let aux := if contracted then "didn't" else "did"
    let neg := if contracted then "" else "not"
    joinWords [subj, aux, neg, vp.inf, vp.particle, vp.compl agr, vp.adv]
  -- Past perfect positive: "he had walked"
  | .Past, .Anter, .CPos =>
    joinWords [subj, "had", vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Past perfect negative: "he hadn't walked"
  | .Past, .Anter, .CNeg contracted =>
    let aux := if contracted then "hadn't" else "had"
    let neg := if contracted then "" else "not"
    joinWords [subj, aux, neg, vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Future simple positive: "he will walk"
  | .Fut, .Simul, .CPos =>
    joinWords [subj, "will", vp.inf, vp.particle, vp.compl agr, vp.adv]
  -- Future simple negative: "he won't walk"
  | .Fut, .Simul, .CNeg contracted =>
    let aux := if contracted then "won't" else "will"
    let neg := if contracted then "" else "not"
    joinWords [subj, aux, neg, vp.inf, vp.particle, vp.compl agr, vp.adv]
  -- Future perfect positive: "he will have walked"
  | .Fut, .Anter, .CPos =>
    joinWords [subj, "will", "have", vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Future perfect negative: "he won't have walked"
  | .Fut, .Anter, .CNeg contracted =>
    let aux := if contracted then "won't" else "will"
    let neg := if contracted then "" else "not"
    joinWords [subj, aux, neg, "have", vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Conditional simple positive: "he would walk"
  | .Cond, .Simul, .CPos =>
    joinWords [subj, "would", vp.inf, vp.particle, vp.compl agr, vp.adv]
  -- Conditional simple negative: "he wouldn't walk"
  | .Cond, .Simul, .CNeg contracted =>
    let aux := if contracted then "wouldn't" else "would"
    let neg := if contracted then "" else "not"
    joinWords [subj, aux, neg, vp.inf, vp.particle, vp.compl agr, vp.adv]
  -- Conditional perfect positive: "he would have walked"
  | .Cond, .Anter, .CPos =>
    joinWords [subj, "would", "have", vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Conditional perfect negative: "he wouldn't have walked"
  | .Cond, .Anter, .CNeg contracted =>
    let aux := if contracted then "wouldn't" else "would"
    let neg := if contracted then "" else "not"
    joinWords [subj, aux, neg, "have", vp.ppart, vp.particle, vp.compl agr, vp.adv]

/-- Construct a question clause (aux-subject inversion).
    "does he walk?", "has he walked?", "will he walk?" -/
def mkQuestClause (subj : String) (vp : EnglishVP) (agr : Agr)
    (t : Tense) (ant : Anteriority) (pol : CPolarity) : String :=
  match t, ant, pol with
  -- Present simple: "does he walk?"
  | .Pres, .Simul, .CPos =>
    joinWords [auxDo.pres .Pos agr, subj, vp.inf, vp.particle, vp.compl agr, vp.adv]
  -- Present simple neg: "doesn't he walk?"
  | .Pres, .Simul, .CNeg contracted =>
    let aux := if contracted then auxDo.pres .Neg agr else auxDo.pres .Pos agr
    let neg := if contracted then "" else "not"
    joinWords [aux, subj, neg, vp.inf, vp.particle, vp.compl agr, vp.adv]
  -- Present perfect: "has he walked?"
  | .Pres, .Anter, .CPos =>
    joinWords [agrVerb "has" "have" agr, subj, vp.ppart, vp.particle, vp.compl agr, vp.adv]
  | .Pres, .Anter, .CNeg contracted =>
    let aux := if contracted then agrVerb "hasn't" "haven't" agr
               else agrVerb "has" "have" agr
    let neg := if contracted then "" else "not"
    joinWords [aux, subj, neg, vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Past simple: "did he walk?"
  | .Past, .Simul, .CPos =>
    joinWords ["did", subj, vp.inf, vp.particle, vp.compl agr, vp.adv]
  | .Past, .Simul, .CNeg contracted =>
    let aux := if contracted then "didn't" else "did"
    let neg := if contracted then "" else "not"
    joinWords [aux, subj, neg, vp.inf, vp.particle, vp.compl agr, vp.adv]
  -- Past perfect: "had he walked?"
  | .Past, .Anter, .CPos =>
    joinWords ["had", subj, vp.ppart, vp.particle, vp.compl agr, vp.adv]
  | .Past, .Anter, .CNeg contracted =>
    let aux := if contracted then "hadn't" else "had"
    let neg := if contracted then "" else "not"
    joinWords [aux, subj, neg, vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Future: "will he walk?"
  | .Fut, .Simul, .CPos =>
    joinWords ["will", subj, vp.inf, vp.particle, vp.compl agr, vp.adv]
  | .Fut, .Simul, .CNeg contracted =>
    let aux := if contracted then "won't" else "will"
    let neg := if contracted then "" else "not"
    joinWords [aux, subj, neg, vp.inf, vp.particle, vp.compl agr, vp.adv]
  | .Fut, .Anter, .CPos =>
    joinWords ["will", subj, "have", vp.ppart, vp.particle, vp.compl agr, vp.adv]
  | .Fut, .Anter, .CNeg contracted =>
    let aux := if contracted then "won't" else "will"
    let neg := if contracted then "" else "not"
    joinWords [aux, subj, neg, "have", vp.ppart, vp.particle, vp.compl agr, vp.adv]
  -- Conditional: "would he walk?"
  | .Cond, .Simul, .CPos =>
    joinWords ["would", subj, vp.inf, vp.particle, vp.compl agr, vp.adv]
  | .Cond, .Simul, .CNeg contracted =>
    let aux := if contracted then "wouldn't" else "would"
    let neg := if contracted then "" else "not"
    joinWords [aux, subj, neg, vp.inf, vp.particle, vp.compl agr, vp.adv]
  | .Cond, .Anter, .CPos =>
    joinWords ["would", subj, "have", vp.ppart, vp.particle, vp.compl agr, vp.adv]
  | .Cond, .Anter, .CNeg contracted =>
    let aux := if contracted then "wouldn't" else "would"
    let neg := if contracted then "" else "not"
    joinWords [aux, subj, neg, "have", vp.ppart, vp.particle, vp.compl agr, vp.adv]

/-- Full clause construction with word order dispatch.
    Ported from ResEng.gf `mkClause`. -/
structure EnglishClause where
  s : Tense → Anteriority → CPolarity → Order → String

def mkClause (subj : String) (agr : Agr) (vp : EnglishVP) : EnglishClause :=
  { s := fun t ant pol ord => match ord with
      | .ODir _ => mkDeclClause subj vp agr t ant pol
      | .OQuest => mkQuestClause subj vp agr t ant pol }

/-! ## Key Linearization Functions

These implement the GF abstract-to-concrete mapping for English.
-/

/-- Articles -/
def theDefArt : EnglishDet := { s := "the", n := .Sg, isDef := true }
def theDefArtPl : EnglishDet := { s := "the", n := .Pl, isDef := true }

/-- Indefinite article with a/an heuristic.
    Simplified: "an" before vowel, "a" otherwise. -/
def aIndefArt : EnglishDet :=
  { s := "a", n := .Sg, isDef := false }  -- a/an selection deferred to linDetCN

/-- Select "a" vs "an" based on first character of following word -/
def articleAn (nextWord : String) : String :=
  match nextWord.toList.head? with
  | some c => if isVowel c then "an" else "a"
  | none => "a"

/-- DetCN: combine determiner with common noun to make NP.
    "the cat", "a dog", "the big cats" -/
def linDetCN (det : EnglishDet) (cn : EnglishCN) : EnglishNP :=
  let nomForm := cn.s det.n .Nom
  let detStr := if !det.isDef && det.n == .Sg then articleAn nomForm else det.s
  { s := fun npc => match npc with
      | .NCase c => detStr ++ " " ++ cn.s det.n c
      | .NPAcc => detStr ++ " " ++ cn.s det.n .Nom
      | .NPNomPoss => detStr ++ " " ++ cn.s det.n .Gen
    agr := match det.n with
      | .Sg => .AgP3Sg cn.g
      | .Pl => .AgP3Pl }

/-- UseN: bare noun as CN (identity in English, like Czech) -/
def linUseN (n : EnglishNoun) : EnglishCN := n

/-- MassNP: mass/bare noun as NP (no article): "water", "music" -/
def linMassNP (cn : EnglishCN) : EnglishNP :=
  { s := fun npc => match npc with
      | .NCase c => cn.s .Sg c
      | .NPAcc => cn.s .Sg .Nom
      | .NPNomPoss => cn.s .Sg .Gen
    agr := .AgP3Sg cn.g }

/-- AdjCN: adjective modifying a noun.
    "big cat" (prenominal), "something big" (postnominal) -/
def linAdjCN (ap : EnglishAP) (cn : EnglishCN) : EnglishCN :=
  let adjStr := ap.s (.AgP3Sg cn.g)
  { s := fun n c =>
      if ap.isPre then adjStr ++ " " ++ cn.s n c
      else cn.s n c ++ " " ++ adjStr
    g := cn.g }

/-- PositA: adjective in positive degree as AP -/
def linPositA (a : EnglishAdj) : EnglishAP :=
  { s := fun _ => a.s (.AAdj .Pos .Nom)
    isPre := true }

/-- ComparA: comparative adjective as AP ("bigger than") -/
def linComparA (a : EnglishAdj) : EnglishAP :=
  { s := fun _ => a.s (.AAdj .Comp .Nom)
    isPre := true }

/-- PredVP: subject NP + verb phrase → clause.
    "the cat walks", "they have eaten" -/
def linPredVP (subj : EnglishNP) (vp : EnglishVP) : EnglishClause :=
  mkClause (subj.s (.NCase .Nom)) subj.agr vp

/-- UseCl: clause → sentence string (fixes tense, polarity, etc.) -/
def linUseCl (t : Tense) (ant : Anteriority) (pol : CPolarity) (cl : EnglishClause) : String :=
  cl.s t ant pol (.ODir true)

/-- QuestCl: clause → question string -/
def linQuestCl (t : Tense) (ant : Anteriority) (pol : CPolarity) (cl : EnglishClause) : String :=
  cl.s t ant pol .OQuest

/-! ## Tests -/

-- Build some test NPs and VPs
private def theCat := linDetCN theDefArt (linUseN cat_N)
private def aDog := linDetCN aIndefArt (linUseN dog_N)
private def theMan := linDetCN theDefArt (linUseN man_N)
private def theBigCat := linDetCN theDefArt (linAdjCN (linPositA big_A) (linUseN cat_N))
private def walkVP := predV walk_V
private def sleepVP := predV sleep_V
private def eatVP := predV eat_V

-- NP surface forms
#eval! theCat.s (.NCase .Nom)    -- "the cat"
#eval! theCat.s (.NCase .Gen)    -- "the cat's"
#eval! aDog.s (.NCase .Nom)      -- "a dog"
#eval! theBigCat.s (.NCase .Nom) -- "the big cat"
#eval! theMan.s (.NCase .Nom)    -- "the man"

-- Declarative sentences
#eval! linUseCl .Pres .Simul .CPos (linPredVP theCat walkVP)
  -- "the cat walks"
#eval! linUseCl .Pres .Simul (.CNeg true) (linPredVP theCat walkVP)
  -- "the cat doesn't walk"
#eval! linUseCl .Past .Simul .CPos (linPredVP theCat walkVP)
  -- "the cat walked"
#eval! linUseCl .Fut .Simul .CPos (linPredVP theCat walkVP)
  -- "the cat will walk"
#eval! linUseCl .Pres .Anter .CPos (linPredVP theCat walkVP)
  -- "the cat has walked"
#eval! linUseCl .Cond .Simul .CPos (linPredVP theCat walkVP)
  -- "the cat would walk"

-- Questions
#eval! linQuestCl .Pres .Simul .CPos (linPredVP theCat walkVP)
  -- "does the cat walk"
#eval! linQuestCl .Past .Simul .CPos (linPredVP theCat walkVP)
  -- "did the cat walk"
#eval! linQuestCl .Fut .Simul .CPos (linPredVP theCat walkVP)
  -- "will the cat walk"

-- Irregular verbs
#eval! linUseCl .Past .Simul .CPos (linPredVP theMan (predV eat_V))
  -- "the man ate"
#eval! linUseCl .Pres .Anter .CPos (linPredVP theMan (predV eat_V))
  -- "the man has eaten"

-- a/an selection
private def anApple := linDetCN aIndefArt (linUseN (regN "apple"))
#eval! anApple.s (.NCase .Nom)  -- "an apple"

/-! ## Correctness Properties -/

/-- linUseN is identity -/
theorem linUseN_id (n : EnglishNoun) : linUseN n = n := rfl

/-- predV preserves infinitive -/
theorem predV_inf (v : EnglishVerb) : (predV v).inf = v.s .VInf := rfl

/-- predV preserves past participle -/
theorem predV_ppart (v : EnglishVerb) : (predV v).ppart = v.s .VPPart := rfl

/-- Positive declarative present uses finite verb form directly -/
theorem mkDeclClause_pres_pos (subj : String) (vp : EnglishVP) (agr : Agr) :
    mkDeclClause subj vp agr .Pres .Simul .CPos =
    joinWords [subj, vp.pres agr, vp.particle, vp.compl agr, vp.adv] := rfl

/-- Question present uses do-support -/
theorem mkQuestClause_pres_pos (subj : String) (vp : EnglishVP) (agr : Agr) :
    mkQuestClause subj vp agr .Pres .Simul .CPos =
    joinWords [auxDo.pres .Pos agr, subj, vp.inf, vp.particle, vp.compl agr, vp.adv] := rfl

end Mettapedia.Languages.GF.English.Syntax
