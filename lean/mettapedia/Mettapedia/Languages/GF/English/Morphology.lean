/-
# English Morphology

Core English morphological parameters and structures.

English is morphologically simpler than Czech:
- 2 cases (Nom, Gen) vs Czech's 7
- 4 noun forms (sg/pl × nom/gen) vs Czech's 14
- 5 verb base forms (inf, pres3sg, past, ppart, prpart)
- Fixed SVO word order (vs Czech's free order)
- Articles (a/an, the) — Czech has none

## References
- GF English Resource: ~/claude/gf-rgl/src/english/ResEng.gf
- GF English Categories: ~/claude/gf-rgl/src/english/CatEng.gf
- GF English Paradigms: ~/claude/gf-rgl/src/english/ParadigmsEng.gf
-/

import Mettapedia.Languages.GF.Core

namespace Mettapedia.Languages.GF.English

open Core

/-! ## English Parameters

Morphological features as inductive types, directly ported from ResEng.gf.
-/

/-- English grammatical case (only 2, vs Czech's 7) -/
inductive Case where
  | Nom  -- Nominative (subject, default)
  | Gen  -- Genitive (possessive: cat's, men's)
  deriving DecidableEq, Repr, Inhabited

/-- NP case forms (4 distinct forms for pronouns: he/him/his/mine) -/
inductive NPCase where
  | NCase (c : Case)  -- Nominative or genitive
  | NPAcc             -- Accusative (him, her, them)
  | NPNomPoss         -- Possessive pronoun standalone (mine, yours, theirs)
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical gender (for pronouns and agreement) -/
inductive Gender where
  | Neutr  -- Neuter (it)
  | Masc   -- Masculine (he)
  | Fem    -- Feminine (she)
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical number -/
inductive Number where
  | Sg  -- Singular
  | Pl  -- Plural
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical person -/
inductive Person where
  | P1  -- First person (I, we)
  | P2  -- Second person (you)
  | P3  -- Third person (he, she, it, they)
  deriving DecidableEq, Repr, Inhabited

/-- Agreement: 8 values (3 persons × 2 numbers, with gender for 3rd person).
    ResEng.gf: `Agr = AgP1 Number | AgP2 Number | AgP3Sg Gender | AgP3Pl` -/
inductive Agr where
  | AgP1 (n : Number)   -- I / we
  | AgP2 (n : Number)   -- you (sg) / you (pl)
  | AgP3Sg (g : Gender)  -- he / she / it
  | AgP3Pl               -- they
  deriving DecidableEq, Repr, Inhabited

/-- Extract number from agreement -/
def Agr.number : Agr → Number
  | .AgP1 n | .AgP2 n => n
  | .AgP3Sg _ => .Sg
  | .AgP3Pl => .Pl

/-- Extract person from agreement -/
def Agr.person : Agr → Person
  | .AgP1 _ => .P1
  | .AgP2 _ => .P2
  | .AgP3Sg _ | .AgP3Pl => .P3

/-! ## Verb Forms -/

/-- The 5 base verb forms (VInf, VPres, VPPart, VPresPart, VPast).
    From these + auxiliaries, all tenses are constructed. -/
inductive VForm where
  | VInf       -- Infinitive: "walk", "go"
  | VPres      -- 3rd person singular present: "walks", "goes"
  | VPPart     -- Past participle: "walked", "gone"
  | VPresPart  -- Present participle: "walking", "going"
  | VPast      -- Past tense: "walked", "went"
  deriving DecidableEq, Repr, Inhabited

/-- VV (control verb) forms: base + negation variants -/
inductive VVForm where
  | VVF (v : VForm)  -- Standard verb form
  | VVPresNeg         -- Present negation
  | VVPastNeg         -- Past negation
  deriving DecidableEq, Repr, Inhabited

/-- Control verb type (what complement form it takes) -/
inductive VVType where
  | VVAux       -- Bare infinitive: "can walk"
  | VVInf       -- To-infinitive: "want to walk"
  | VVPresPart  -- Gerund: "enjoy walking"
  deriving DecidableEq, Repr, Inhabited

/-! ## Adjective Forms -/

/-- Degree of comparison -/
inductive Degree where
  | Pos    -- Positive: "big"
  | Comp   -- Comparative: "bigger"
  | Super  -- Superlative: "biggest"
  deriving DecidableEq, Repr, Inhabited

/-- Adjective form: degree × case (for nominalization) or adverb -/
inductive AForm where
  | AAdj (d : Degree) (c : Case)  -- Adjectival: "big" (Nom), "big" (Gen)
  | AAdv                           -- Adverbial: "bigly" / "beautifully"
  deriving DecidableEq, Repr, Inhabited

/-! ## Tense and Aspect -/

/-- Tense -/
inductive Tense where
  | Pres  -- Present
  | Past  -- Past
  | Fut   -- Future
  | Cond  -- Conditional
  deriving DecidableEq, Repr, Inhabited

/-- Anteriority (simple vs perfect) -/
inductive Anteriority where
  | Simul  -- Simple: "walks", "walked"
  | Anter  -- Perfect: "has walked", "had walked"
  deriving DecidableEq, Repr, Inhabited

/-- Polarity with contraction support -/
inductive CPolarity where
  | CPos                      -- Positive: "walks"
  | CNeg (contracted : Bool)  -- Negative: "doesn't walk" vs "does not walk"
  deriving DecidableEq, Repr, Inhabited

/-- Simple polarity (no contraction distinction) -/
inductive Polarity where
  | Pos  -- Positive
  | Neg  -- Negative
  deriving DecidableEq, Repr, Inhabited

/-- Word order -/
inductive Order where
  | ODir (hasSubj : Bool)  -- Declarative: "he walks" (true=has subject)
  | OQuest                 -- Question: "does he walk?"
  deriving DecidableEq, Repr, Inhabited

/-- Question form -/
inductive QForm where
  | QDir    -- Direct question: "Does he walk?"
  | QIndir  -- Indirect question: "whether he walks"
  deriving DecidableEq, Repr, Inhabited

/-- Imperative form -/
inductive ImpForm where
  | ImpF (n : Number) (pol : Polarity)
  deriving DecidableEq, Repr, Inhabited

/-! ## Core Structures -/

/-- English noun: 4 forms (Number × Case) + inherent gender.
    CatEng.gf: `N = {s : Number => Case => Str ; g : Gender}` -/
structure EnglishNoun where
  s : Number → Case → String
  g : Gender

/-- English verb: 5 base forms + particle + reflexive flag.
    ResEng.gf: `Verb = {s : VForm => Str ; p : Str ; isRefl : Bool}` -/
structure EnglishVerb where
  s : VForm → String
  p : String       -- particle ("up" in "give up", "" for no particle)
  isRefl : Bool    -- reflexive flag

/-- English adjective: degree × case forms + adverb.
    ResEng.gf: `Adjective = {s : AForm => Str}` -/
structure EnglishAdj where
  s : AForm → String

/-! ## Parameter Structures -/

/-- Complete parameter set for English linearization -/
structure EnglishParams where
  case : Case
  number : Number
  deriving DecidableEq, Repr, Inhabited

namespace EnglishParams

/-- All 4 possible parameter combinations (2 cases × 2 numbers) -/
def allForms : List EnglishParams :=
  ([Case.Nom, Case.Gen].map fun c =>
    [Number.Sg, Number.Pl].map fun n => ⟨c, n⟩).flatten

end EnglishParams

/-! ## String Helpers (kernel-reducible for `decide`) -/

/-- Check if string ends with suffix -/
def strEndsWith (s : String) (suffix : String) : Bool :=
  let cs := s.toList
  let sufl := suffix.toList
  cs.length >= sufl.length && cs.drop (cs.length - sufl.length) == sufl

/-- Drop last n characters -/
def strDropEnd (s : String) (n : Nat) : String :=
  String.ofList (s.toList.take (s.toList.length - n))

/-- Get last character -/
def strLast (s : String) : Option Char :=
  s.toList.getLast?

/-- Get last n characters -/
def strTakeEnd (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop (s.toList.length - n))

/-- Check if character is a vowel -/
def isVowel (c : Char) : Bool :=
  c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']

/-- Check if character is a consonant letter -/
def isConsonant (c : Char) : Bool :=
  c.isAlpha && !isVowel c

end Mettapedia.Languages.GF.English
