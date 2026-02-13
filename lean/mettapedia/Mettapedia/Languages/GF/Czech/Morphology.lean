/-
# Czech Morphology

Core Czech morphological parameters and noun declension.

Czech nouns inflect for:
- 7 cases (Nom, Gen, Dat, Acc, Voc, Loc, Ins)
- 2 numbers (Sg, Pl)
- 4 genders (Masc animate, Masc inanimate, Fem, Neutr)

Despite 14 theoretical slots (7 cases × 2 numbers), most nouns use <10 distinct forms
due to syncretism, demonstrating the compression paradox.

## References
- GF Czech Resource: ~/claude/gf-rgl/src/czech/ResCze.gf
- Grammar compression analysis: ~/claude/grammar_compression_FAIR.txt
-/

import Mettapedia.Languages.GF.Core
import Mettapedia.Languages.GF.Concrete

namespace Mettapedia.Languages.GF.Czech

open Core Concrete

/-! ## Czech Parameters

Morphological features as inductive types (not predicates!).
This follows the field-based encoding pattern from SUMO work.
-/

/-- Czech grammatical cases -/
inductive Case where
  | Nom  -- Nominative (subject)
  | Gen  -- Genitive (possession, after numbers)
  | Dat  -- Dative (indirect object)
  | Acc  -- Accusative (direct object)
  | Voc  -- Vocative (addressing)
  | Loc  -- Locative (location, with prepositions)
  | Ins  -- Instrumental (means, with)
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical number -/
inductive Number where
  | Sg  -- Singular
  | Pl  -- Plural
  deriving DecidableEq, Repr, Inhabited

/-- Czech grammatical gender (with animacy for masculine) -/
inductive Gender where
  | MascAnim    -- Masculine animate (man, teacher)
  | MascInanim  -- Masculine inanimate (table, house)
  | Fem         -- Feminine (woman, book)
  | Neutr       -- Neuter (city, window)
  deriving DecidableEq, Repr, Inhabited

/-- Declension paradigms (based on GF ResCze.gf patterns).
    Named after canonical exemplar nouns, matching GF convention. -/
inductive DeclensionType where
  | pan        -- pán: masculine animate hard (pán, kluk, doktor)
  | predseda   -- předseda: masculine animate -a (předseda, kolega)
  | soudce     -- soudce: masculine animate -ce (soudce, průvodce)
  | hrad       -- hrad: masculine inanimate hard (hrad, dům, stůl)
  | muz        -- muž: masculine animate soft (muž, učitel)
  | stroj      -- stroj: masculine inanimate soft (stroj, počítač)
  | zena       -- žena: feminine -a (žena, kniha, škola)
  | ruze       -- růže: feminine -e soft (růže, ulice)
  | pisen      -- píseň: feminine soft consonant (píseň, báseň)
  | kost       -- kost: feminine -ost (kost, radost)
  | mesto      -- město: neuter -o (město, okno, auto)
  | kure       -- kuře: neuter -e/-ete (kuře, zvíře)
  | more       -- moře: neuter soft -e (moře, pole)
  | staveni    -- stavení: neuter -í invariant (stavení, náměstí)
  | irregular  -- Irregular nouns
  deriving DecidableEq, Repr, Inhabited

/-! ## Grammatical Person and Agreement

Used for verb conjugation, pronoun selection, and numeral agreement.
-/

/-- Grammatical person -/
inductive Person where
  | P1  -- First person (I, we)
  | P2  -- Second person (you)
  | P3  -- Third person (he, she, it, they)
  deriving DecidableEq, Repr, Inhabited

/-- Agreement features: Gender x Number x Person.
    Used for verb-subject agreement and pronoun reference. -/
structure Agr where
  gender : Gender
  number : Number
  person : Person
  deriving DecidableEq, Repr, Inhabited

/-- Numeral size governing noun agreement (CEG 6.1).
    Czech numerals change how the governed noun inflects. -/
inductive NumSize where
  | Num1    -- 1: singular agreement
  | Num2_4  -- 2-4: plural agreement
  | Num5    -- 5+: forces genitive plural for Nom/Acc
  deriving DecidableEq, Repr, Inhabited

/-! ## Parameter Sets

Combined parameter structures for different parts of speech.
-/

/-- Complete parameter set for Czech adjective inflection.
    Adjectives agree with their noun in gender, number, and case. -/
structure AdjParams where
  gender : Gender
  number : Number
  case : Case
  deriving DecidableEq, Repr, Inhabited

namespace AdjParams

/-- All 56 possible adjective parameter combinations (4 genders x 2 numbers x 7 cases) -/
def allForms : List AdjParams :=
  ([Gender.MascAnim, Gender.MascInanim, Gender.Fem, Gender.Neutr].map fun g =>
    [Number.Sg, Number.Pl].map fun n =>
      [Case.Nom, Case.Gen, Case.Dat, Case.Acc, Case.Voc, Case.Loc, Case.Ins].map fun c =>
        ⟨g, n, c⟩).flatten.flatten

end AdjParams

/-! ## Czech Noun Parameters

Combined parameters for noun inflection.
-/

/-- Complete parameter set for Czech noun inflection -/
structure CzechParams where
  case : Case
  number : Number
  deriving DecidableEq, Repr, Inhabited

namespace CzechParams

/-- All 14 possible parameter combinations -/
def allForms : List CzechParams :=
  ([Case.Nom, Case.Gen, Case.Dat, Case.Acc, Case.Voc, Case.Loc, Case.Ins].map fun c =>
    [Number.Sg, Number.Pl].map fun n => ⟨c, n⟩).flatten

end CzechParams

/-! ## Czech Noun Structure

A Czech noun with intrinsic features (SUMO-style field encoding).
-/

/-- Czech noun with inherent morphological features -/
structure CzechNoun where
  /-- Base form (lemma) - typically nominative singular -/
  lemma : String
  /-- Grammatical gender (inherent) -/
  gender : Gender
  /-- Declension pattern this noun follows -/
  declension : DeclensionType
  deriving DecidableEq, Repr

/-! ## Stem Extraction

Extract stem from lemma based on declension type.
-/

/-! ## Kernel-Reducible String Helpers

Using List Char operations so `decide` can reduce proofs.
-/

/-- Check if string ends with suffix (kernel-reducible) -/
def strEndsWith (s : String) (suffix : String) : Bool :=
  let cs := s.toList
  let sufl := suffix.toList
  cs.length >= sufl.length && cs.drop (cs.length - sufl.length) == sufl

/-- Drop last n characters (kernel-reducible) -/
def strDropEnd (s : String) (n : Nat) : String :=
  String.ofList (s.toList.take (s.toList.length - n))

namespace Stem

/-- Extract stem for feminine -a nouns (žena → žen) -/
def feminineA (lemma : String) : String :=
  if strEndsWith lemma "a" then strDropEnd lemma 1 else lemma

/-- Extract stem for neuter -o nouns (město → měst) -/
def neuterO (lemma : String) : String :=
  if strEndsWith lemma "o" then strDropEnd lemma 1 else lemma

end Stem

/-! ## Note on Declension

The main declension function `declineFull` is in Declensions.lean,
which dispatches to per-paradigm functions (declinePAN, declineHRAD, etc.).
-/

end Mettapedia.Languages.GF.Czech
