/-
# English Pronouns and Structural Words

Personal pronouns, demonstratives, interrogatives, and key structural
words ported from GF StructuralEng.gf and MorphoEng.gf.

## References
- GF StructuralEng.gf: i_Pron, he_Pron, this_Det, who_IP, etc.
- GF MorphoEng.gf: mkPron, mkDeterminer
-/

import Mettapedia.Languages.GF.English.Syntax

namespace Mettapedia.Languages.GF.English.Pronouns

open Mettapedia.Languages.GF.English
open Syntax

/-! ## Pronoun Forms -/

/-- Build a pronoun NP from 4 case forms + agreement.
    Ported from MorphoEng.gf `mkPron`. -/
def mkPron (nom acc gen genPoss : String) (agr : Agr) : EnglishNP :=
  { s := fun npc => match npc with
      | .NCase .Nom => nom
      | .NCase .Gen => gen
      | .NPAcc => acc
      | .NPNomPoss => genPoss
    agr := agr }

/-! ## Personal Pronouns (StructuralEng.gf) -/

def i_Pron : EnglishNP := mkPron "I" "me" "my" "mine" (.AgP1 .Sg)
def we_Pron : EnglishNP := mkPron "we" "us" "our" "ours" (.AgP1 .Pl)
def youSg_Pron : EnglishNP := mkPron "you" "you" "your" "yours" (.AgP2 .Sg)
def youPl_Pron : EnglishNP := mkPron "you" "you" "your" "yours" (.AgP2 .Pl)
def he_Pron : EnglishNP := mkPron "he" "him" "his" "his" (.AgP3Sg .Masc)
def she_Pron : EnglishNP := mkPron "she" "her" "her" "hers" (.AgP3Sg .Fem)
def it_Pron : EnglishNP := mkPron "it" "it" "its" "its" (.AgP3Sg .Neutr)
def they_Pron : EnglishNP := mkPron "they" "them" "their" "theirs" .AgP3Pl

/-! ## Demonstrative Determiners -/

def this_Det : EnglishDet := { s := "this", n := .Sg, isDef := true }
def that_Det : EnglishDet := { s := "that", n := .Sg, isDef := true }
def these_Det : EnglishDet := { s := "these", n := .Pl, isDef := true }
def those_Det : EnglishDet := { s := "those", n := .Pl, isDef := true }

/-! ## Quantifier Determiners -/

def every_Det : EnglishDet := { s := "every", n := .Sg, isDef := false }
def some_Det : EnglishDet := { s := "some", n := .Sg, isDef := false }
def no_Det : EnglishDet := { s := "no", n := .Sg, isDef := false }
def many_Det : EnglishDet := { s := "many", n := .Pl, isDef := false }
def few_Det : EnglishDet := { s := "few", n := .Pl, isDef := false }

/-! ## Interrogative Pronouns -/

/-- Interrogative NP: who/what/which -/
structure EnglishIP where
  s : NPCase → String
  n : Number

def who_IP : EnglishIP :=
  { s := fun npc => match npc with
      | .NCase .Nom => "who"
      | .NPAcc => "whom"
      | .NCase .Gen | .NPNomPoss => "whose"
    n := .Sg }

def what_IP : EnglishIP :=
  { s := fun _ => "what", n := .Sg }

/-! ## Prepositions -/

/-- English preposition (may be pre- or post-positional) -/
structure EnglishPrep where
  s : String
  isPre : Bool  -- true = preposition, false = postposition

def mkPrep (s : String) : EnglishPrep := { s := s, isPre := true }
def mkPost (s : String) : EnglishPrep := { s := s, isPre := false }

-- Common prepositions
def in_Prep : EnglishPrep := mkPrep "in"
def on_Prep : EnglishPrep := mkPrep "on"
def to_Prep : EnglishPrep := mkPrep "to"
def from_Prep : EnglishPrep := mkPrep "from"
def with_Prep : EnglishPrep := mkPrep "with"
def by_Prep : EnglishPrep := mkPrep "by"
def for_Prep : EnglishPrep := mkPrep "for"
def of_Prep : EnglishPrep := mkPrep "of"
def at_Prep : EnglishPrep := mkPrep "at"
def ago_Post : EnglishPrep := mkPost "ago"

/-- PrepNP: preposition + NP -/
def linPrepNP (prep : EnglishPrep) (np : EnglishNP) : String :=
  if prep.isPre then prep.s ++ " " ++ np.s .NPAcc
  else np.s .NPAcc ++ " " ++ prep.s

/-! ## Conjunctions -/

structure EnglishConj where
  s1 : String  -- first part (empty for simple conjunctions)
  s2 : String  -- main conjunction word
  n : Number   -- resulting number

def and_Conj : EnglishConj := { s1 := "", s2 := "and", n := .Pl }
def or_Conj : EnglishConj := { s1 := "", s2 := "or", n := .Sg }
def both_and_Conj : EnglishConj := { s1 := "both", s2 := "and", n := .Pl }
def either_or_Conj : EnglishConj := { s1 := "either", s2 := "or", n := .Sg }
def neither_nor_Conj : EnglishConj := { s1 := "neither", s2 := "nor", n := .Sg }

/-! ## Subjunctions (Subordinating Conjunctions)

"when", "if", "because", etc. — turn a sentence into an adverbial clause.
Ported from GF StructuralEng.gf and Adverb.gf.
-/

/-- Subordinating conjunction -/
structure EnglishSubj where
  s : String

def when_Subj : EnglishSubj := { s := "when" }
def if_Subj : EnglishSubj := { s := "if" }
def because_Subj : EnglishSubj := { s := "because" }
def although_Subj : EnglishSubj := { s := "although" }
def that_Subj : EnglishSubj := { s := "that" }
def before_Subj : EnglishSubj := { s := "before" }
def after_Subj : EnglishSubj := { s := "after" }
def while_Subj : EnglishSubj := { s := "while" }

/-- SubjS: subordinate clause as adverb string.
    "when she sleeps", "if the cat walks" -/
def linSubjS (subj : EnglishSubj) (s : String) : String :=
  subj.s ++ " " ++ s

/-- SSubjS: main clause + subordinate clause.
    "he walks if she sleeps", "the cat runs because the dog barks" -/
def linSSubjS (s1 : String) (subj : EnglishSubj) (s2 : String) : String :=
  s1 ++ " " ++ subj.s ++ " " ++ s2

/-! ## Tests -/

-- Pronouns
#eval! i_Pron.s (.NCase .Nom)    -- "I"
#eval! i_Pron.s .NPAcc            -- "me"
#eval! i_Pron.s (.NCase .Gen)    -- "my"
#eval! i_Pron.s .NPNomPoss        -- "mine"
#eval! he_Pron.s (.NCase .Nom)   -- "he"
#eval! she_Pron.s .NPAcc          -- "her"
#eval! they_Pron.s (.NCase .Gen) -- "their"

-- Demonstratives with nouns
#eval! (linDetCN this_Det (linUseN Nouns.cat_N)).s (.NCase .Nom)  -- "this cat"
#eval! (linDetCN these_Det (linUseN Nouns.cat_N)).s (.NCase .Nom) -- "these cats"
#eval! (linDetCN that_Det (linUseN Nouns.dog_N)).s (.NCase .Nom)  -- "that dog"

-- Pronoun sentences
#eval! linUseCl .Pres .Simul .CPos (linPredVP he_Pron (predV Verbs.walk_V))
  -- "he walks"
#eval! linUseCl .Pres .Simul .CPos (linPredVP they_Pron (predV Verbs.walk_V))
  -- "they walk"
#eval! linUseCl .Pres .Simul (.CNeg true) (linPredVP she_Pron (predV Verbs.sleep_V))
  -- "she doesn't sleep"

-- Prepositions
#eval! linPrepNP in_Prep (linDetCN theDefArt (linUseN Nouns.house_N))
  -- "in the house"
#eval! linPrepNP with_Prep he_Pron
  -- "with him"

-- Interrogatives
#eval! who_IP.s (.NCase .Nom)  -- "who"
#eval! who_IP.s .NPAcc          -- "whom"
#eval! who_IP.s (.NCase .Gen)  -- "whose"

/-! ## Correctness Properties -/

/-- mkPron nominative = first argument -/
theorem mkPron_nom (a b c d : String) (agr : Agr) :
    (mkPron a b c d agr).s (.NCase .Nom) = a := rfl

/-- mkPron accusative = second argument -/
theorem mkPron_acc (a b c d : String) (agr : Agr) :
    (mkPron a b c d agr).s .NPAcc = b := rfl

-- Concrete tests
theorem test_I : i_Pron.s (.NCase .Nom) = "I" := by decide
theorem test_me : i_Pron.s .NPAcc = "me" := by decide
theorem test_my : i_Pron.s (.NCase .Gen) = "my" := by decide
theorem test_mine : i_Pron.s .NPNomPoss = "mine" := by decide
theorem test_he : he_Pron.s (.NCase .Nom) = "he" := by decide
theorem test_him : he_Pron.s .NPAcc = "him" := by decide
theorem test_she_her : she_Pron.s .NPAcc = "her" := by decide
theorem test_their : they_Pron.s (.NCase .Gen) = "their" := by decide

end Mettapedia.Languages.GF.English.Pronouns
