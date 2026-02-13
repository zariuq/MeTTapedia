/-
# GF Core - Grammatical Framework Foundation

Core abstractions from the Grammatical Framework:
- Categories (types in the grammar)
- Abstract syntax (language-independent trees)
- Concrete syntax (language-specific linearization)
- Bisimulation equivalence (when trees mean the same thing)

## References
- GF Resource Grammar Library: ~/claude/gf-rgl/
- GF Tutorial: http://www.grammaticalframework.org/
-/

namespace Mettapedia.Languages.GF.Core

/-! ## Categories

GF categories represent grammatical types:
- Base categories: S (sentence), NP (noun phrase), CN (common noun), etc.
- Function categories: arrows between categories
-/

inductive Category where
  | base : String → Category
  | arrow : Category → Category → Category
  deriving DecidableEq, Repr

namespace Category

-- Sentences and clauses (Cat.gf)
def S : Category := base "S"             -- declarative sentence
def QS : Category := base "QS"           -- question
def RS : Category := base "RS"           -- relative clause
def Cl : Category := base "Cl"           -- declarative clause (all tenses)
def ClSlash : Category := base "ClSlash" -- clause missing NP (S/NP)
def SSlash : Category := base "SSlash"   -- sentence missing NP
def Imp : Category := base "Imp"         -- imperative

-- Questions and interrogatives (Cat.gf)
def QCl : Category := base "QCl"         -- question clause (all tenses)
def IP : Category := base "IP"           -- interrogative pronoun
def IComp : Category := base "IComp"     -- interrogative complement of copula
def IDet : Category := base "IDet"       -- interrogative determiner
def IQuant : Category := base "IQuant"   -- interrogative quantifier
def QVP : Category := base "QVP"         -- question VP (Question.gf)

-- Relative clauses and pronouns (Cat.gf)
def RCl : Category := base "RCl"         -- relative clause (all tenses)
def RP : Category := base "RP"           -- relative pronoun

-- Verb phrases (Cat.gf)
def VP : Category := base "VP"           -- verb phrase
def Comp : Category := base "Comp"       -- complement of copula
def VPSlash : Category := base "VPSlash" -- VP missing complement

-- Adjectival phrases (Cat.gf)
def AP : Category := base "AP"           -- adjectival phrase

-- Nouns and noun phrases (Cat.gf)
def CN : Category := base "CN"           -- common noun
def NP : Category := base "NP"           -- noun phrase
def Pron : Category := base "Pron"       -- personal pronoun
def Det : Category := base "Det"         -- determiner phrase
def Predet : Category := base "Predet"   -- predeterminer
def Quant : Category := base "Quant"     -- quantifier (nucleus of Det)
def Num : Category := base "Num"         -- number determining element
def Card : Category := base "Card"       -- cardinal number
def ACard : Category := base "ACard"     -- adjective-like cardinal
def Ord : Category := base "Ord"         -- ordinal number
def DAP : Category := base "DAP"         -- determiner with adjective

-- Numerals (Cat.gf)
def Numeral : Category := base "Numeral" -- cardinal/ordinal in words
def Digits : Category := base "Digits"   -- cardinal/ordinal in digits
def Decimal : Category := base "Decimal" -- decimal number

-- Structural words (Cat.gf)
def Conj : Category := base "Conj"       -- conjunction
def Subj : Category := base "Subj"       -- subjunction
def Prep : Category := base "Prep"       -- preposition or case

-- Open-class words (Cat.gf)
def V : Category := base "V"             -- one-place verb
def V2 : Category := base "V2"           -- two-place verb
def V3 : Category := base "V3"           -- three-place verb
def VV : Category := base "VV"           -- VP-complement verb
def VS : Category := base "VS"           -- S-complement verb
def VQ : Category := base "VQ"           -- Q-complement verb
def VA : Category := base "VA"           -- AP-complement verb
def V2V : Category := base "V2V"         -- verb with NP+V complement
def V2S : Category := base "V2S"         -- verb with NP+S complement
def V2Q : Category := base "V2Q"         -- verb with NP+Q complement
def V2A : Category := base "V2A"         -- verb with NP+AP complement
def A : Category := base "A"             -- one-place adjective
def A2 : Category := base "A2"           -- two-place adjective
def N : Category := base "N"             -- common noun (lexical)
def N2 : Category := base "N2"           -- relational noun
def N3 : Category := base "N3"           -- three-place relational noun
def GN : Category := base "GN"           -- given name
def SN : Category := base "SN"           -- second name
def LN : Category := base "LN"           -- location name
def PN : Category := base "PN"           -- proper name

-- Common categories (Common.gf) — uniform linearization across languages
def Text : Category := base "Text"       -- text of several phrases
def Phr : Category := base "Phr"         -- phrase in a text
def Utt : Category := base "Utt"         -- sentence, question, word...
def Voc : Category := base "Voc"         -- vocative or "please"
def PConj : Category := base "PConj"     -- phrase-beginning conjunction
def Interj : Category := base "Interj"   -- interjection
def SC : Category := base "SC"           -- embedded sentence/question
def Adv : Category := base "Adv"         -- VP-modifying adverb
def AdV : Category := base "AdV"         -- adverb directly on verb
def AdA : Category := base "AdA"         -- adjective-modifying adverb
def AdN : Category := base "AdN"         -- numeral-modifying adverb
def IAdv : Category := base "IAdv"       -- interrogative adverb
def CAdv : Category := base "CAdv"       -- comparative adverb
def Temp : Category := base "Temp"       -- temporal/aspectual features
def Tense : Category := base "Tense"     -- tense
def Pol : Category := base "Pol"         -- polarity
def Ant : Category := base "Ant"         -- anteriority
def MU : Category := base "MU"           -- unit of measurement

-- Conjunction list categories (Conjunction.gf)
def ListS : Category := base "ListS"
def ListRS : Category := base "ListRS"
def ListAdv : Category := base "ListAdv"
def ListAdV : Category := base "ListAdV"
def ListNP : Category := base "ListNP"
def ListAP : Category := base "ListAP"
def ListIAdv : Category := base "ListIAdv"
def ListCN : Category := base "ListCN"
def ListDAP : Category := base "ListDAP"

-- Numeral sub-categories (Numeral.gf)
def Digit : Category := base "Digit"
def Sub10 : Category := base "Sub10"
def Sub100 : Category := base "Sub100"
def Sub1000 : Category := base "Sub1000"
def Sub1000000 : Category := base "Sub1000000"
def Sub1000000000 : Category := base "Sub1000000000"
def Sub1000000000000 : Category := base "Sub1000000000000"
def Dig : Category := base "Dig"

-- Extend categories (Extend.gf)
def VPS : Category := base "VPS"           -- finite VP with tense/polarity
def VPI : Category := base "VPI"           -- infinitive VP
def VPS2 : Category := base "VPS2"         -- binary VPS
def VPI2 : Category := base "VPI2"         -- binary VPI
def RNP : Category := base "RNP"           -- reflexive noun phrase
def RNPList : Category := base "RNPList"   -- list of reflexive NPs
def ListVPS : Category := base "ListVPS"
def ListVPI : Category := base "ListVPI"
def ListVPS2 : Category := base "ListVPS2"
def ListVPI2 : Category := base "ListVPI2"
def ListComp : Category := base "ListComp"
def ListImp : Category := base "ListImp"

-- Construction categories (Construction.gf)
def Timeunit : Category := base "Timeunit"
def Hour : Category := base "Hour"
def Weekday : Category := base "Weekday"
def Month : Category := base "Month"
def Monthday : Category := base "Monthday"
def Year : Category := base "Year"
def Language : Category := base "Language"

-- Symbol categories (Symbol.gf)
def Symb : Category := base "Symb"
def ListSymb : Category := base "ListSymb"

/-- All GF RGL category names (full: Common + Cat + Question + Conjunction +
    Numeral + Extend + Construction + Symbol). -/
def allCategoryNames : List String :=
  -- Sentences/clauses
  ["S", "QS", "RS", "Cl", "ClSlash", "SSlash", "Imp",
  -- Questions/interrogatives
   "QCl", "IP", "IComp", "IDet", "IQuant", "QVP",
  -- Relatives
   "RCl", "RP",
  -- Verb phrases
   "VP", "Comp", "VPSlash",
  -- Adjective phrases
   "AP",
  -- Nouns/NPs
   "CN", "NP", "Pron", "Det", "Predet", "Quant", "Num", "Card", "ACard", "Ord", "DAP",
  -- Numerals (Cat)
   "Numeral", "Digits", "Decimal",
  -- Structural
   "Conj", "Subj", "Prep",
  -- Open-class words
   "V", "V2", "V3", "VV", "VS", "VQ", "VA",
   "V2V", "V2S", "V2Q", "V2A",
   "A", "A2", "N", "N2", "N3", "GN", "SN", "LN", "PN",
  -- Common
   "Text", "Phr", "Utt", "Voc", "PConj", "Interj", "SC",
   "Adv", "AdV", "AdA", "AdN", "IAdv", "CAdv",
   "Temp", "Tense", "Pol", "Ant", "MU",
  -- Conjunction lists
   "ListS", "ListRS", "ListAdv", "ListAdV", "ListNP",
   "ListAP", "ListIAdv", "ListCN", "ListDAP",
  -- Numeral sub-categories
   "Digit", "Sub10", "Sub100", "Sub1000", "Sub1000000",
   "Sub1000000000", "Sub1000000000000", "Dig",
  -- Extend
   "VPS", "VPI", "VPS2", "VPI2", "RNP", "RNPList",
   "ListVPS", "ListVPI", "ListVPS2", "ListVPI2", "ListComp", "ListImp",
  -- Construction
   "Timeunit", "Hour", "Weekday", "Month", "Monthday", "Year", "Language",
  -- Symbol
   "Symb", "ListSymb"]

end Category

/-! ## Abstract Syntax

Abstract syntax trees represent the meaning/structure independent of any specific language.
For MVP, we use a simplified representation without full dependent trees.
-/

/-- Abstract syntax tree with a category -/
structure AbstractTree where
  cat : Category
  /-- Tree identifier (for simplified MVP - full version would have constructor+args) -/
  id : Nat
  deriving DecidableEq, Repr


/-! ## Concrete Syntax

Concrete syntax maps abstract trees to strings in a specific language.
Linearization may depend on morphological parameters (case, number, gender, etc.).
-/

/-- Concrete form with parameterized linearization -/
structure ConcreteForm (Params : Type) where
  linearize : Params → String


/-! ## Grammar

A GF grammar consists of:
- Abstract syntax (categories and functions)
- Concrete syntax (linearization rules per category)
-/

/-- GF grammar with parameterized concrete syntax -/
structure Grammar (Params : Type) where
  /-- Name of the grammar -/
  name : String
  /-- Abstract categories in this grammar -/
  categories : List Category
  /-- Linearization function for each category -/
  concrete : Category → ConcreteForm Params


/-! ## Note on Bisimulation Equivalence

Proper linguistic bisimulation requires comparing tree *structure* and *linearization*,
not just category labels. The simplified `AbstractTree` type (category + id) is too
weak for this. Meaningful bisimulation is defined in:
- `Abstract.lean`: `NodeEquiv` for tree-structural equivalence
- `Czech/Properties.lean`: `LinguisticallyEquivalent` for inflectional equivalence
-/

end Mettapedia.Languages.GF.Core
