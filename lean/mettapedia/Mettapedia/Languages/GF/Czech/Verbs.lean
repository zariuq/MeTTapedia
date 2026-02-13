/-
# Czech Verb Conjugation

Verb forms and conjugation ported from GF Resource Grammar Library.
Covers present tense (6 person x number forms), past participles,
infinitive, and the productive -ovat conjugation class.

## Source
Ported from: ~/claude/gf-rgl/src/czech/ResCze.gf (lines 552-619)

## Verbs Implemented
1. **copulaVerbForms** (být) - to be (irregular, with special negation)
2. **haveVerbForms** (mít) - to have (irregular)
3. **iii_kupovatVerbForms** (kupovat) - productive -ovat class
-/

import Mettapedia.Languages.GF.Czech.Morphology

namespace Mettapedia.Languages.GF.Czech.Verbs

open Mettapedia.Languages.GF.Czech

/-! ## Verb Forms Record

10 named fields covering present tense conjugation + participles.
-/

/-- Czech verb forms: infinitive, present tense (6 forms), past participles, special negation -/
structure VerbForms where
  inf        : String  -- infinitive (být, mít, kupovat)
  pressg1    : String  -- present singular 1st (jsem, mám)
  pressg2    : String  -- present singular 2nd (jsi, máš)
  pressg3    : String  -- present singular 3rd (je, má)
  prespl1    : String  -- present plural 1st (jsme, máme)
  prespl2    : String  -- present plural 2nd (jste, máte)
  prespl3    : String  -- present plural 3rd (jsou, mají)
  pastpartsg : String  -- past participle singular (byl, měl)
  pastpartpl : String  -- past participle plural (byli, měli)
  negpressg3 : String  -- negative present 3sg (matters for copula: není vs *neje)
  deriving DecidableEq, Repr

/-- Complement case for transitive verbs: preposition + governed case -/
structure ComplementCase where
  s : String       -- preposition string (empty for direct objects)
  c : Case         -- governed case
  hasPrep : Bool   -- whether preposition is present
  deriving DecidableEq, Repr

/-! ## Verb Agreement Dispatch

Select the correct present tense form based on agreement features.
-/

/-- Select present tense form by person x number.
    Bool = polarity (true = positive, false = negative).
    Negation only matters for copula (je vs ní). -/
def verbAgr (vf : VerbForms) (a : Agr) (polarity : Bool) : String :=
  match a.number, a.person with
  | .Sg, .P1 => vf.pressg1
  | .Sg, .P2 => vf.pressg2
  | .Sg, .P3 => if polarity then vf.pressg3 else vf.negpressg3
  | .Pl, .P1 => vf.prespl1
  | .Pl, .P2 => vf.prespl2
  | .Pl, .P3 => vf.prespl3

/-! ## Lexicalized Verbs -/

/-- Copula "být" (to be) - irregular, with special negation form.
    Source: GF ResCze.gf lines 576-587 -/
def copulaVerbForms : VerbForms :=
  { inf := "být"
  , pressg1 := "jsem"
  , pressg2 := "jsi"
  , pressg3 := "je"
  , prespl1 := "jsme"
  , prespl2 := "jste"
  , prespl3 := "jsou"
  , pastpartsg := "byl"
  , pastpartpl := "byli"
  , negpressg3 := "ní" }  -- ne + ní → není

/-- "mít" (to have) - irregular.
    Source: GF ResCze.gf lines 589-599 -/
def haveVerbForms : VerbForms :=
  { inf := "mít"
  , pressg1 := "mám"
  , pressg2 := "máš"
  , pressg3 := "má"
  , prespl1 := "máme"
  , prespl2 := "máte"
  , prespl3 := "mají"
  , pastpartsg := "měl"
  , pastpartpl := "měli"
  , negpressg3 := "má" }  -- no special negation

/-! ## Productive Paradigm: -ovat Class

Third conjugation class. Productive and regular.
kupovat → kupuji, kupuješ, kupuje, kupujeme, kupujete, kupují
Source: GF ResCze.gf lines 604-619
-/

/-- Conjugate -ovat verbs (productive class III).
    kupovat → stem "kupo" → u-stem "kupu" → kupuji, kupuješ, ... -/
def iii_kupovatVerbForms (lemma : String) : VerbForms :=
  let stem := strDropEnd lemma 3          -- kupovat → kupo (drop "vat")
  let uStem := strDropEnd stem 1 ++ "u"   -- kupo → kupu (last vowel → u)
  { inf := lemma
  , pressg1 := uStem ++ "ji"
  , pressg2 := uStem ++ "ješ"
  , pressg3 := uStem ++ "je"
  , prespl1 := uStem ++ "jeme"
  , prespl2 := uStem ++ "jete"
  , prespl3 := uStem ++ "jí"
  , pastpartsg := stem ++ "val"
  , pastpartpl := stem ++ "vali"
  , negpressg3 := uStem ++ "je" }  -- no special negation

/-! ## Default Complement Case -/

/-- Default accusative complement (direct object with no preposition) -/
def accComplement : ComplementCase :=
  { s := "", c := .Acc, hasPrep := false }

end Mettapedia.Languages.GF.Czech.Verbs
