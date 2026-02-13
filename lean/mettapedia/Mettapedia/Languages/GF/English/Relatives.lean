/-
# English Relative Clauses

Relative pronouns, relative clauses, and clause slashes for English.
Ported from GF RelativeEng.gf and ResEng.gf.

Key constructions:
- RelVP: "who walks", "that sleeps" (RP + VP)
- RelSlash: "whom she loves", "that he sees" (RP + ClSlash)
- RelCN: "cat that walks", "man whom she loves" (CN + RS)

## References
- GF RelativeEng.gf: RelVP, RelSlash, IdRP
- GF ResEng.gf: SlashVP, RCase, RAgr
-/

import Mettapedia.Languages.GF.English.Pronouns

namespace Mettapedia.Languages.GF.English.Relatives

open Mettapedia.Languages.GF.English
open Syntax Verbs Nouns Pronouns

/-! ## Relative Pronoun Types -/

/-- Case for relative pronouns: RC (in a relative clause) or RPrep (after preposition) -/
inductive RCase where
  | RC (g : Gender) (c : NPCase)
  | RPrep (g : Gender)
  deriving DecidableEq, Repr, Inhabited

/-- Agreement for relative pronouns: inherit from antecedent or fixed -/
inductive RAgr where
  | RNoAg   -- inherits agreement from antecedent
  | RAg (a : Agr)  -- fixed agreement
  deriving DecidableEq, Repr, Inhabited

/-! ## Core Structures -/

/-- Relative pronoun: who/whom/whose/which/that -/
structure EnglishRP where
  s : RCase → String
  a : RAgr

/-- Relative clause with unapplied tense (parameterized by antecedent agreement) -/
structure EnglishRCl where
  s : Tense → Anteriority → CPolarity → Agr → String

/-- Relative sentence: tense applied, still parameterized by antecedent agreement -/
structure EnglishRS where
  s : Agr → String

/-- Clause with a missing NP (slash category) -/
structure EnglishClSlash where
  s : Tense → Anteriority → CPolarity → Order → String
  c2 : String  -- the preposition of the gap

/-! ## Relative Pronoun -/

/-- Extract gender from agreement -/
def agrGender : Agr → Gender
  | .AgP3Sg g => g
  | .AgP3Pl => .Neutr
  | _ => .Neutr

/-- The basic relative pronoun: who/whom/whose/which/that.
    Ported from RelativeEng.gf `IdRP`. -/
def idRP : EnglishRP :=
  { s := fun rc => match rc with
      | .RC _ (.NCase .Gen) => "whose"
      | .RC _ .NPNomPoss => "whose"
      | .RC .Neutr _ => "that"
      | .RC _ (.NCase .Nom) => "that"
      | .RC _ .NPAcc => "that"
      | .RPrep .Neutr => "which"
      | .RPrep _ => "who"
    a := .RNoAg }

/-- "which" relative pronoun (for non-restrictive clauses) -/
def whichRP : EnglishRP :=
  { s := fun rc => match rc with
      | .RC _ (.NCase .Gen) => "whose"
      | .RC _ .NPNomPoss => "whose"
      | .RC .Neutr _ => "which"
      | .RC _ _ => "who"
      | .RPrep .Neutr => "which"
      | .RPrep _ => "whom"
    a := .RNoAg }

/-! ## Clause Slash Construction -/

/-- Build a clause slash from subject + VPSlash.
    "everybody loves ___", "she looks at ___" -/
def slashVP (subj : EnglishNP) (vps : EnglishVPSlash) : EnglishClSlash :=
  let cl := mkClause (subj.s (.NCase .Nom)) subj.agr vps.toEnglishVP
  { s := fun t ant pol ord => cl.s t ant pol ord
    c2 := vps.c2 }

/-! ## Relative Clause Construction -/

/-- RelVP: relative pronoun + VP → relative clause.
    "who walks", "that sleeps" -/
def relVP (rp : EnglishRP) (vp : EnglishVP) : EnglishRCl :=
  { s := fun t ant pol ag =>
      let agr := match rp.a with
        | .RNoAg => ag      -- inherit from antecedent
        | .RAg a => a       -- use RP's own agreement
      let subjStr := rp.s (.RC (agrGender agr) (.NCase .Nom))
      let cl := mkClause subjStr agr vp
      cl.s t ant pol (.ODir true) }

/-- RelSlash: relative pronoun + clause slash → relative clause.
    "that everybody loves", "whom she saw" -/
def relSlash (rp : EnglishRP) (slash : EnglishClSlash) : EnglishRCl :=
  { s := fun t ant pol ag =>
      let rpStr := rp.s (.RC (agrGender ag) .NPAcc)
      let clStr := slash.s t ant pol (.ODir true)
      if slash.c2 == "" then rpStr ++ " " ++ clStr
      else rpStr ++ " " ++ clStr ++ " " ++ slash.c2 }

/-! ## Tense Application -/

/-- UseRCl: apply tense/aspect/polarity to a relative clause -/
def useRCl (t : Tense) (ant : Anteriority) (pol : CPolarity)
    (rcl : EnglishRCl) : EnglishRS :=
  { s := fun ag => rcl.s t ant pol ag }

/-! ## CN Modification -/

/-- RelCN: add a relative clause to a common noun.
    "cat that walks", "man whom she loves" -/
def relCN (cn : EnglishCN) (rs : EnglishRS) : EnglishCN :=
  { s := fun n c =>
      let agr := match n with
        | .Sg => Agr.AgP3Sg cn.g
        | .Pl => .AgP3Pl
      cn.s n c ++ " " ++ rs.s agr
    g := cn.g }

/-! ## Tests -/

-- Relative pronoun forms
#eval! idRP.s (.RC .Neutr (.NCase .Nom))  -- "that"
#eval! idRP.s (.RC .Masc (.NCase .Nom))   -- "that"
#eval! idRP.s (.RC .Neutr (.NCase .Gen))  -- "whose"
#eval! idRP.s (.RPrep .Neutr)             -- "which"
#eval! idRP.s (.RPrep .Masc)              -- "who"

-- RelVP: "the cat that walks"
private def catThatWalks :=
  linDetCN theDefArt (relCN (linUseN cat_N)
    (useRCl .Pres .Simul .CPos (relVP idRP (predV walk_V))))
#eval! catThatWalks.s (.NCase .Nom)  -- "the cat that walks"

-- RelVP: "the man that sleeps"
private def manThatSleeps :=
  linDetCN theDefArt (relCN (linUseN man_N)
    (useRCl .Pres .Simul .CPos (relVP idRP (predV sleep_V))))
#eval! manThatSleeps.s (.NCase .Nom)  -- "the man that sleeps"

-- RelSlash: "the cat that he loves"
private def catThatHeLoves :=
  let slash := slashVP he_Pron (slashV2a love_V2)
  linDetCN theDefArt (relCN (linUseN cat_N)
    (useRCl .Pres .Simul .CPos (relSlash idRP slash)))
#eval! catThatHeLoves.s (.NCase .Nom)  -- "the cat that he loves"

-- RelSlash with preposition: "the man that she looks at"
private def manSheLooksAt :=
  let slash := slashVP she_Pron (slashV2a lookAt_V2)
  linDetCN theDefArt (relCN (linUseN man_N)
    (useRCl .Pres .Simul .CPos (relSlash idRP slash)))
#eval! manSheLooksAt.s (.NCase .Nom)  -- "the man that she looks at"

-- Sentence with relative clause: "the cat that walks sleeps"
#eval! linUseCl .Pres .Simul .CPos
  (linPredVP catThatWalks (predV sleep_V))
  -- "the cat that walks sleeps"

/-! ## Correctness Properties -/

theorem test_idRP_that : idRP.s (.RC .Neutr (.NCase .Nom)) = "that" := by decide
theorem test_idRP_whose : idRP.s (.RC .Masc (.NCase .Gen)) = "whose" := by decide
theorem test_idRP_which : idRP.s (.RPrep .Neutr) = "which" := by decide
theorem test_idRP_who : idRP.s (.RPrep .Masc) = "who" := by decide

end Mettapedia.Languages.GF.English.Relatives
