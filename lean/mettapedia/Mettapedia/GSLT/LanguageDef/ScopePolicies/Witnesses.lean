import Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus
import Mettapedia.GSLT.LanguageDef.ScopePolicies.Translators

/-!
# Where the identity on text is not a translator

Two policies that give one program different numbers of answers are separated
by the identity on text: it is no translator between them
(`not_translates_of_answers`), and no map of theories that fixes that program
and the observations is hosting (`not_hosting_of_answers`).

The witnesses are rows of the scope corpus whose answer tables
`TemplateScope.SpectrumCorpus` proves by kernel-checked computation; nothing is
recomputed here.

| Pair | Row | Answers |
|---|---|---|
| rule M, lexical fresh | 23c, `(let $y 1 (Pair $y (let $y 2 $y)))` | 0, 1 |
| rule M, explicit capture | 5, `(let $y 5 (let $f L ($f 1)))` | 0, 1 |
| rule M, query-wide | 1, `(let $f L (Pair ($f 1) ($f 2)))` | 1, 0 |
| lexical fresh, explicit capture | 22b | 1, 0 |
| lexical fresh, query-wide | 1 | 1, 0 |
| explicit capture, query-wide | 1 | 1, 0 |
| per call, per closure (rule M) | 1 | 1, 0 |
| reference, snapshot (rule M) | 6, `(let $f L (Pair ($f 1) (let $y 5 $y)))` | 0, 1 |

So every two of the four ownership policies are separated
(`ownership_separated`), and so are the two lifetimes and the two readouts.
On the same rows the translators of `ScopePolicies.Translators` apply: the
translation of row 23c under lexical fresh has no answer, as rule M has none
on the source (`row23c_translated`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus

universe u v

section General

variable {S : Type u} {X : Type v} [DecidableEq X] [DecidableEq S]

/-- The answers of a query under a configuration come from a bag of the same
length. -/
theorem run_of_answersCfg {c : Config} {prog : S → Option (Tm S (Slot X))} {n : ℕ}
    {t : Src S X} {answerBag : List (Tm S (Slot X))}
    (answered : answersCfg c prog n t = some answerBag) :
    ∃ bag, run c.disc prog n [] Store.empty (elabCfg c [] t) = some bag ∧
      bag.length = answerBag.length := by
  unfold answersCfg answers at answered
  cases defined : run c.disc prog n [] Store.empty (elabCfg c [] t) with
  | none =>
      rw [defined] at answered
      cases answered
  | some bag =>
      rw [defined] at answered
      refine ⟨bag, rfl, ?_⟩
      rw [← Option.some.inj answered, List.length_map]

/-- **Different numbers of answers: the identity is no translator**, on any
domain that contains the program. -/
theorem not_translates_of_answers {c c' : Config} {u : X} {unit : S} {text : Program S X}
    {n n' : ℕ} {answerBag answerBag' : List (Tm S (Slot X))}
    (answered : answersCfg c (progSlot c u unit text.clauses) n text.query = some answerBag)
    (answered' : answersCfg c' (progSlot c' u unit text.clauses) n' text.query = some answerBag')
    (differ : answerBag.length ≠ answerBag'.length) (domain : Program S X → Prop)
    (inside : domain text) : ¬ Translates c c' u unit domain fun text => text := by
  intro translates
  obtain ⟨bag, defined, same⟩ := run_of_answersCfg answered
  obtain ⟨bag', defined', same'⟩ := run_of_answersCfg answered'
  exact differ (same.symm.trans ((translates.bag_length inside defined defined').trans same'))

/-- **Different numbers of answers: one policy steps where the other does
not.** -/
theorem step_lost_of_answers {c c' : Config} {u : X} {unit : S} {text : Program S X}
    {n n' : ℕ} {answerBag answerBag' : List (Tm S (Slot X))}
    (answered : answersCfg c (progSlot c u unit text.clauses) n text.query = some answerBag)
    (answered' : answersCfg c' (progSlot c' u unit text.clauses) n' text.query = some answerBag')
    (differ : answerBag.length ≠ answerBag'.length) :
    ∃ bag, (coreGSLT S X).rewrites (elabState c u unit (.program text)) (.done bag) ∧
      ¬ (coreGSLT S X).rewrites (elabState c' u unit (.program text)) (.done bag) := by
  obtain ⟨bag, defined, same⟩ := run_of_answersCfg answered
  obtain ⟨bag', defined', same'⟩ := run_of_answersCfg answered'
  refine ⟨bag, core_rewrites_of_run defined, fun step => ?_⟩
  have equivalent := core_rewrites_functional (core_rewrites_of_run defined') step
  exact differ (same.symm.trans ((coreEquiv_done_length equivalent).symm.trans same'))

/-- **Different numbers of answers: no map of theories that fixes the program
and the observations is hosting.** -/
theorem not_hosting_of_answers {c c' : Config} {u : X} {unit : S} {text : Program S X}
    {n n' : ℕ} {answerBag answerBag' : List (Tm S (Slot X))}
    (answered : answersCfg c (progSlot c u unit text.clauses) n text.query = some answerBag)
    (answered' : answersCfg c' (progSlot c' u unit text.clauses) n' text.query = some answerBag')
    (differ : answerBag.length ≠ answerBag'.length) {domain domain' : Program S X → Prop}
    (inside : domain text)
    (map : ContextMap (policyOn c u unit domain).termsAlone (policyOn c' u unit domain').termsAlone)
    (fixesProgram : (map.term (origin := PUnit.unit) ⟨.program text, inside⟩).1 = .program text)
    (fixesObservations : ∀ bag : Result S (Slot X),
      (map.term (origin := PUnit.unit) ⟨.done bag, trivial⟩).1 = .done bag) :
    ¬ map.Hosting := by
  obtain ⟨bag, step, lost⟩ := step_lost_of_answers answered answered' differ
  refine GSLT.not_hosting_of_step_lost (target := coreGSLT S X) map
    (origin := ⟨.program text, inside⟩) (next := ⟨.done bag, trivial⟩) step ?_
  show ¬ (coreGSLT S X).rewrites (elabState c' u unit _) (elabState c' u unit _)
  rw [fixesProgram, fixesObservations bag]
  exact lost

end General

/-! ## The rows -/

/-- A row of the corpus with the corpus equations, as a program. -/
def rowProgram (t : A) : Program Sy Sp := ⟨clauses, t⟩

/-- The answers of a row under a configuration, as the corpus computes them. -/
theorem ans_eq (c : Config) (t : A) :
    SpectrumCorpus.ans c clauses t =
      answersCfg c (progSlot c .u .unit (rowProgram t).clauses) 80 (rowProgram t).query :=
  rfl

theorem row23c_answers :
    SpectrumCorpus.ans cfgM clauses row23c = some [] ∧
      SpectrumCorpus.ans cfgLF clauses row23c = some [pairT (kT .n1) (kT .n2)] := by
  have table := row23c_table
  simp only [six, List.map_cons, List.cons.injEq] at table
  exact ⟨table.1, table.2.1⟩

theorem row5_answers :
    SpectrumCorpus.ans cfgM clauses row5 = some [] ∧
      ∃ answer, SpectrumCorpus.ans cfgEC clauses row5 = some [answer] := by
  have table := row5_table
  simp only [six, List.map_cons, List.cons.injEq] at table
  exact ⟨table.1, _, table.2.2.1⟩

theorem row1_answers :
    (∃ answer, SpectrumCorpus.ans cfgM clauses row1 = some [answer]) ∧
    (∃ answer, SpectrumCorpus.ans cfgLF clauses row1 = some [answer]) ∧
    (∃ answer, SpectrumCorpus.ans cfgEC clauses row1 = some [answer]) ∧
    SpectrumCorpus.ans cfgQ clauses row1 = some [] ∧
    SpectrumCorpus.ans cfgPC clauses row1 = some [] := by
  have table := row1_table
  simp only [six, List.map_cons, List.cons.injEq] at table
  exact ⟨⟨_, table.1⟩, ⟨_, table.2.1⟩, ⟨_, table.2.2.1⟩, table.2.2.2.1, table.2.2.2.2.1⟩

theorem row22b_answers :
    (∃ answer, SpectrumCorpus.ans cfgLF clauses row22b = some [answer]) ∧
      SpectrumCorpus.ans cfgEC clauses row22b = some [] := by
  have table := row22b_table
  simp only [six, List.map_cons, List.cons.injEq] at table
  exact ⟨⟨_, table.2.1⟩, table.2.2.1⟩

theorem row6_answers :
    SpectrumCorpus.ans cfgM clauses row6 = some [] ∧
      ∃ answer, SpectrumCorpus.ans cfgSN clauses row6 = some [answer] := by
  have table := row6_table
  simp only [six, List.map_cons, List.cons.injEq] at table
  exact ⟨table.1, _, table.2.2.2.2.2.1⟩

/-- Two configurations are separated by the identity when it is a translator
in neither direction, on the domain of all programs. -/
def Separated (c c' : Config) : Prop :=
  (¬ Translates c c' Sp.u Sy.unit (fun _ => True) fun text => text) ∧
    ¬ Translates c' c Sp.u Sy.unit (fun _ => True) fun text => text

theorem Separated.symm {c c' : Config} (separated : Separated c c') : Separated c' c :=
  ⟨separated.2, separated.1⟩

/-- Separation from two answer bags of different lengths. -/
theorem separated_of_answers {c c' : Config} {t : A} {answerBag answerBag' : List T}
    (answered : SpectrumCorpus.ans c clauses t = some answerBag)
    (answered' : SpectrumCorpus.ans c' clauses t = some answerBag')
    (differ : answerBag.length ≠ answerBag'.length) : Separated c c' :=
  ⟨not_translates_of_answers (text := rowProgram t) answered answered' differ _ trivial,
    not_translates_of_answers (text := rowProgram t) answered' answered (Ne.symm differ) _ trivial⟩

/-- **Rule M and lexical fresh**: row 23c. -/
theorem mercury_lexicalFresh_separated : Separated cfgM cfgLF :=
  separated_of_answers row23c_answers.1 row23c_answers.2 (by simp)

/-- **Rule M and explicit capture**: row 5. -/
theorem mercury_explicitCapture_separated : Separated cfgM cfgEC := by
  obtain ⟨none, answer, one⟩ := row5_answers
  exact separated_of_answers none one (by simp)

/-- **Rule M and the query-wide policy**: row 1. -/
theorem mercury_queryWide_separated : Separated cfgM cfgQ := by
  obtain ⟨⟨answer, one⟩, -, -, none, -⟩ := row1_answers
  exact separated_of_answers one none (by simp)

/-- **Lexical fresh and explicit capture**: row 22b. -/
theorem lexicalFresh_explicitCapture_separated : Separated cfgLF cfgEC := by
  obtain ⟨⟨answer, one⟩, none⟩ := row22b_answers
  exact separated_of_answers one none (by simp)

/-- **Lexical fresh and the query-wide policy**: row 1. -/
theorem lexicalFresh_queryWide_separated : Separated cfgLF cfgQ := by
  obtain ⟨-, ⟨answer, one⟩, -, none, -⟩ := row1_answers
  exact separated_of_answers one none (by simp)

/-- **Explicit capture and the query-wide policy**: row 1. -/
theorem explicitCapture_queryWide_separated : Separated cfgEC cfgQ := by
  obtain ⟨-, -, ⟨answer, one⟩, none, -⟩ := row1_answers
  exact separated_of_answers one none (by simp)

/-- **The two lifetimes**, under rule M: row 1. -/
theorem lifetimes_separated : Separated cfgM cfgPC := by
  obtain ⟨⟨answer, one⟩, -, -, -, none⟩ := row1_answers
  exact separated_of_answers one none (by simp)

/-- **The two readouts**, under rule M: row 6. -/
theorem readouts_separated : Separated cfgM cfgSN := by
  obtain ⟨none, answer, one⟩ := row6_answers
  exact separated_of_answers none one (by simp)

/-- **Every two ownership policies are separated by the identity on text**, at
per call and reference. -/
theorem ownership_separated (o o' : Ownership) (differ : o ≠ o') :
    Separated ⟨o, .perCall, .reference⟩ ⟨o', .perCall, .reference⟩ := by
  cases o <;> cases o' <;> first
    | exact absurd rfl differ
    | exact mercury_lexicalFresh_separated
    | exact mercury_lexicalFresh_separated.symm
    | exact mercury_explicitCapture_separated
    | exact mercury_explicitCapture_separated.symm
    | exact mercury_queryWide_separated
    | exact mercury_queryWide_separated.symm
    | exact lexicalFresh_explicitCapture_separated
    | exact lexicalFresh_explicitCapture_separated.symm
    | exact lexicalFresh_queryWide_separated
    | exact lexicalFresh_queryWide_separated.symm
    | exact explicitCapture_queryWide_separated
    | exact explicitCapture_queryWide_separated.symm

/-- **The identity on text is not a hosting map from the Mercury policy to the
lexical-fresh policy**: no map of theories that fixes row 23c and the
observations is hosting, whatever the domains. -/
theorem identity_not_hosting_mercury_lexicalFresh {domain domain' : Program Sy Sp → Prop}
    (inside : domain (rowProgram row23c))
    (map : ContextMap (policyOn cfgM Sp.u Sy.unit domain).termsAlone
      (policyOn cfgLF Sp.u Sy.unit domain').termsAlone)
    (fixesProgram : (map.term (origin := PUnit.unit) ⟨.program (rowProgram row23c), inside⟩).1 =
      .program (rowProgram row23c))
    (fixesObservations : ∀ bag : Result Sy (Slot Sp),
      (map.term (origin := PUnit.unit) ⟨.done bag, trivial⟩).1 = .done bag) :
    ¬ map.Hosting :=
  not_hosting_of_answers (text := rowProgram row23c) row23c_answers.1 row23c_answers.2 (by simp)
    inside map fixesProgram fixesObservations

/-- Row 23c is an admissible program, so it lies in the domain of
`toLexicalMap`. -/
theorem row23c_admissible : (rowProgram row23c).Admissible := by
  refine ⟨fun F body found => ?_, by decide⟩
  cases F <;> first
    | (cases found; decide)
    | cases found

/-- **Positive, on the same row**: the translation of row 23c has, under
lexical fresh, as many answers as rule M gives the source: none. -/
theorem row23c_translated {n : ℕ} {bag : Result Sy (Slot Sp)}
    (defined : run .static (progSlot cfgLF Sp.u Sy.unit (toLexProgram (rowProgram row23c)).clauses)
      n [] Store.empty (elabCfg cfgLF [] (toLexProgram (rowProgram row23c)).query) = some bag) :
    bag = [] := by
  obtain ⟨source, definedSource, same⟩ := run_of_answersCfg row23c_answers.1
  have length := (translates_toLexical Sp.u Sy.unit).bag_length row23c_admissible
    definedSource defined
  exact List.eq_nil_of_length_eq_zero (length.symm.trans same)

#print axioms not_translates_of_answers
#print axioms not_hosting_of_answers
#print axioms ownership_separated
#print axioms lifetimes_separated
#print axioms readouts_separated
#print axioms identity_not_hosting_mercury_lexicalFresh
#print axioms row23c_translated

end Mettapedia.GSLT.LanguageDef.ScopePolicies
