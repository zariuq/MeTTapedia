import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects

/-!
# Source search and atomic attempt outcomes

The bounded contextual search keeps completed emptiness separate from an
unfinished solver job. The effect phase is a finite source sub-run over its
already prepared common interface. Its body compiler remains responsible
for the source bindings; this interface does not call a host evaluator.

A one-answer attempt may proceed when a match is known even if other jobs
are unfinished. A whole-table attempt requires completeness and may fire
vacuously. Neither refusal nor incompleteness publishes a private prefix.
The outcome relation retains the evidence instead of treating lack of a
readiness proof as a completed rejection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAttemptOutcomes

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries

variable {S : Signature} {Query Local Shared O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt}

structure Search where
  equations : EquationStore (Term (signature S captures) Γ sort)
  patterns : List (Term (signature S (queryFamily queries captures)) Γ sort)
  rows : O → ContextualStoredRows.Row locals captures Γ sort
  world : Finset O
  budget : (Fin patterns.length → O) → Nat

namespace Search

variable {queries locals captures}
    [DecidableEq Query] [DecidableEq Local] [DecidableEq Shared] [DecidableEq O]
    [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

def complete (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort)) : Bool :=
  ContextualQueryAnswers.certifies queries locals captures search.equations search.patterns search.rows search.world search.budget

def entries (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort)) :=
  ContextualQueryAnswers.answers queries locals captures search.equations search.patterns search.rows search.world search.budget

def SourceMatch (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort))
    (chosen : Fin search.patterns.length → O) : Prop :=
  (∀ port, chosen port ∈ search.world) ∧
    ∃ (Next : Type) (next : Next → MetaArity S) (candidate : Assignment captures next),
      ContextualFrameUnifier.Models candidate search.equations ∧
        ContextualConjunctiveQueries.Matches queries locals captures candidate search.patterns search.rows chosen

theorem entries_exact (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort))
    (complete : search.complete = true) (chosen : Fin search.patterns.length → O) :
    chosen ∈ search.entries ↔ search.SourceMatch chosen :=
  ContextualQueryAnswers.actual_answer_iff queries locals captures search.equations search.patterns search.rows
    search.world search.budget complete chosen

/-- A completed answer is usable without waiting for unrelated search jobs.
Only the converse completeness assertion needs the whole-table certificate. -/
theorem entry_sound (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort))
    (chosen : Fin search.patterns.length → O) (member : chosen ∈ search.entries) : search.SourceMatch chosen := by
  have present := (ContextualConjunctiveAbsence.mem_candidates search.world chosen).mp
    (Finset.mem_filter.mp member).1
  obtain ⟨update, _, empty, _⟩ := ContextualQueryAnswers.answer_factors queries locals captures search.equations
    search.patterns search.rows search.world search.budget chosen member
  have solved := (ContextualResidual.models_observeProblem update.answer _).mp (update.completed empty)
  have split := ContextualConjunctiveModels.joint_model_gives_caller_and_match queries locals captures update.answer
    search.equations search.patterns search.rows chosen solved
  exact ⟨present, update.Variables, update.declaration,
    ContextualConjunctiveModels.caller queries locals captures update.answer, split⟩

theorem complete_empty_iff (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort))
    (complete : search.complete = true) :
    search.entries = ∅ ↔ ¬ ∃ chosen, search.SourceMatch chosen := by
  constructor
  · intro empty ⟨chosen, matched⟩
    have member := (search.entries_exact complete chosen).mpr matched
    rw [empty] at member
    simp at member
  · intro absent
    apply Finset.eq_empty_of_forall_notMem
    intro chosen member
    exact absent ⟨chosen, (search.entries_exact complete chosen).mp member⟩

/-- Failure of the complete-table check identifies an actual unfinished
job, rather than a refuted match or an empty successful table. -/
theorem unfinished_job (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort))
    (unfinished : search.complete = false) :
    ∃ chosen ∈ ContextualConjunctiveAbsence.candidates search.world search.patterns.length,
      ∃ update : ContextualFrameUpdate.Update
        (ContextualQueryAnswers.problemAt queries locals captures search.equations search.patterns search.rows chosen),
        ContextualQueryAnswers.scan queries locals captures search.equations search.patterns search.rows search.budget chosen =
          .residual update ∧ update.remaining ≠ [] := by
  have missing : ¬ ∀ chosen ∈ ContextualConjunctiveAbsence.candidates search.world search.patterns.length,
      ContextualQueryAnswers.closed
        (ContextualQueryAnswers.scan queries locals captures search.equations search.patterns search.rows search.budget chosen) = true := by
    intro all
    have complete : search.complete = true := by exact decide_eq_true all
    rw [unfinished] at complete
    cases complete
  push Not at missing
  obtain ⟨chosen, present, notClosed⟩ := missing
  cases computed : ContextualQueryAnswers.scan queries locals captures search.equations search.patterns search.rows
      search.budget chosen with
  | refuted impossible => exact False.elim (notClosed (by rw [computed]; rfl))
  | residual update =>
      refine ⟨chosen, present, update, computed, ?_⟩
      intro empty
      exact notClosed (by simp only [computed, ContextualQueryAnswers.closed, empty, List.isEmpty_nil])

end Search

inductive Mode where
  | one
  | every
deriving DecidableEq

inductive Outcome where
  | fired
  | none
  | refused
  | incomplete
deriving DecidableEq

variable {queries locals captures}
    [DecidableEq Query] [DecidableEq Local] [DecidableEq Shared] [DecidableEq O]
    [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

def SourceReady (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort)) : Mode → Prop
  | .one => search.entries.Nonempty
  | .every => search.complete = true

theorem one_ready_has_a_source_match
    (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort))
    (ready : SourceReady search .one) : ∃ chosen, search.SourceMatch chosen := by
  obtain ⟨chosen, member⟩ := ready
  exact ⟨chosen, search.entry_sound chosen member⟩

section Effects

variable {T EffectSubst : Type} {EffectO : Type} [DecidableEq EffectO]

inductive Attempt (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort)) (mode : Mode)
    (action : SubstitutionAction T EffectSubst) (label : EffectO → T)
    (code : List (StagedSourceEffects.Instruction T EffectSubst EffectO))
    (before : Configuration T EffectO) : Outcome → Configuration T EffectO → Prop where
  | fired (source : SourceReady search mode)
      (ready : StagedSourceEffects.Executable action label before code) :
      Attempt search mode action label code before .fired
        (ConditionalSchedule.follow label before (code.map StagedSourceEffects.Instruction.raw))
  | none (one : mode = .one) (complete : search.complete = true) (empty : search.entries = ∅) :
      Attempt search mode action label code before .none before
  | refused (source : SourceReady search mode)
      (denied : ¬ StagedSourceEffects.Executable action label before code) :
      Attempt search mode action label code before .refused before
  | incomplete (unfinished : search.complete = false) :
      Attempt search mode action label code before .incomplete before

namespace Attempt

variable {search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort)} {mode : Mode}
    {action : SubstitutionAction T EffectSubst} {label : EffectO → T}
    {code : List (StagedSourceEffects.Instruction T EffectSubst EffectO)} {before after : Configuration T EffectO}

theorem nonfiring_unchanged {outcome : Outcome} (attempt : Attempt search mode action label code before outcome after)
    (nonfiring : outcome ≠ .fired) : after = before := by
  cases attempt with
  | fired _ _ => exact False.elim (nonfiring rfl)
  | none _ _ _ => rfl
  | refused _ _ => rfl
  | incomplete _ => rfl

theorem refused_keeps_a_standing_rule (attempt : Attempt search mode action label code before .refused after)
    (installation : EffectO) (present : installation ∈ before.present) : installation ∈ after.present := by
  rw [attempt.nonfiring_unchanged (by decide)]
  exact present

theorem none_has_no_source_match (attempt : Attempt search mode action label code before .none after) :
    ¬ ∃ chosen, search.SourceMatch chosen := by
  cases attempt with
  | none _ complete empty => exact (search.complete_empty_iff complete).mp empty

theorem unfinished_cannot_report_none (unfinished : search.complete = false) :
    ¬ Attempt search mode action label code before .none after := by
  intro attempt
  cases attempt with
  | none _ complete _ => rw [unfinished] at complete; cases complete

theorem whole_table_never_reports_none : ¬ Attempt search .every action label code before .none after := by
  intro attempt
  cases attempt with
  | none impossible _ _ => cases impossible

/-- Successful attempts are actual source sub-runs and have the compiled
entry's retained guard and census conditions, in addition to source readiness. -/
theorem fired_retains_admission (attempt : Attempt search mode action label code before .fired after) :
    SourceReady search mode ∧ (StagedSourceEffects.compile label code).Holds action label before ∧
      after = ConditionalSchedule.follow label before (code.map StagedSourceEffects.Instruction.raw) := by
  cases attempt with
  | fired source ready => exact ⟨source, (StagedSourceEffects.compile_exact action label code before).mpr ready, rfl⟩

theorem fired_has_one_atomic_realization (attempt : Attempt search mode action label code before .fired after) :
    let plan := (StagedSourceEffects.compile label code).raw
    let selected := CensusSourceCompilation.selection plan.effect
    let rule := CensusSourceCompilation.rule label plan.effect plan.equations
    PredicateQueryAdmission.Valid action label rule (plan.effect.queries.map PredicateQueryAdmission.Query.fixed) before selected ∧
      action.Equivalent (selected.result label rule before).equations after.equations ∧
      (selected.result label rule before).present = after.present := by
  have ready := attempt.fired_retains_admission
  rw [ready.2.2]
  exact StagedSourceEffects.realize_net_under_retained_admission action label code before ready.2.1

/-- This is semantic exhaustiveness, with certified negative branches. It
does not assert a decision procedure for arbitrary higher-order guards. -/
theorem exists_outcome (search : Search queries locals captures (O := O) (Γ := Γ) (sort := sort))
    (mode : Mode) (action : SubstitutionAction T EffectSubst) (label : EffectO → T)
    (code : List (StagedSourceEffects.Instruction T EffectSubst EffectO)) (before : Configuration T EffectO) :
    ∃ outcome after, Attempt search mode action label code before outcome after := by
  classical
  by_cases source : SourceReady search mode
  · by_cases ready : StagedSourceEffects.Executable action label before code
    · exact ⟨.fired, _, .fired source ready⟩
    · exact ⟨.refused, _, .refused source ready⟩
  · cases complete : search.complete with
    | false => exact ⟨.incomplete, _, .incomplete complete⟩
    | true =>
        cases mode with
        | every => exact False.elim (source complete)
        | one =>
            have empty : search.entries = ∅ := Finset.not_nonempty_iff_eq_empty.mp source
            exact ⟨.none, _, .none rfl complete empty⟩

end Attempt
end Effects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAttemptOutcomes
