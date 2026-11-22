import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAttemptOutcomes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswersControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffectsControls

/-! # Complete none, refusal without residue, unfinished search and vacuous every -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAttemptOutcomes.Controls

open ContextualConjunctiveControls ContextualQueryAnswersControls
open ContextualSelectionViews.Controls (base)
open ConstraintMultisetRewriting.Controls (A)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def completeSearch : Search queries locals captures (O := Nat) (Γ := []) (sort := ()) :=
  ⟨[], single, alternatives, domain, budget⟩
def emptySearch : Search queries locals captures (O := Nat) (Γ := []) (sort := ()) :=
  ⟨[], single, alternatives, ∅, budget⟩
def unfinishedSearch : Search queries locals captures (O := Nat) (Γ := []) (sort := ()) :=
  ⟨[], single, alternatives, domain, fun _ => 0⟩
def partialSearch : Search queries locals captures (O := Nat) (Γ := []) (sort := ()) :=
  ⟨[], single, alternatives, domain, fun chosen => if chosen ⟨0, by decide⟩ = 1 then 4 else 0⟩

theorem completeSearch_ready : SourceReady completeSearch .one := by
  refine ⟨tuple 1, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨(ContextualConjunctiveAbsence.mem_candidates domain _).mpr (fun _ => by change 1 ∈ domain; decide +kernel),
    (actual_jobs_finish 1 (by decide +kernel)).2⟩

theorem completed_empty_search_reports_none :
    Attempt emptySearch .one A StagedSourceEffects.Controls.label StagedSourceEffects.Controls.code
      StagedSourceEffects.Controls.good .none StagedSourceEffects.Controls.good := by
  apply Attempt.none rfl
  · decide +kernel
  · decide +kernel

theorem refusal_keeps_the_consumable_and_standing_rule :
    Attempt completeSearch .one A StagedSourceEffects.Controls.label StagedSourceEffects.Controls.code
      StagedSourceEffects.Controls.bad .refused StagedSourceEffects.Controls.bad ∧
      0 ∈ StagedSourceEffects.Controls.bad.present := by
  exact ⟨.refused completeSearch_ready StagedSourceEffects.Controls.bad_code_is_not_admitted, by decide +kernel⟩

theorem unfinished_search_reports_incomplete :
    Attempt unfinishedSearch .one A StagedSourceEffects.Controls.label StagedSourceEffects.Controls.code
      StagedSourceEffects.Controls.good .incomplete StagedSourceEffects.Controls.good :=
  .incomplete unfinished_jobs_are_not_a_complete_empty_answer.1

theorem unfinished_search_cannot_report_none (after : Configuration _ Nat) :
    ¬ Attempt unfinishedSearch .one A StagedSourceEffects.Controls.label StagedSourceEffects.Controls.code
      StagedSourceEffects.Controls.good .none after :=
  Attempt.unfinished_cannot_report_none unfinished_jobs_are_not_a_complete_empty_answer.1

theorem every_fires_on_a_complete_empty_source :
    Attempt emptySearch .every A StagedSourceEffects.Controls.label []
      StagedSourceEffects.Controls.good .fired StagedSourceEffects.Controls.good := by
  apply Attempt.fired (show SourceReady emptySearch .every from by change emptySearch.complete = true; decide +kernel)
  exact ⟨A.identity, by intro equation member; cases member⟩

theorem partial_search_has_one_ready_answer : SourceReady partialSearch .one := by
  refine ⟨tuple 1, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨(ContextualConjunctiveAbsence.mem_candidates domain _).mpr (fun _ => by change 1 ∈ domain; decide +kernel),
    (actual_jobs_finish 1 (by decide +kernel)).2⟩

theorem partial_search_is_not_a_complete_table : partialSearch.complete = false := by
  cases test : partialSearch.complete with
  | false => rfl
  | true =>
      have all : ∀ chosen ∈ ContextualConjunctiveAbsence.candidates domain single.length,
          ContextualQueryAnswers.closed (ContextualQueryAnswers.scan queries locals captures [] single alternatives
            partialSearch.budget chosen) = true := of_decide_eq_true test
      have second := all (tuple 2) ((ContextualConjunctiveAbsence.mem_candidates domain _).mpr
        (fun _ => by change 2 ∈ domain; decide +kernel))
      have unfinished : ContextualQueryAnswers.closed (ContextualQueryAnswers.scan queries locals captures [] single alternatives
          partialSearch.budget (tuple 2)) = false := by
        obtain ⟨Next, next, candidate, model⟩ := job_has_a_model 2
        unfold ContextualQueryAnswers.scan
        rw [ContextualFrameWorklist.run_eq_local_on_model _ _ next candidate model]
        decide +kernel
      rw [unfinished] at second
      cases second

theorem one_answer_does_not_wait_for_the_whole_table :
    partialSearch.complete = false ∧
      Attempt partialSearch .one A StagedSourceEffects.Controls.label StagedSourceEffects.Controls.code
        StagedSourceEffects.Controls.good .fired
        (ConditionalSchedule.follow StagedSourceEffects.Controls.label StagedSourceEffects.Controls.good
          (StagedSourceEffects.Controls.code.map StagedSourceEffects.Instruction.raw)) :=
  ⟨partial_search_is_not_a_complete_table,
    .fired partial_search_has_one_ready_answer StagedSourceEffects.Controls.good_code_executes⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAttemptOutcomes.Controls
