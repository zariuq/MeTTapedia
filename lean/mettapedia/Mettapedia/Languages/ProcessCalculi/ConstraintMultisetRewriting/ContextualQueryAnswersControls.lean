import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveControls

/-! # Complete contextual tables with open rows and independent alternatives -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswersControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching
open ContextualConjunctiveQueries
open ContextualConjunctiveControls
open ContextualSelectionViews.Controls (base)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

def single : List Pattern := [p x]
def alternatives (occurrence : Nat) : Stored :=
  if occurrence = 1 then .shared (p a)
  else if occurrence = 2 then .shared (p b)
  else .schema universalRow
def domain : Finset Nat := {1, 2, 3}
def budget (_ : Fin single.length → Nat) : Nat := 4
def tuple (occurrence : Nat) : Fin single.length → Nat := fun _ => occurrence

theorem tuple_eq (chosen : Fin single.length → Nat) : chosen = tuple (chosen ⟨0, by decide⟩) := by
  funext port
  have only : port = ⟨0, by decide⟩ := by
    apply Fin.ext
    change port.val = 0
    have bound : port.val < 1 := by simpa only [single, List.length_cons, List.length_nil] using port.isLt
    omega
  subst port
  rfl

theorem job_has_a_model (occurrence : Nat) :
    ∃ (Next : Type) (next : Next → MetaArity base)
      (candidate : Assignment (family queries locals captures) next),
      ContextualResidual.Models candidate
        (ContextualQueryAnswers.problemAt queries locals captures [] single alternatives (tuple occurrence)) := by
  let value := if occurrence = 2 then b else a
  have matched : ContextualConjunctiveQueries.Matches queries locals captures (generator captures)
      single alternatives (tuple occurrence) := by
    refine ⟨Extension.identity captures, (fun _ => value), (fun _ => value), ?_⟩
    intro port
    have only : port = ⟨0, by decide⟩ := by
      apply Fin.ext
      change port.val = 0
      have bound : port.val < 1 := by simpa only [single, List.length_cons, List.length_nil] using port.isLt
      omega
    subst port
    by_cases first : occurrence = 1
    · subst occurrence
      with_unfolding_all rfl
    · by_cases second : occurrence = 2
      · subst occurrence
        with_unfolding_all rfl
      · simp only [tuple, alternatives, first, second, if_false]
        dsimp only [value]
        rw [if_neg second]
        with_unfolding_all rfl
  obtain ⟨Next, next, candidate, solved⟩ := match_gives_joint_model queries locals captures
    (generator captures) [] single alternatives (tuple occurrence) (by intro equation member; cases member) matched
  exact ⟨Next, next, candidate, (ContextualResidual.models_observeProblem candidate _).mpr solved⟩

/-- The checked combined driver agrees with its local implementation on
these independently inhabited jobs; reduction does not choose a model. -/
theorem actual_jobs_finish (occurrence : Nat) (member : occurrence ∈ domain) :
    ContextualQueryAnswers.closed
        (ContextualQueryAnswers.scan queries locals captures [] single alternatives budget (tuple occurrence)) = true ∧
      ContextualQueryAnswers.successful
        (ContextualQueryAnswers.scan queries locals captures [] single alternatives budget (tuple occurrence)) = true := by
  obtain ⟨Next, next, candidate, solved⟩ := job_has_a_model occurrence
  unfold ContextualQueryAnswers.scan
  rw [ContextualFrameWorklist.run_eq_local_on_model _ _ next candidate solved]
  simp only [domain, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl <;> decide +kernel

theorem the_actual_table_is_complete :
    ContextualQueryAnswers.certifies queries locals captures [] single alternatives domain budget = true := by
  apply decide_eq_true
  intro chosen member
  have present := (ContextualConjunctiveAbsence.mem_candidates domain chosen).mp member ⟨0, by decide⟩
  rw [tuple_eq chosen]
  exact (actual_jobs_finish _ present).1

theorem the_answer_tuples_are_exact :
    ContextualQueryAnswers.answers queries locals captures [] single alternatives domain budget =
      ContextualConjunctiveAbsence.candidates domain single.length := by
  ext chosen
  change chosen ∈ (ContextualConjunctiveAbsence.candidates domain single.length).filter
    (fun choice => ContextualQueryAnswers.successful
      (ContextualQueryAnswers.scan queries locals captures [] single alternatives budget choice) = true) ↔ _
  rw [Finset.mem_filter, and_iff_left_iff_imp]
  intro member
  have present := (ContextualConjunctiveAbsence.mem_candidates domain chosen).mp member ⟨0, by decide⟩
  rw [tuple_eq chosen]
  exact (actual_jobs_finish _ present).2

theorem every_physical_alternative_is_retained :
    (ContextualQueryAnswers.answers queries locals captures [] single alternatives domain budget).image
      (fun chosen => chosen ⟨0, by decide⟩) = domain := by
  rw [the_answer_tuples_are_exact]
  ext occurrence
  constructor
  · rintro member
    obtain ⟨chosen, present, rfl⟩ := Finset.mem_image.mp member
    exact (ContextualConjunctiveAbsence.mem_candidates domain chosen).mp present _
  · intro member
    exact Finset.mem_image.mpr ⟨tuple occurrence,
      (ContextualConjunctiveAbsence.mem_candidates domain _).mpr (fun _ => member), rfl⟩

theorem unfinished_jobs_are_not_a_complete_empty_answer :
    ContextualQueryAnswers.certifies queries locals captures [] single alternatives domain (fun _ => 0) = false ∧
      ContextualQueryAnswers.answers queries locals captures [] single alternatives domain (fun _ => 0) = ∅ := by
  decide +kernel

theorem empty_domain_and_empty_conjunction_differ :
    (ContextualQueryAnswers.answers queries locals captures [] single alternatives ∅ budget).card = 0 ∧
      (ContextualQueryAnswers.answers queries locals captures [] [] alternatives ∅ (fun _ => 0)).card = 1 ∧
      ContextualQueryAnswers.certifies queries locals captures [] [] alternatives ∅ (fun _ => 0) = true := by
  decide +kernel

def reading (value : Captured) : Assignment (family queries locals captures) captures :=
  combinedAssignment queries locals captures (fun _ => value) (fun _ => value)
    (generator captures) (generator captures)

/-- Both models of one recorded answer expose their distinct query values.
The equal physical identity does not collapse those alternative readings. -/
theorem schema_accepts_two_readings :
    ContextualResidual.Models (reading a)
        (ContextualQueryAnswers.problemAt queries locals captures [] single alternatives (tuple 3)) ∧
      ContextualResidual.Models (reading b)
        (ContextualQueryAnswers.problemAt queries locals captures [] single alternatives (tuple 3)) ∧
      reading a (.inl 0) = a ∧ reading b (.inl 0) = b ∧ a ≠ b := by
  refine ⟨?_, ?_, rfl, rfl, by intro same; cases same⟩
  all_goals
    apply (ContextualResidual.models_observeProblem _ _).mpr
    intro equation member
    change equation ∈ [
      (rowView queries locals captures ⟨0, by decide⟩ (alternatives 3),
        queryView queries locals captures (p x))] at member
    obtain rfl := List.mem_singleton.mp member
    with_unfolding_all rfl

theorem the_schema_answer_retains_every_future_solution :
    ∃ update : ContextualFrameUpdate.Update
        (ContextualQueryAnswers.problemAt queries locals captures [] single alternatives (tuple 3)),
      ContextualQueryAnswers.scan queries locals captures [] single alternatives budget (tuple 3) = .residual update ∧
      update.remaining = [] ∧
      ∀ (Next : Type) (next : Next → MetaArity base)
        (candidate : Assignment (family queries locals captures) next),
        ContextualResidual.Models candidate
          (ContextualQueryAnswers.problemAt queries locals captures [] single alternatives (tuple 3)) ↔
          ∃ residual : Assignment update.declaration next,
            ∀ identity, candidate identity = instantiate residual (update.answer identity) := by
  apply ContextualQueryAnswers.answer_factors queries locals captures [] single alternatives domain budget (tuple 3)
  rw [the_answer_tuples_are_exact]
  exact (ContextualConjunctiveAbsence.mem_candidates domain _).mpr
    (fun _ => show (3 : Nat) ∈ domain from by decide +kernel)

/-- A repeated read is a candidate tuple; freshening is per port, so its two
pattern instances may differ. The table does not impose injective reads. -/
theorem aliased_schema_ports_are_admitted :
    ContextualQueryAnswers.certifies queries locals captures [] independentPatterns schemaRows {7} (fun _ => 4) = true ∧
      (fun _ => 7) ∈ ContextualQueryAnswers.answers queries locals captures []
        independentPatterns schemaRows {7} (fun _ => 4) := by
  have model := match_gives_joint_model queries locals captures (generator captures) [] independentPatterns schemaRows
    (fun _ => 7) (by intro equation member; cases member) one_schema_row_may_be_read_at_two_independent_instances
  obtain ⟨Next, next, candidate, solved⟩ := model
  have exactRun := ContextualFrameWorklist.run_eq_local_on_model 4
    (ContextualQueryAnswers.problemAt queries locals captures [] independentPatterns schemaRows (fun _ => 7))
    next candidate ((ContextualResidual.models_observeProblem candidate _).mpr solved)
  have finished : ContextualQueryAnswers.closed
      (ContextualQueryAnswers.scan queries locals captures [] independentPatterns schemaRows (fun _ => 4) (fun _ => 7)) = true ∧
      ContextualQueryAnswers.successful
      (ContextualQueryAnswers.scan queries locals captures [] independentPatterns schemaRows (fun _ => 4) (fun _ => 7)) = true := by
    unfold ContextualQueryAnswers.scan
    rw [exactRun]
    decide +kernel
  constructor
  · apply decide_eq_true
    intro chosen member
    have same : chosen = fun _ => 7 := funext fun port =>
      Finset.mem_singleton.mp ((ContextualConjunctiveAbsence.mem_candidates {7} chosen).mp member port)
    rw [same]
    exact finished.1
  · exact Finset.mem_filter.mpr
      ⟨(ContextualConjunctiveAbsence.mem_candidates {7} _).mpr (fun _ => Finset.mem_singleton_self _), finished.2⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswersControls
