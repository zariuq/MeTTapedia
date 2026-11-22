import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAtomicIdentityControls

/-!
# Native count queries retain actual row dependencies

The existing solver-backed firing consumes symbol 1 and publishes symbol 2
at a fresh occurrence. Its regressed count is one in every future model.
A point query admits that same firing and preserves its actual output
observations. Count zero is refused despite the raw firing existing. A
separating insertion then shows why the point query alone is insufficient
for dynamic guard revalidation. A query over actual conditional row labels
detects the missing dependency.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmissionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows
open ContextualPredicateQueryAdmission
open ContextualPrefixPublicationControls (DataOperator base none captures symbol)
open ContextualAtomicIdentityControls (initial fresh_name_repair)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

abbrev nativeFamily := ContextualActivatedStep.target none captures
def rows (occurrence : Nat) : Row none nativeFamily [] () :=
  ofStored none nativeFamily (.shared (symbol (if occurrence = 0 then 1 else 2)))

def countCondition (number : Nat) (candidate : Candidate nativeFamily) : Prop :=
  ContextualGuardRegression.entryCondition none none candidate.assignment rows rows {0} {0} {1}
    (.count (symbol 2) number)

theorem input_region_empty (candidate : Candidate nativeFamily) :
    ContextualConditionalGuards.region none candidate.assignment rows {0} (symbol 2) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro occurrence member
  obtain ⟨present, matched⟩ := (ContextualConditionalGuards.mem_region _ _ _ _ _ _).mp member
  have zero := Finset.mem_singleton.mp present
  subst occurrence
  rw [rows, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff] at matched
  change symbol (decl := candidate.declarations) 2 = symbol 1 at matched
  have impossible : (2 : Nat) = 1 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj matched).1)
  omega

theorem output_region_one (candidate : Candidate nativeFamily) :
    ContextualConditionalGuards.region none candidate.assignment rows {1} (symbol 2) = {1} := by
  ext occurrence
  rw [ContextualConditionalGuards.mem_region]
  constructor
  · exact And.left
  · intro member
    have one := Finset.mem_singleton.mp member
    subst occurrence
    refine ⟨Finset.mem_singleton_self _, ?_⟩
    rw [rows, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
    rfl

theorem count_condition_iff (number : Nat) (candidate : Candidate nativeFamily) :
    countCondition number candidate ↔ 1 = number := by
  change (ContextualConditionalGuards.region none candidate.assignment rows {0} (symbol 2)).card -
    (ContextualConditionalGuards.region none candidate.assignment rows {0} (symbol 2)).card +
      (ContextualConditionalGuards.region none candidate.assignment rows {1} (symbol 2)).card = number ↔ _
  rw [input_region_empty, output_region_one]
  rfl

/-- Predicate-query admission retains the same actual firing, solver budget and published value. -/
theorem an_actual_native_firing_with_a_point_query (fuel : Nat) :
    ∃ observed : WithQueries none (initial.native ∅),
      observed.firing.fuel = fuel ∧ observed.firing.target.present = {1} ∧
        observed.queries = [liftPoint (ofCondition (countCondition 1) 0)] ∧
        ∀ (Future : Type) (future : Future → MetaArity base)
          (candidate : Assignment observed.firing.target.declarations future)
          (pattern : Term (signature base future) [] ()),
          Matches (ContextualPublication.privateFamily none observed.firing.update.declaration)
            observed.firing.target.declarations candidate pattern (observed.firing.target.rows 1) ↔ pattern = symbol 2 := by
  obtain ⟨firing, budget, physical, meaning⟩ := fresh_name_repair fuel
  obtain ⟨observed, same, queries⟩ := (admit_condition_iff none firing (countCondition 1) 0 (by decide +kernel)).mpr
    (fun Future future candidate _model => (count_condition_iff 1 ⟨Future, future, candidate⟩).mpr rfl)
  refine ⟨observed, ?_, ?_, queries, ?_⟩
  · rw [same]
    exact budget
  · rw [same]
    exact physical
  · rw [same]
    exact meaning

theorem the_wrong_count_has_no_query_admitted_firing
    (firing : ContextualConditionalExecution.Firing none (initial.native ∅)) :
    ¬ ∃ observed : WithQueries none (initial.native ∅),
      observed.firing = firing ∧ observed.queries = [liftPoint (ofCondition (countCondition 0) 0)] := by
  intro observed
  have wrong := (admit_condition_iff none firing (countCondition 0) 0 (by decide +kernel)).mp observed
  obtain ⟨Future, future, candidate, model⟩ := firing.admitted.solvable
  have impossible := (count_condition_iff 0 ⟨Future, future, candidate⟩).mp (wrong Future future candidate model)
  omega

namespace PhantomInsertion

open ContextualAtomicIdentityControls (freshSelection fusedRule fusedOutputs)

def storedRows (occurrence : Nat) : Row none captures [] () :=
  ofStored none captures (.shared (symbol (if occurrence = 3 then 2 else 1)))

abbrev state (inserted : Bool) : ContextualClauseSourceState.World none Nat [] () where
  Names := Unit
  equality := inferInstance
  declarations := captures
  equations := []
  present := if inserted then {0, 3} else {0}
  rows := storedRows

theorem admitted (inserted : Bool) : ContextualConditionalExecution.Admitted none
    ((state inserted).native ∅) fusedRule freshSelection fusedOutputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    ?_, (by cases inserted <;> decide +kernel), by decide +kernel, ?_, ?_, ?_⟩
  · cases inserted <;> decide +kernel
  · cases inserted <;> decide +kernel
  · with_unfolding_all exact ContextualAtomicIdentityControls.fresh_native_admission.solvable
  · intro check member
    cases member

theorem the_marker_query_admits_after_a_matching_insertion (fuel : Nat) :
    ∃ observed : WithQueries none ((state true).native ∅),
      observed.firing.fuel = fuel ∧ observed.firing.target.present = {1, 3} ∧
        observed.queries = [liftPoint (ofCondition (countCondition 1) 0)] ∧
        ∀ (Future : Type) (future : Future → MetaArity base)
          (candidate : Assignment observed.firing.target.declarations future),
          ¬ ContextualConditionalGuards.Holds (ContextualPublication.privateFamily none observed.firing.update.declaration)
            candidate observed.firing.target.rows observed.firing.target.present (.count (symbol 2) 1) := by
  obtain ⟨firing, _authored, selected, outputs, kinds, budget⟩ :=
    ContextualConditionalExecution.realize_at_fuel none ((state true).native ∅) fusedRule freshSelection
      fusedOutputs (fun _ => false) (admitted true) fuel
  obtain ⟨observed, same, queries⟩ := (admit_condition_iff none firing (countCondition 1) 0 (by decide +kernel)).mpr
    (fun Future future candidate _model => (count_condition_iff 1 ⟨Future, future, candidate⟩).mpr rfl)
  refine ⟨observed, ?_, ?_, queries, ?_⟩
  · rw [same]
    exact budget
  · rw [same, firing.physical_result, selected]
    decide +kernel
  · rw [same]
    intro Future future candidate counted
    have first : Matches (ContextualPublication.privateFamily none firing.update.declaration)
        firing.target.declarations candidate (symbol 2) (firing.target.rows 1) := by
      rw [firing.shared_row 1 (by rw [selected]; decide +kernel) (by rw [kinds]), outputs]
      rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
      rfl
    have third : Matches (ContextualPublication.privateFamily none firing.update.declaration)
        firing.target.declarations candidate (symbol 2) (firing.target.rows 3) := by
      apply (firing.retained_matches 3 (by rw [selected]; decide +kernel) future candidate _).mpr
      dsimp only [ContextualClauseSourceState.World.native, state, storedRows]
      rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
      rfl
    have physical : firing.target.present = {1, 3} := by
      rw [firing.physical_result, selected]
      decide +kernel
    have subset : {1, 3} ⊆ ContextualConditionalGuards.region
        (ContextualPublication.privateFamily none firing.update.declaration) candidate firing.target.rows
          firing.target.present (symbol 2) := by
      intro occurrence member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · exact (ContextualConditionalGuards.mem_region _ _ _ _ _ _).mpr ⟨by rw [physical]; decide +kernel, first⟩
      · exact (ContextualConditionalGuards.mem_region _ _ _ _ _ _).mpr ⟨by rw [physical]; decide +kernel, third⟩
    have bound := Finset.card_le_card subset
    change (ContextualConditionalGuards.region _ candidate firing.target.rows firing.target.present (symbol 2)).card = 1 at counted
    rw [counted] at bound
    have two : ({1, 3} : Finset Nat).card = 2 := by decide +kernel
    omega

theorem actual_data_query_refuses_the_phantom
    (firing : ContextualConditionalExecution.Firing none ((state true).native ∅)) :
    ¬ ∃ observed : WithQueries none ((state true).native ∅),
      observed.firing = firing ∧ observed.queries = [matchingQuery none (symbol 2) ∅] := by
  rintro ⟨observed, _same, queries⟩
  have asked := observed.observations (matchingQuery none (symbol 2) ∅)
    (by rw [queries]; exact List.mem_singleton_self _)
  obtain ⟨Future, future, candidate, model⟩ := observed.firing.admitted.solvable
  have absent := (matching_empty_iff none (symbol 2)
    (ContextualConditionalExecution.guardRows none captures storedRows) (state true).present
    ⟨Future, future, candidate⟩).mp (asked Future future candidate model)
  apply absent 3 (by decide +kernel)
  have actual : ContextualConditionalExecution.guardRows none captures storedRows 3 =
      ofStored none nativeFamily (.shared (symbol 2)) := by with_unfolding_all rfl
  rw [actual, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]

theorem actual_data_query_admits_the_same_program_before_the_insertion (fuel : Nat) :
    ∃ observed : WithQueries none ((state false).native ∅),
      observed.firing.fuel = fuel ∧ observed.queries = [matchingQuery none (symbol 2) ∅] := by
  obtain ⟨firing, _authored, _selected, _outputs, _kinds, budget⟩ :=
    ContextualConditionalExecution.realize_at_fuel none ((state false).native ∅) fusedRule freshSelection
      fusedOutputs (fun _ => false) (admitted false) fuel
  refine ⟨⟨firing, [matchingQuery none (symbol 2) ∅], ?_⟩, budget, rfl⟩
  intro query member
  have only := List.mem_singleton.mp member
  subst query
  apply (matching_ask_empty_iff none _ (symbol 2) _ _).mpr
  intro Future future candidate _model occurrence present matched
  have zero := Finset.mem_singleton.mp present
  subst occurrence
  have actual : ContextualConditionalExecution.guardRows none captures storedRows 0 =
      ofStored none nativeFamily (.shared (symbol 1)) := by with_unfolding_all rfl
  rw [actual, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff] at matched
  change symbol (decl := future) 2 = symbol 1 at matched
  have impossible : (2 : Nat) = 1 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj matched).1)
  omega

/-- The inserted symbol 2 is unrelated to an absence query for symbol 7. -/
theorem an_unrelated_actual_data_query_is_still_admitted (fuel : Nat) :
    ∃ observed : WithQueries none ((state true).native ∅),
      observed.firing.fuel = fuel ∧ observed.queries = [matchingQuery none (symbol 7) ∅] := by
  obtain ⟨firing, _authored, _selected, _outputs, _kinds, budget⟩ :=
    ContextualConditionalExecution.realize_at_fuel none ((state true).native ∅) fusedRule freshSelection
      fusedOutputs (fun _ => false) (admitted true) fuel
  refine ⟨⟨firing, [matchingQuery none (symbol 7) ∅], ?_⟩, budget, rfl⟩
  intro query member
  have only := List.mem_singleton.mp member
  subst query
  apply (matching_ask_empty_iff none _ (symbol 7) _ _).mpr
  intro Future future candidate _model occurrence _present matched
  have actual : ContextualConditionalExecution.guardRows none captures storedRows occurrence =
      ofStored none nativeFamily (.shared (symbol (if occurrence = 3 then 2 else 1))) := by with_unfolding_all rfl
  rw [actual, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff] at matched
  change symbol (decl := future) 7 = symbol (if occurrence = 3 then 2 else 1) at matched
  have impossible : (7 : Nat) = if occurrence = 3 then 2 else 1 :=
    DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj matched).1)
  split_ifs at impossible <;> omega

theorem the_unrelated_query_would_detect_its_own_matching_fact (candidate : Candidate nativeFamily) :
    (matchingQuery none (symbol 7) (∅ : Finset Nat)).region candidate
      (99, ofStored none nativeFamily (.shared (symbol 7))) = true := by
  classical
  change decide (Matches none nativeFamily candidate.assignment
    (instantiate candidate.assignment (symbol 7)) (ofStored none nativeFamily (.shared (symbol 7)))) = true
  apply decide_eq_true_eq.mpr
  rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]

end PhantomInsertion

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmissionControls
