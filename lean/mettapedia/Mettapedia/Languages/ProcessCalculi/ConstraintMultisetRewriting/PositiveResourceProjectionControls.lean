import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceSchedules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences

/-!
# Resource-planning controls for physical reads and shared substitution

A repeated read port uses one resource, whereas a repeated take needs two.
The constructive converse allocates distinct output occurrences even when
their values coincide. One shared solution also interprets surviving caller
syntax; a local solve that leaves that frame arbitrary is rejected.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjection.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls

noncomputable section

local instance : DecidableEq (Term signature) := Classical.decEq _

theorem shared_read_has_a_complete_store_model :
    A.Models zero (sharedRead.problem label readsRule singletonStore) := by
  intro equation member
  have same : equation = (Term.var (σ := signature) 0, .var 0) := by
    simpa [Selection.problem, Selection.equations, sharedRead, readsRule, singletonStore, label] using member
  subst equation
  rfl

theorem repeated_read_ports_use_one_resource :
    readFootprint A zero label sharedRead = ({Term.const (σ := signature) 0} : Multiset (Term signature)) := by
  simp [readFootprint, realized, sharedRead, labels, label, zero, FirstOrder.action]
  exact Subst.single_eq _ _

/-- The raw read-list rendering incorrectly demands two resources from a
store with one occurrence, despite the valid actual firing. -/
theorem raw_read_list_is_not_the_linear_demand :
    ¬ ((readsRule.read.map (A.apply zero) : Multiset (Term signature)) ≤
      labels (realized A zero label) singletonStore.present) := by
  intro fits
  have count := Multiset.card_le_card fits
  norm_num [readsRule, singletonStore, labels] at count

theorem normalized_read_rendering_preserves_the_actual_firing :
    (resources A zero label).takeRepublish.Enables
      (labels (realized A zero label) singletonStore.present)
      (site := ⟨readsRule⟩) ⟨sharedRead⟩ ∧
      labels (realized A zero label) (sharedRead.result label readsRule singletonStore).present =
        (resources A zero label).takeRepublish.fire
          (labels (realized A zero label) singletonStore.present)
          (site := ⟨readsRule⟩) ⟨sharedRead⟩ := by
  classical
  exact atomic_linear_rendering A rfl two_reads_share_one_occurrence shared_read_has_a_complete_store_model

theorem source_take_multiplicity_cannot_be_deduplicated :
    ¬ duplicateTake.Valid A label twoTakes singletonStore ∧
      distinctTake.Valid A label twoTakes duplicateValuedStore :=
  ⟨cannot_consume_one_occurrence_twice, equal_values_allow_distinct_consumption⟩

theorem the_frame_uses_the_whole_firing_solution (assignment : Subst signature)
    (solved : A.Models assignment (callSelection.result label callRule initial).equations) :
    1 ∈ (callSelection.result label callRule initial).present ∧
      realized A assignment label 1 = .const 0 :=
  ⟨caller_frame_survives, caller_binding_reaches_frame assignment solved⟩

def both : Subst signature := fun identity => if identity = 0 then .const 0 else .const 1

def duplicateOutputs : RuleInstance (Term signature) :=
  ⟨[.const 0, .const 0], [], [(.var 1, .const 1)], [], [.var 1, .var 1]⟩

abbrev Id := IndexedOccurrences.Occurrence (Term signature)
def indexedLabel : Id → Term signature := IndexedOccurrences.label
def indexedWorld : Finset Id := {(0, Term.var (σ := signature) 0), (1, Term.var (σ := signature) 0), (2, Term.var (σ := signature) 1)}
def indexedBefore : Configuration (Term signature) Id := ⟨[], indexedWorld⟩

theorem the_shared_ground_frame_decomposition :
    labels (realized A both indexedLabel) indexedBefore.present =
      ({Term.const (σ := signature) 1} : Multiset (Term signature)) +
        (duplicateOutputs.take.map (A.apply both) : Multiset (Term signature)) := by
  classical
  simp [labels, indexedBefore, indexedWorld, realized, indexedLabel, IndexedOccurrences.label,
    duplicateOutputs, FirstOrder.action, Subst.applyTerm, both]
  change (([Term.const (σ := signature) 0, .const 0, .const 1] : List (Term signature)) : Multiset (Term signature)) =
    (([Term.const (σ := signature) 1, .const 0, .const 0] : List (Term signature)) : Multiset (Term signature))
  apply Multiset.coe_eq_coe.mpr
  exact (List.perm_append_comm : List.Perm
    ([Term.const (σ := signature) 1] ++ [Term.const (σ := signature) 0, .const 0] : List (Term signature))
    ([Term.const (σ := signature) 0, .const 0] ++ [Term.const (σ := signature) 1])).symm

theorem an_actual_selection_realizes_the_bag_frame :
    ∃ selection : Selection Id, selection.Valid A indexedLabel duplicateOutputs indexedBefore ∧
      A.Models both (selection.result indexedLabel duplicateOutputs indexedBefore).equations ∧
      selection.taken.length = 2 ∧ selection.made.length = 2 ∧ selection.made.Nodup ∧
      labels (realized A both indexedLabel)
        (selection.result indexedLabel duplicateOutputs indexedBefore).present =
          ({Term.const (σ := signature) 1, Term.const (σ := signature) 1, Term.const (σ := signature) 1} : Multiset (Term signature)) := by
  classical
  have supply : ∀ (world : Finset Id) (value : Term signature),
      ∃ occurrence, occurrence ∉ world ∧ indexedLabel occurrence = value :=
    IndexedOccurrences.supply
  have tells : A.Models both duplicateOutputs.tell := by
    intro equation member
    have same : equation = (Term.var (σ := signature) 1, .const 1) := by
      simpa [duplicateOutputs] using member
    subst equation
    rfl
  obtain ⟨selection, valid, solved, result⟩ := lift_no_read_frame A both indexedLabel rfl supply
    duplicateOutputs rfl rfl indexedBefore (A.models_nil both) tells {Term.const (σ := signature) 1}
    the_shared_ground_frame_decomposition
  refine ⟨selection, valid, solved, ?_, ?_, valid.output_distinct, ?_⟩
  · exact valid.take_length.symm
  · have lengths := congrArg List.length valid.outputs
    simpa [duplicateOutputs] using lengths
  · change _ = (([Term.const (σ := signature) 1, .const 1, .const 1] : List (Term signature)) : Multiset (Term signature))
    simpa [duplicateOutputs, FirstOrder.action, Subst.applyTerm, both] using result

theorem a_locally_solved_call_cannot_leave_its_frame_arbitrary :
    ¬ A.Models one (callSelection.result label callRule initial).equations :=
  caller_value_cannot_stay_arbitrary

def oneTake : RuleInstance (Term signature) := ⟨[.var 0], [], [], [], []⟩
def takeOne : Selection Nat := ⟨[1], [], []⟩

theorem one_take_is_enabled : takeOne.Valid A label oneTake singletonStore := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zero, ?_⟩, ?_⟩
  · intro equation member
    have same : equation = (Term.var (σ := signature) 0, .var 0) := by
      simpa [Selection.problem, Selection.equations, singletonStore, takeOne, oneTake, label] using member
    subst equation
    rfl
  · simp [oneTake]

/-- Neither action produces a premise for the other, but reading before
consumption works and the reverse order does not. Produced-to-use edges
alone therefore cannot determine the permitted orders of these actions. -/
theorem a_read_consumption_dependency_has_no_produced_premise :
    readsRule.produce = [] ∧ oneTake.produce = [] ∧
      takeOne.Valid A label oneTake (sharedRead.result label readsRule singletonStore) ∧
        ¬ sharedRead.Valid A label readsRule (takeOne.result label oneTake singletonStore) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zero, ?_⟩, ?_⟩
    · intro equation member
      have same : equation = (Term.var (σ := signature) 0, .var 0) := by
        simpa [Selection.problem, Selection.result, Selection.equations, singletonStore,
          takeOne, oneTake, readsRule, sharedRead, label] using member
      subst equation
      rfl
    · simp [oneTake]
  · intro valid
    have present := valid.occurrences.kept_subset (show 1 ∈ sharedRead.commit.kept by decide)
    simp [Selection.result, Selection.commit, fire, takeOne, singletonStore] at present

def readThenTake : List (ConditionalSchedule.Firing (Term signature) Nat) :=
  [(readsRule, sharedRead), (oneTake, takeOne)]

theorem the_reader_consumer_schedule_is_executable :
    ConditionalSchedule.Executable A label singletonStore readThenTake := by
  refine ⟨two_reads_share_one_occurrence,
    a_read_consumption_dependency_has_no_produced_premise.2.2.1, zero, ?_⟩
  intro equation member
  have same : equation = (Term.var (σ := signature) 0, .var 0) := by
    simpa [ConditionalSchedule.follow, Selection.result, Selection.problem, Selection.equations,
      singletonStore, sharedRead, readsRule, takeOne, oneTake, label] using member
  subst equation
  rfl

theorem the_whole_schedule_has_one_shared_model :
    A.Models zero (ConditionalSchedule.follow label singletonStore readThenTake).equations := by
  intro equation member
  have same : equation = (Term.var (σ := signature) 0, .var 0) := by
    simpa [readThenTake, ConditionalSchedule.follow, Selection.result, Selection.problem, Selection.equations,
      singletonStore, sharedRead, readsRule, takeOne, oneTake, label] using member
  subst equation
  rfl

theorem the_actual_schedule_is_an_ordered_resource_run :
    (resources A zero label).Fires (PositiveResourceSchedules.entries A zero label readThenTake)
      (labels (realized A zero label) singletonStore.present)
      (labels (realized A zero label) (ConditionalSchedule.follow label singletonStore readThenTake).present) :=
  PositiveResourceSchedules.realized_fires A zero label rfl readThenTake singletonStore
    the_reader_consumer_schedule_is_executable the_whole_schedule_has_one_shared_model

theorem the_compiled_schedule_is_the_same_ordered_resource_run :
    (resources A zero label).Fires (PositiveResourceSchedules.entries A zero label readThenTake)
      (labels (realized A zero label) singletonStore.present)
      (labels (realized A zero label) ((ConditionalSchedule.compile label readThenTake).result singletonStore).present) := by
  have admitted := (ConditionalSchedule.compile_holds_iff A label singletonStore readThenTake).mpr
    the_reader_consumer_schedule_is_executable
  have solved : A.Models zero ((ConditionalSchedule.compile label readThenTake).result singletonStore).equations := by
    rw [ConditionalSchedule.compile_result A label singletonStore readThenTake the_reader_consumer_schedule_is_executable]
    exact the_whole_schedule_has_one_shared_model
  exact PositiveResourceSchedules.compiled_realized_fires A zero label rfl readThenTake singletonStore admitted solved

theorem the_reverse_schedule_is_not_executable :
    ¬ ConditionalSchedule.Executable A label singletonStore [(oneTake, takeOne), (readsRule, sharedRead)] := by
  intro executable
  exact a_read_consumption_dependency_has_no_produced_premise.2.2.2 executable.2.1

def branchRule (value : Nat) : RuleInstance (Term signature) :=
  ⟨[], [], [(.var 0, .const value)], [], [.const 2]⟩
def branchSelection : Selection Nat := ⟨[], [], [5]⟩
def branchLabel (_ : Nat) : Term signature := .const 2
def branchBefore : Configuration (Term signature) Nat := ⟨[], ∅⟩

private theorem branch_is_valid (value : Nat) :
    branchSelection.Valid A branchLabel (branchRule value) branchBefore := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.single 0 (.const value), ?_⟩, ?_⟩
  · intro equation member
    have same : equation = (Term.var (σ := signature) 0, .const value) := by
      simpa [Selection.problem, Selection.equations, branchSelection, branchRule, branchBefore] using member
    subst equation
    rfl
  · simp [branchRule]

/-- Disjoint full solution regions need not give disjoint observations after
the distinguishing variable is projected away from the returned value. -/
theorem incompatible_bindings_can_return_the_same_closed_value :
    branchSelection.Valid A branchLabel (branchRule 0) branchBefore ∧
      branchSelection.Valid A branchLabel (branchRule 1) branchBefore ∧
      ¬ A.Consistent ((branchRule 0).tell ++ (branchRule 1).tell) ∧
      realized A zero branchLabel 5 = realized A one branchLabel 5 ∧
      (branchSelection.result branchLabel (branchRule 0) branchBefore).present =
        (branchSelection.result branchLabel (branchRule 1) branchBefore).present := by
  refine ⟨branch_is_valid 0, branch_is_valid 1, ?_, rfl, rfl⟩
  rintro ⟨assignment, solved⟩
  have zeroModel := solved (.var 0, .const 0) (by simp [branchRule])
  have oneModel := solved (.var 0, .const 1) (by simp [branchRule])
  change assignment 0 = Term.const (σ := signature) 0 at zeroModel
  change assignment 0 = Term.const (σ := signature) 1 at oneModel
  have impossible := zeroModel.symm.trans oneModel
  cases impossible

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjection.Controls
