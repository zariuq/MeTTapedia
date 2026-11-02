import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourceRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadAliasRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadResourceCounterexamples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences

/-!
# Read aliases, exclusive consumption and one shared caller binding

Two equal-valued physical rows remain two read classes. Two ports reading
one class demand one row. A take and a read demand separate physical rows.
Fresh duplicate outputs and retained caller syntax use the same final model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourceControls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls (signature A zero)
open ReadCompatibleResourcePlanning
open PositiveResourceProjection (realized readFootprint)

noncomputable section
local instance : DecidableEq (Term signature) := Classical.decEq _

abbrev Id := IndexedOccurrences.Occurrence (Term signature)
def indexedLabel : Id → Term signature := IndexedOccurrences.label
def first : Id := (1, .var 0)
def second : Id := (2, .var 0)
def oneWorld : Finset Id := {first}
def twoWorld : Finset Id := {first, second}
def oneBefore : Configuration (Term signature) Id := ⟨[], oneWorld⟩
def twoBefore : Configuration (Term signature) Id := ⟨[], twoWorld⟩

def readTwice : RuleInstance (Term signature) := ⟨[], [.var 0, .var 0], [], [], []⟩
def readSource : AdmittedRule A zero := ⟨readTwice, rfl, A.models_nil zero⟩
def repeatPlan : ReadPlan A zero indexedLabel readTwice := ⟨[first, first], .cons rfl (.cons rfl .nil)⟩
def distinctPlan : ReadPlan A zero indexedLabel readTwice := ⟨[first, second], .cons rfl (.cons rfl .nil)⟩

theorem repeated_read_needs_one_row :
    (resources A zero indexedLabel).Enables (labels (realized A zero indexedLabel) oneWorld)
      (site := ⟨readSource⟩) ⟨repeatPlan⟩ := by
  simp [Mettapedia.GSLT.Causality.ResourceInteraction.System.Enables, resources, readSource, readTwice,
    readFootprint, ReadPlan.selection, repeatPlan, oneWorld]

theorem distinct_equal_reads_need_two_rows :
    ¬ (resources A zero indexedLabel).Enables (labels (realized A zero indexedLabel) oneWorld)
      (site := ⟨readSource⟩) ⟨distinctPlan⟩ := by
  intro enabled
  have counts := Multiset.card_le_card enabled
  simp [resources, readSource, readTwice, readFootprint, ReadPlan.selection, distinctPlan,
    oneWorld, first, second, labels] at counts

theorem distinct_equal_reads_fit_two_rows :
    (resources A zero indexedLabel).Enables (labels (realized A zero indexedLabel) twoWorld)
      (site := ⟨readSource⟩) ⟨distinctPlan⟩ := by
  simp [Mettapedia.GSLT.Causality.ResourceInteraction.System.Enables, resources, readSource, readTwice,
    readFootprint, ReadPlan.selection, distinctPlan, twoWorld]

theorem repeated_read_lifts_with_the_same_physical_alias :
    ∃ selection : Selection Id, ∃ realization : ReadRealization A zero indexedLabel repeatPlan selection,
      selection.Valid A indexedLabel readTwice oneBefore ∧ selection.read.length = 2 ∧
      realization.port ⟨0, by decide⟩ = realization.port ⟨1, by decide⟩ := by
  obtain ⟨selection, valid, _, ⟨realization⟩, _⟩ := lift_enabled rfl IndexedOccurrences.supply
    readSource repeatPlan oneBefore (A.models_nil zero) repeated_read_needs_one_row
  exact ⟨selection, realization, valid, realization.read_length,
    (realization.actual_alias_iff _ _).mpr rfl⟩

theorem distinct_equal_reads_lift_to_different_physical_rows :
    ∃ selection : Selection Id, ∃ realization : ReadRealization A zero indexedLabel distinctPlan selection,
      selection.Valid A indexedLabel readTwice twoBefore ∧
      realization.port ⟨0, by decide⟩ ≠ realization.port ⟨1, by decide⟩ := by
  obtain ⟨selection, valid, _, ⟨realization⟩, _⟩ := lift_enabled rfl IndexedOccurrences.supply
    readSource distinctPlan twoBefore (A.models_nil zero) distinct_equal_reads_fit_two_rows
  refine ⟨selection, realization, valid, ?_⟩
  intro same
  have identity := (realization.actual_alias_iff _ _).mp same
  have bad : (1 : Nat) = 2 := congrArg Prod.fst identity
  cases bad

def takeAndRead : RuleInstance (Term signature) := ⟨[.var 0], [.var 0], [], [], []⟩
def exclusiveSource : AdmittedRule A zero := ⟨takeAndRead, rfl, A.models_nil zero⟩
def exclusivePlan : ReadPlan A zero indexedLabel takeAndRead := ⟨[first], .cons rfl .nil⟩

theorem take_and_read_cannot_share_one_physical_row :
    ¬ (resources A zero indexedLabel).Enables (labels (realized A zero indexedLabel) oneWorld)
      (site := ⟨exclusiveSource⟩) ⟨exclusivePlan⟩ := by
  intro enabled
  have counts := Multiset.card_le_card enabled
  simp [resources, exclusiveSource, takeAndRead, readFootprint, ReadPlan.selection, exclusivePlan,
    oneWorld, labels] at counts

theorem empty_footprint_is_not_a_compatible_plan :
    ¬ List.Forall₂
      (fun pattern occurrence => A.apply zero pattern = realized A zero indexedLabel occurrence)
      readTwice.read [] := by
  intro compatible
  have lengths := compatible.length_eq
  cases lengths

def zeroRead : RuleInstance (Term signature) := ⟨[], [.const 0], [], [], []⟩
def wrongValuePrototype : Id := (9, .const 1)

theorem correct_arity_with_wrong_value_is_still_incompatible :
    ¬ List.Forall₂
      (fun pattern occurrence => A.apply zero pattern = realized A zero indexedLabel occurrence)
      zeroRead.read [wrongValuePrototype] := by
  intro compatible
  have same : (Term.const (σ := signature) 0) = .const 1 := compatible.get (i := 0) (by decide) (by decide)
  cases Term.const.inj same

def callerRule : RuleInstance (Term signature) :=
  ⟨[], [.var 0], [(.var 0, .const 0)], [], [.var 0, .var 0]⟩
def callerSource : AdmittedRule A zero where
  rule := callerRule
  noChecks := rfl
  tells := by
    intro equation member
    have same : equation = (Term.var (σ := signature) 0, .const 0) := List.mem_singleton.mp member
    subst equation
    change zero 0 = Term.const (σ := signature) 0
    exact Subst.single_eq _ _
def callerPlan : ReadPlan A zero indexedLabel callerRule := ⟨[first], .cons rfl .nil⟩

theorem caller_enabled :
    (resources A zero indexedLabel).Enables (labels (realized A zero indexedLabel) twoWorld)
      (site := ⟨callerSource⟩) ⟨callerPlan⟩ := by
  change (0 : Multiset (Term signature)) +
    labels (realized A zero indexedLabel) ([first] : List Id).toFinset ≤ _
  simp only [zero_add, List.toFinset_cons, List.toFinset_nil]
  exact labels_mono (by intro row member; simp_all [twoWorld])

theorem caller_binding_and_duplicate_fresh_outputs :
    ∃ selection : Selection Id, selection.Valid A indexedLabel callerRule twoBefore ∧
      selection.made.length = 2 ∧ selection.made.Nodup ∧
      Disjoint selection.made.toFinset twoBefore.present ∧
      second ∈ (selection.result indexedLabel callerRule twoBefore).present ∧
      ∀ final : Subst signature,
        A.Models final (selection.result indexedLabel callerRule twoBefore).equations →
          realized A final indexedLabel second = .const 0 := by
  obtain ⟨selection, valid, _, _, _⟩ := lift_enabled rfl IndexedOccurrences.supply
    callerSource callerPlan twoBefore (A.models_nil zero) caller_enabled
  have noTakes : selection.taken = [] := by
    apply List.length_eq_zero_iff.mp
    simpa only [callerSource, callerRule, List.length_nil] using valid.take_length.symm
  refine ⟨selection, valid, ?_, valid.output_distinct, valid.occurrences.fresh, ?_, ?_⟩
  · have lengths := congrArg List.length valid.outputs
    simpa only [List.length_map, callerSource, callerRule, List.length_cons, List.length_nil] using lengths
  · apply mem_fire.mpr
    left
    exact ⟨by simp [twoBefore, twoWorld], by simp [Selection.commit, noTakes]⟩
  · intro final modeled
    have told := (Selection.models_problem A valid modeled).2.2.2
      (Term.var (σ := signature) 0, .const 0) (List.mem_singleton_self _)
    exact told

def repeatedEntry : (resources A zero indexedLabel).Entry := ⟨⟨readSource⟩, ⟨repeatPlan⟩⟩

theorem repeated_enabled_with_two_rows :
    (resources A zero indexedLabel).Enables (labels (realized A zero indexedLabel) twoWorld) repeatedEntry.2 := by
  simpa [Mettapedia.GSLT.Causality.ResourceInteraction.System.Enables, resources,
    repeatedEntry, readSource, readTwice, readFootprint, ReadPlan.selection, repeatPlan] using
    (labels_mono (label := realized A zero indexedLabel)
      (show ({first} : Finset Id) ⊆ twoWorld from by simp [twoWorld]))

theorem repeated_fire_same (bag : Multiset (Term signature)) :
    (resources A zero indexedLabel).fire bag repeatedEntry.2 = bag := by
  change bag - 0 + 0 = bag
  simp

/-- The lift retains the whole two-row bag after the complete two-entry
resource run, and the same model solves the full final constraint store. -/
theorem finite_run_lifts_with_complete_residual_bag :
    ∃ schedule : List (ConditionalSchedule.Firing (Term signature) Id),
      ConditionalSchedule.Executable A indexedLabel twoBefore schedule ∧
      A.Models zero (ConditionalSchedule.follow indexedLabel twoBefore schedule).equations ∧
      schedule.length = 2 ∧
      labels (realized A zero indexedLabel) (ConditionalSchedule.follow indexedLabel twoBefore schedule).present =
        labels (realized A zero indexedLabel) twoWorld := by
  have fired : (resources A zero indexedLabel).Fires [repeatedEntry, repeatedEntry]
      (labels (realized A zero indexedLabel) twoWorld) (labels (realized A zero indexedLabel) twoWorld) := by
    refine ⟨repeated_enabled_with_two_rows, ?_⟩
    rw [repeated_fire_same]
    refine ⟨repeated_enabled_with_two_rows, ?_⟩
    exact (repeated_fire_same _).symm
  obtain ⟨schedule, executable, solved, matching, finalBag⟩ := lift_fires rfl IndexedOccurrences.supply
    [repeatedEntry, repeatedEntry] twoBefore (labels (realized A zero indexedLabel) twoWorld)
    (A.models_nil zero) fired
  exact ⟨schedule, executable, solved, matching.length_eq.symm, finalBag⟩

end
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourceControls
