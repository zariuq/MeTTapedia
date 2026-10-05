import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerOperations
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamiliesControls

/-!
# Infinite contextual controls for singleton and union

Singleton and union retain the different predicates associated with
parallel future histories. A stable outer predicate can admit no inner
predicate currently and still admit inner predicates at later targets;
its union therefore has nonempty full future truth and empty present truth.
These are actual operations on the infinite observed material input.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerOperationsControls

open _root_.CategoryTheory
open ContextualGeneratedUniverse
open FuturePowerFamilies
open FuturePowerOperations
open ContextualPowerFamilies
open ContextualPowerOperations
open ContextualPowerFamiliesControls
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths

def lateOuter : Predicate (family domain.family) initialPoint where
  holds future := 0 < future.1.1.1.unop.unop.length
  closed {first _second} move available := Nat.lt_of_lt_of_le available
    ((Nat.le_add_right first.1.1.1.unop.unop.length move.1.1.val.unop.unop.val.length).trans_eq
      move.1.1.val.unop.unop.property)

theorem lateOuter_has_no_current_inner (inner : Predicate domain.family initialPoint) :
    ¬ lateOuter.holds (current (family domain.family) initialPoint inner) := by
  change ¬ 0 < 0
  exact Nat.lt_irrefl 0

theorem lateOuter_union_future (label : Nat) :
    (flatten domain.family initialPoint lateOuter).holds (futureArgument label) := by
  refine ⟨singleton domain.family (nextPoint label) (futureArgument label).2,
    (show 0 < 1 from Nat.zero_lt_succ 0), ?_⟩
  exact (singleton_current domain.family (nextPoint label) (futureArgument label).2
    (futureArgument label).2).mpr rfl

theorem lateOuter_union_has_no_present_truth (argument : domain.family.obj initialPoint) :
    ¬ (flatten domain.family initialPoint lateOuter).holds (current domain.family initialPoint argument) := by
  rintro ⟨inner, admitted, _truth⟩
  exact lateOuter_has_no_current_inner inner admitted

def outerMember :
    {value : HSet // value ∈ ((power powers arrowCoding).model initialPoint).carrier} :=
  ((power powers arrowCoding).model initialPoint).decode.symm lateOuter

def unionMember : {value : HSet // value ∈ (powers.model initialPoint).carrier} :=
  flattenMember domain arrowCoding initialPoint outerMember

theorem unionMember_decode :
    (powers.model initialPoint).decode unionMember = flatten domain.family initialPoint lateOuter := by
  rw [unionMember, flattenMember_decode]
  exact congrArg (flatten domain.family initialPoint)
    (((power powers arrowCoding).model initialPoint).decode.apply_symm_apply lateOuter)

theorem unionMember_value : unionMember.val =
    (powers.model initialPoint).value (flatten domain.family initialPoint lateOuter) :=
  ((powers.model initialPoint).value_decode unionMember).symm.trans
    (congrArg (powers.model initialPoint).value unionMember_decode)

theorem union_material_future (label : Nat) :
    (domain.futureCoding arrowCoding initialPoint).reading (futureArgument label) ∈ unionMember.val := by
  rw [unionMember_value]
  exact (power_truth domain arrowCoding initialPoint _ (futureArgument label)).mpr
    (lateOuter_union_future label)

theorem union_material_nonempty : unionMember.val ≠ ∅ := by
  intro empty
  have available := union_material_future 0
  rw [empty] at available
  exact HSet.notMem_empty _ available

theorem union_present_part_empty :
    presentPart domain arrowCoding initialPoint (flatten domain.family initialPoint lateOuter) = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value available
  obtain ⟨argument, _, truth⟩ := (mem_presentPart domain arrowCoding initialPoint _ value).mp available
  exact lateOuter_union_has_no_present_truth argument truth

/-- Lack of a current admitted inner predicate does not imply lack of
future membership in the actual union. -/
theorem current_outer_empty_future_union_inhabited :
    (∀ inner, ¬ lateOuter.holds (current (family domain.family) initialPoint inner)) ∧
      unionMember.val ≠ ∅ ∧
      presentPart domain arrowCoding initialPoint (flatten domain.family initialPoint lateOuter) = ∅ :=
  ⟨lateOuter_has_no_current_inner, union_material_nonempty, union_present_part_empty⟩

def historyMember (label : Nat) : {value : HSet // value ∈ (powers.model initialPoint).carrier} :=
  (powers.model initialPoint).decode.symm (startsWith label)

theorem material_union_singleton_history (label : Nat) :
    flattenMember domain arrowCoding initialPoint
      (singletonMember powers arrowCoding initialPoint (historyMember label)) = historyMember label :=
  flatten_singletonMember domain arrowCoding initialPoint (historyMember label)

theorem infinite_histories_survive_union_singleton :
    Function.Injective (fun label =>
      (flattenMember domain arrowCoding initialPoint
        (singletonMember powers arrowCoding initialPoint (historyMember label))).val) := by
  intro first second same
  have recoveredFirst := congrArg Subtype.val (material_union_singleton_history first)
  have recoveredSecond := congrArg Subtype.val (material_union_singleton_history second)
  exact materialPredicate_injective (recoveredFirst.symm.trans (same.trans recoveredSecond))

theorem parallel_future_truth_survives_union_singleton :
    (flatten domain.family initialPoint (singleton (family domain.family) initialPoint (startsWith 0))).holds
        (futureArgument 0) ∧
      ¬ (flatten domain.family initialPoint (singleton (family domain.family) initialPoint (startsWith 0))).holds
        (futureArgument 1) := by
  rw [flatten_singleton]
  exact ⟨(startsWith_future_iff 0 0).mpr rfl,
    fun truth => Nat.zero_ne_one ((startsWith_future_iff 0 1).mp truth)⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerOperationsControls
