import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableConversion

/-!
# The dynamic pattern fragment on concrete stores

* **Inside, with pruning.** Over `T : U0, F G : (a b : T) → U0`, the store
  `λ x y z. G y z ≐ λ x y z. F x y` has three metavariables; solving it needs pruning (`G` loses
  its second argument, `F` its first). It is proved to belong to the dynamic pattern fragment, from
  its normal forms read by the actual normalizer. The rigid solver and the normalizing solver both
  commit on it with a principal answer.
* **Outside.** The non-pattern `λ x y. F x x ≐ λ x y. Id T y x` repeats a local; it is proved to lie
  outside the fragment. The full solver and the normalizing solver leave it suspended: neither
  refutes it.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDynamicFragment.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentExecutableJoin
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentRigidDecomposition.Controls
open ContextualDependentNormalizing.Controls

/-- A side is in the fragment when the actual normalizer reaches a normal form that is. -/
theorem side_by_normalizer {n count : Nat} {context : Tower.Ctx n} {x : Tower.Tm (n + count)} (fuel : Nat)
    (finished : (ContextualDependentExecutableConversion.red (L := Nat) fuel x).isSome = true)
    (normal : ExecutableReduction.step Tower.rules (fun _ => none)
      ((ContextualDependentExecutableConversion.red (L := Nat) fuel x).get finished).val = none)
    (inside : InFragmentCode context count ((ContextualDependentExecutableConversion.red (L := Nat) fuel x).get finished).val) :
    ∀ code, Star (R := Tower.rules) x code → Normal Tower.rules code → InFragmentCode context count code :=
  side_of_normal_form rfl
    (ContextualDependentExecutableConversion.normalize_star fuel (Option.some_get finished).symm)
    ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr normal) inside

/-- A side is outside the fragment when the actual normalizer reaches a normal form that is. -/
theorem side_not_by_normalizer {n count : Nat} {context : Tower.Ctx n} {x : Tower.Tm (n + count)} (fuel : Nat)
    (finished : (ContextualDependentExecutableConversion.red (L := Nat) fuel x).isSome = true)
    (normal : ExecutableReduction.step Tower.rules (fun _ => none)
      ((ContextualDependentExecutableConversion.red (L := Nat) fuel x).get finished).val = none)
    (outside : ¬ InFragmentCode context count
      ((ContextualDependentExecutableConversion.red (L := Nat) fuel x).get finished).val) :
    ¬ ∀ code, Star (R := Tower.rules) x code → Normal Tower.rules code → InFragmentCode context count code :=
  side_not_of_normal_form
    (ContextualDependentExecutableConversion.normalize_star fuel (Option.some_get finished).symm)
    ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr normal) outside

/-! ## Inside: `G y z ≐ F x y` -/

theorem flexFlex_store_length : flexFlexStore.length = 1 := by decide +kernel

/-- `λ x y z. G y z ≐ λ x y z. F x y`. -/
def flexEquation : Equation (TotalTerm ContextualDependentPrune.Controls.metas) :=
  flexFlexStore.head (List.ne_nil_of_length_pos (by rw [flexFlex_store_length]; decide))

theorem singleton_of_length {α : Type} : ∀ (l : List α) (h : l.length = 1),
    l = [l.head (List.ne_nil_of_length_pos (by omega))]
  | [], h => absurd h (by simp)
  | [_], _ => rfl
  | _ :: _ :: _, h => absurd h (by simp)

theorem flexFlex_store_eq : flexFlexStore = [flexEquation] :=
  singleton_of_length flexFlexStore flexFlex_store_length

/-- The opened sides are `G y z` and `F x y`, with `T, F, G` flexible and `x, y, z` rigid. -/
theorem flex_opened :
    ContextualDependentPatternSolver.lamDepth flexEquation.1.2.code = 3 := by decide +kernel

/-- **`G y z ≐ F x y` is in the dynamic pattern fragment.** -/
theorem flex_in_fragment : InFragment flexEquation := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have same : flexEquation.2.1.code = flexEquation.1.1.code := by decide +kernel
    rw [same]
    exact IsType.refl flexEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact side_by_normalizer 64 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact side_by_normalizer 64 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem flexFlex_in_fragment : InFragmentStore flexFlexStore := by
  rw [flexFlex_store_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  exact flex_in_fragment

/-- The normalizing solver commits on it, with a principal answer. -/
theorem flexFlex_normalizing_solved : (run normalizingOnly flexFlexStore 2).readout = .commit := by decide +kernel

theorem flexFlex_normalizing_principal :
    ∃ state finished, run normalizingOnly flexFlexStore 2 = .solved state finished ∧
      (frames setting.levels).Principal flexFlexStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit flexFlex_normalizing_solved
  exact ⟨state, finished, solved, drive_solved_principal normalizingOnly solved⟩

/-- The rigid solver commits on it too. -/
theorem flexFlex_rigid_solved : (run rigidOnly flexFlexStore 2).readout = .commit := by decide +kernel

/-! ## Outside: `F x x ≐ Id T y x` -/

theorem repeated_store_length : repeatedStore.length = 1 := by decide +kernel

/-- `λ x y. F x x ≐ λ x y. Id T y x`. -/
def repeatedEquation : Equation (TotalTerm (extend types ContextualDependentGeneralPattern.Controls.outerWhole)) :=
  repeatedStore.head (List.ne_nil_of_length_pos (by rw [repeated_store_length]; decide))

/-- **`F x x ≐ Id T y x` is outside the dynamic pattern fragment**: its opened left side repeats
the local `x`. -/
theorem repeated_not_in_fragment : ¬ InFragment repeatedEquation := by
  intro inside
  exact side_not_by_normalizer 64 (by decide +kernel) (by decide +kernel) (by decide +kernel) inside.2.2.2.1

theorem repeated_store_not_in_fragment : ¬ InFragmentStore repeatedStore := by
  intro inside
  exact repeated_not_in_fragment (inside _ (List.head_mem _))

/-- **The normalizing solver leaves it suspended**, never refuted, as the full solver does
(`repeated_suspended`). -/
theorem repeated_normalizing_suspended : (run normalizingOnly repeatedStore 4).readout = .suspended := by
  decide +kernel

end ContextualDependentDynamicFragment.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
