import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringEventual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringControls

/-!
# The flexible rows on concrete stores

* **The rigid out-of-scope row.** `λ x y. F x ≐ λ x y. Π y (G x)` is in the row (`rigid_row`), so the firing
  theorem applies to it (`rigid_fires`). `λ x y. F x ≐ λ x y. G y` and `λ x y. F x ≐ λ x y. Π A (G x y)` are not:
  their out-of-scope local `y` occurs only under `G` (`flexible_not_row`, `prunable_not_row`).
* **Cumulativity at a pattern argument.** Over `A : U0, F : U1 → U1`, at `U0 → U1`, `λ x. F x ≐ λ x. x` is in the
  fragment and solvable by `F := λ y. y`; the firing solver is stuck on it at budget 16 (`cumulative_unread`).
  Recognition of a pattern asks the locals' declared types to be the metavariable's binder types: here `x : U0`
  is passed where `U1` is declared. At the matching annotation `U1 → U1` the same equation commits.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentDynamicFragment ContextualDependentExecutableJoin

/-! ## The rigid out-of-scope row -/

theorem rigid_row : RigidOutside rigidEquation :=
  rigidOutside_of_normal (head := ⟨2, by decide +kernel⟩) (arguments := [⟨1, by decide +kernel⟩])
    (outside := ⟨0, by decide +kernel⟩) rfl
    ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel))
    ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The tower's normality certificate accepts every normal term. -/
theorem certifies {n : Nat} (term : Tower.Tm n) (normal : Normal Tower.rules term) :
    (ContextualDependentGeneralPattern.DispatchControls.certifyNormal term).isSome := by
  have quiet := (ContextualDependentNormalizing.normal_iff_step_none rfl term).mp normal
  unfold ContextualDependentGeneralPattern.DispatchControls.certifyNormal
  rw [dif_pos quiet]
  rfl

/-- **The firing theorem applies**: on `λ x y. F x ≐ λ x y. Π y (G x)` the firing round of the tower is not stuck
from some budget on. -/
theorem rigid_fires : ∃ bound, ∀ larger, bound ≤ larger →
    firingRound TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentExecutableChecking.declared ContextualDependentExecutableChecking.tc
      ContextualDependentExecutableConversion.red (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) larger rigidStore ≠ .stuck :=
  firingRound_fires (fun _ => (0 : Nat)) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique rigidStore (by rw [rigidStore_eq]; exact List.mem_cons_self)
    (rigid_in_fragment _ (by rw [rigidStore_eq]; exact List.mem_cons_self)) (.inl rigid_row) certifies

/-! ## The row with the metavariable on the right -/

/-- `λ x y. Π y (G x) ≐ λ x y. F x`. -/
def swappedStore : EquationStore (TotalTerm withMetas) :=
  [(termIn withMetas twoLocals (.lam (.lam (.pi (.var 0) (.app (.var 4) (.var 2))))) (by decide +kernel),
    termIn withMetas twoLocals (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel))]

theorem swappedStore_length : swappedStore.length = 1 := rfl

def swappedEquation : Equation (TotalTerm withMetas) :=
  swappedStore.head (List.ne_nil_of_length_pos (by rw [swappedStore_length]; decide))

theorem swappedStore_eq : swappedStore = [swappedEquation] := rfl

theorem swapped_in_fragment : InFragmentStore swappedStore := by
  rw [swappedStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl swappedEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem swapped_row : RigidOutsideRight swappedEquation := by
  intro left right toLeft normalLeft toRight normalRight
  rw [normal_reduct_unique rfl (ContextualDependentCensus.openCode_star _ _)
    (ContextualDependentCensus.openNormal_normal rfl
      ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)) _) toLeft normalLeft]
  rw [normal_reduct_unique rfl (ContextualDependentCensus.openCode_star _ _)
    (ContextualDependentCensus.openNormal_normal rfl
      ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)) _) toRight normalRight]
  exact ⟨⟨2, by decide +kernel⟩, [⟨1, by decide +kernel⟩], ⟨0, by decide +kernel⟩, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem swapped_arguments_stuck :
    isStuck (run ContextualDependentIdEndpointsArguments.Controls.argumentsOnly swappedStore 8) = true := by
  decide +kernel

/-- **The firing solver refutes the swapped store.** -/
theorem swapped_firing_refuted : (run firingOnly swappedStore 8).readout = .refuted := by decide +kernel

/-- **The firing theorem applies in the other orientation.** -/
theorem swapped_fires : ∃ bound, ∀ larger, bound ≤ larger →
    firingRound TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentExecutableChecking.declared ContextualDependentExecutableChecking.tc
      ContextualDependentExecutableConversion.red (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) larger swappedStore ≠ .stuck :=
  firingRound_fires (fun _ => (0 : Nat)) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique swappedStore
    (by rw [swappedStore_eq]; exact List.mem_cons_self)
    (swapped_in_fragment _ (by rw [swappedStore_eq]; exact List.mem_cons_self)) (.inr swapped_row) certifies

/-! ## Flexible occurrences are not in the row -/

theorem flexibleStore_length : flexibleStore.length = 1 := rfl

def flexibleEquation : Equation (TotalTerm withMetas) :=
  flexibleStore.head (List.ne_nil_of_length_pos (by rw [flexibleStore_length]; decide))

theorem flexible_not_row : ¬ RigidOutside flexibleEquation := by
  intro row
  obtain ⟨head, arguments, outside, read, _, _, occurs, rigidOutside, notArgument⟩ :=
    row _ _ (ContextualDependentCensus.openCode_star (R := setting.R) _ _)
      (ContextualDependentCensus.openNormal_normal rfl
        ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)) _)
      (ContextualDependentCensus.openCode_star (R := setting.R) _ _)
      (ContextualDependentCensus.openNormal_normal rfl
        ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)) _)
  have computed : readSpine (ContextualDependentCensus.openNormal
      (ContextualDependentPatternSolver.lamDepth flexibleEquation.1.2.code) flexibleEquation.1.2.code) =
      some (⟨2, by decide +kernel⟩, [⟨1, by decide +kernel⟩]) := by decide +kernel
  rw [computed] at read
  cases read
  revert occurs rigidOutside notArgument
  revert outside
  decide +kernel

theorem prunableStore_length : prunableStore.length = 1 := rfl

def prunableEquation : Equation (TotalTerm withPrunable) :=
  prunableStore.head (List.ne_nil_of_length_pos (by rw [prunableStore_length]; decide))

theorem prunable_not_row : ¬ RigidOutside prunableEquation := by
  intro row
  obtain ⟨head, arguments, outside, read, _, _, occurs, rigidOutside, notArgument⟩ :=
    row _ _ (ContextualDependentCensus.openCode_star (R := setting.R) _ _)
      (ContextualDependentCensus.openNormal_normal rfl
        ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)) _)
      (ContextualDependentCensus.openCode_star (R := setting.R) _ _)
      (ContextualDependentCensus.openNormal_normal rfl
        ((ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)) _)
  have computed : readSpine (ContextualDependentCensus.openNormal
      (ContextualDependentPatternSolver.lamDepth prunableEquation.1.2.code) prunableEquation.1.2.code) =
      some (⟨2, by decide +kernel⟩, [⟨1, by decide +kernel⟩]) := by decide +kernel
  rw [computed] at read
  cases read
  revert occurs rigidOutside notArgument
  revert outside
  decide +kernel

/-! ## Cumulativity at a pattern argument -/

/-- `U1 → U1`, over `A`. -/
def large : TypeOver typeContext :=
  formIn typeContext (.pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `A : U0, F : U1 → U1`. -/
abbrev withLarge := extend typeContext large

/-- `U0 → U1`, over `A, F`. -/
def raising : TypeOver withLarge :=
  formIn withLarge (.pi (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `U1 → U1`, over `A, F`. -/
def largeHere : TypeOver withLarge :=
  formIn withLarge (.pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `λ x. F x ≐ λ x. x` at `U0 → U1`. -/
def cumulativeStore : EquationStore (TotalTerm withLarge) :=
  [(termIn withLarge raising (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn withLarge raising (.lam (.var 0)) (by decide +kernel))]

theorem cumulativeStore_length : cumulativeStore.length = 1 := rfl

def cumulativeEquation : Equation (TotalTerm withLarge) :=
  cumulativeStore.head (List.ne_nil_of_length_pos (by rw [cumulativeStore_length]; decide))

theorem cumulativeStore_eq : cumulativeStore = [cumulativeEquation] := rfl

theorem cumulative_in_fragment : InFragmentStore cumulativeStore := by
  rw [cumulativeStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl cumulativeEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- `λ y. y : U1 → U1`, over `A`. -/
def identityValue : Term typeContext large :=
  (termIn typeContext large (.lam (.var 0)) (by decide +kernel)).2

/-- **The instantiation `F := λ y. y`.** -/
def identityAnswer : typeContext ⟶ withLarge := Elimination.instantiate typeContext identityValue

theorem cumulative_compared : (Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.reducer 16 (cumulativeEquation.1.reindex identityAnswer)
    (cumulativeEquation.2.reindex identityAnswer)).isSome := by
  decide +kernel

/-- **`λ x. F x ≐ λ x. x` is solvable**, by `F := λ y. y`. -/
theorem cumulative_solvable : (frames setting.levels).Solvable cumulativeStore := by
  refine ⟨_, identityAnswer, fun equation member => ?_⟩
  rw [cumulativeStore_eq] at member
  obtain rfl := List.mem_singleton.mp member
  exact ((Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer 16 _ _).get cumulative_compared).down

theorem cumulative_firing_stuck : isStuck (run firingOnly cumulativeStore 8) = true := by decide +kernel

/-- **A cumulative pattern argument is not read**: the store is in the fragment, solvable, and the firing solver
is stuck on it at budget 16. -/
theorem cumulative_unread : InFragmentStore cumulativeStore ∧ (frames setting.levels).Solvable cumulativeStore ∧
    isStuck (run firingOnly cumulativeStore 8) = true :=
  ⟨cumulative_in_fragment, cumulative_solvable, cumulative_firing_stuck⟩

/-- `λ x. F x ≐ λ x. x` at `U1 → U1`. -/
def matchingStore : EquationStore (TotalTerm withLarge) :=
  [(termIn withLarge largeHere (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn withLarge largeHere (.lam (.var 0)) (by decide +kernel))]

/-- **Control: at the matching annotation the pattern commits.** -/
theorem matching_firing_committed : (run firingOnly matchingStore 8).readout = .commit := by decide +kernel

end ContextualDependentPatternFiring.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
