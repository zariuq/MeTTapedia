import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTwinsUnder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentDecisiveClashControls

/-!
# Twins with convertible annotations on concrete stores

Over `A X : U0`, at `(A → A) → U0`:

* **`λ g. Π (Id (A → A) (λ x. g x) g) (Π X A) ≐ λ g. Π (Id (A → A) g g) (Π A A)`** is in the dynamic
  pattern fragment and is solved by `X := A`. Decomposing it under its abstraction gives the domain
  equation, removed by conversion (η), and the codomain twin `λ g d. Π X A ≐ λ g d. Π A A`, whose two
  annotations mention `λ x. g x` and `g`: equal types, different codes, at every instantiation. The
  ranked abstraction solver leaves the twin suspended; the twin solver makes it homogeneous, decomposes
  it and solves `X := A`, with a principal answer.
* **The same with `Σ A A` in the right codomain** is in the fragment and has no solution. The twin solver
  makes the twin homogeneous and refutes the clash `Π X A ≐ Σ A A` under the abstractions; the ranked
  abstraction solver leaves it suspended.
* **With the same domain on both sides** the twin is homogeneous from the start, and both solvers commit.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentTwinsUnder.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentSpinesMany.Controls ContextualDependentFragmentDecisive.ClashControls

/-- The twin solver of the tower controls, as a fuel-indexed family. -/
noncomputable def twinTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  twinFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The twin solver at budget 16. -/
noncomputable def twinOnly : Solver setting.levels := twinTower.solver 16

/-! ## The stores -/

theorem endoFamily_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.pi (.var 1) (.var 2)) (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `(A → A) → U0`. -/
def endoFamily : TypeOver twoTypes := formedAt _ endoFamily_formed

theorem expanded_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw
    (.lam (.pi (.id (.pi (.var 2) (.var 3)) (.lam (.app (.var 1) (.var 0))) (.var 0)) (.pi (.var 2) (.var 4))))
    endoFamily.code).isSome = true := by
  decide +kernel

theorem plain_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw
    (.lam (.pi (.id (.pi (.var 2) (.var 3)) (.var 0) (.var 0)) (.pi (.var 3) (.var 4))))
    endoFamily.code).isSome = true := by
  decide +kernel

theorem plainMeta_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw
    (.lam (.pi (.id (.pi (.var 2) (.var 3)) (.var 0) (.var 0)) (.pi (.var 2) (.var 4))))
    endoFamily.code).isSome = true := by
  decide +kernel

theorem plainSigma_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw
    (.lam (.pi (.id (.pi (.var 2) (.var 3)) (.var 0) (.var 0)) (.sigma (.var 3) (.var 4))))
    endoFamily.code).isSome = true := by
  decide +kernel

/-- `λ g. Π (Id (A → A) (λ x. g x) g) (Π X A) ≐ λ g. Π (Id (A → A) g g) (Π A A)`. -/
def twinStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨endoFamily, checkedAt endoFamily _ expanded_checked⟩, ⟨endoFamily, checkedAt endoFamily _ plain_checked⟩)]

/-- `λ g. Π (Id (A → A) (λ x. g x) g) (Π X A) ≐ λ g. Π (Id (A → A) g g) (Σ A A)`. -/
def clashTwinStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨endoFamily, checkedAt endoFamily _ expanded_checked⟩, ⟨endoFamily, checkedAt endoFamily _ plainSigma_checked⟩)]

/-- `λ g. Π (Id (A → A) g g) (Π X A) ≐ λ g. Π (Id (A → A) g g) (Π A A)`. -/
def homogeneousStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨endoFamily, checkedAt endoFamily _ plainMeta_checked⟩, ⟨endoFamily, checkedAt endoFamily _ plain_checked⟩)]

theorem twinStore_length : twinStore.length = 1 := rfl

def twinEquation : Equation (TotalTerm twoTypes) :=
  twinStore.head (List.ne_nil_of_length_pos (by rw [twinStore_length]; decide))

theorem twinStore_eq : twinStore = [twinEquation] := rfl

theorem clashTwinStore_length : clashTwinStore.length = 1 := rfl

def clashTwinEquation : Equation (TotalTerm twoTypes) :=
  clashTwinStore.head (List.ne_nil_of_length_pos (by rw [clashTwinStore_length]; decide))

theorem clashTwinStore_eq : clashTwinStore = [clashTwinEquation] := rfl

/-! ## Membership in the fragment -/

/-- **The twin store is in the dynamic pattern fragment.** -/
theorem twin_in_fragment : InFragmentStore twinStore := by
  rw [twinStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl twinEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The clashing twin store is in the dynamic pattern fragment.** -/
theorem clashTwin_in_fragment : InFragmentStore clashTwinStore := by
  rw [clashTwinStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl clashTwinEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-! ## Runs -/

/-- **The ranked abstraction solver leaves the twin suspended.** -/
theorem twin_any_suspended : (run anyOnly twinStore 8).readout = .suspended := by decide +kernel

/-- **The twin solver commits**, with the answer `X := A`. -/
theorem twin_committed : (run twinOnly twinStore 8).readout = .commit := by decide +kernel

/-- **The ranked abstraction solver leaves the clashing twin suspended.** -/
theorem clashTwin_any_suspended : (run anyOnly clashTwinStore 8).readout = .suspended := by decide +kernel

/-- **The twin solver refutes the clashing twin.** -/
theorem clashTwin_refuted : (run twinOnly clashTwinStore 8).readout = .refuted := by decide +kernel

theorem clashTwin_unsolvable : ¬ (frames setting.levels).Solvable clashTwinStore :=
  drive_refuted twinOnly 8 _ clashTwin_refuted

/-- **Without the η-difference both solvers commit.** -/
theorem homogeneous_any_committed : (run anyOnly homogeneousStore 8).readout = .commit := by decide +kernel

theorem homogeneous_twin_committed : (run twinOnly homogeneousStore 8).readout = .commit := by decide +kernel

/-- **The twin store is decided with a principal answer**: in the fragment, and the run at budget 16 with
eight rounds ends in a solved state whose answer is principal. -/
theorem twin_in_fragment_principal : InFragmentStore twinStore ∧
    ∃ state finished, run twinOnly twinStore 8 = .solved state finished ∧
      (frames setting.levels).Principal twinStore state.answer := by
  refine ⟨twin_in_fragment, ?_⟩
  have committed := twin_committed
  cases outcome : run twinOnly twinStore 8 with
  | solved state finished => exact ⟨state, finished, rfl, state.completed finished⟩
  | refuted _ => rw [outcome] at committed; cases committed
  | stuck _ => rw [outcome] at committed; cases committed
  | cutoff _ => rw [outcome] at committed; cases committed

end ContextualDependentTwinsUnder.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
