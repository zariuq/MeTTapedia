import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyNeutralControls

/-!
# A spine of a local of dependent type on a concrete store

Over `A X : U0`, with a local `g : (Y : U0) → (Y → Y) → U0` bound by the abstraction,
`λ g. g X (λ y. y) ≐ λ g. g A (λ y. y)` is in the dynamic pattern fragment and is solved by `X := A`.
The head's type is dependent, so the non-dependent reading refuses it, and the second argument equation
is heterogeneous: `λ y. y : X → X` against `λ y. y : A → A`.

The ranked abstraction solver decomposes it along the head's type into `λ g. X ≐ λ g. A` and the
heterogeneous `λ g y. y` pair, solves the first by the pattern rule, and discharges the second by
conversion once its annotations agree, with a principal answer. The full occurs and ranked occurs
solvers leave it suspended.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSpinesMany.DependentControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentOccursFull.UnderControls ContextualDependentSpinesMany.Controls

/-- `(Y : U0) → (Y → Y) → U0`, as a code under one binder of `A X`. -/
abbrev headCode : Tower.Tm 2 :=
  .pi (.head (.sort Tower.zero)) (.pi (.pi (.var 0) (.var 1)) (.head (.sort Tower.zero)))

theorem dependentAt_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi headCode (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `((Y : U0) → (Y → Y) → U0) → U0` over `A X : U0`. -/
def dependentAt : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.pi headCode (.head (.sort Tower.zero)))).get
      dependentAt_formed).val

/-- A function over `A X` at `((Y : U0) → (Y → Y) → U0) → U0`, checked by the executable checker. -/
def checkedDependent (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 twoTypes.raw code dependentAt.code).isSome = true) :
    Term twoTypes dependentAt :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 twoTypes.raw code dependentAt.code).get accepted).down twoTypes.formed dependentAt.isType⟩

theorem flexDependent_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw
    (.lam (.app (.app (.var 0) (.var 1)) (.lam (.var 0)))) dependentAt.code).isSome = true := by
  decide +kernel

theorem rigidDependent_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw
    (.lam (.app (.app (.var 0) (.var 2)) (.lam (.var 0)))) dependentAt.code).isSome = true := by
  decide +kernel

/-- `λ g. g X (λ y. y) ≐ λ g. g A (λ y. y)`. -/
def dependentStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨dependentAt, checkedDependent _ flexDependent_checked⟩, ⟨dependentAt, checkedDependent _ rigidDependent_checked⟩)]

theorem dependentStore_length : dependentStore.length = 1 := rfl

def dependentEquation : Equation (TotalTerm twoTypes) :=
  dependentStore.head (List.ne_nil_of_length_pos (by rw [dependentStore_length]; decide))

theorem dependentStore_eq : dependentStore = [dependentEquation] := rfl

/-- **`λ g. g X (λ y. y) ≐ λ g. g A (λ y. y)` is in the dynamic pattern fragment.** -/
theorem dependent_in_fragment : InFragmentStore dependentStore := by
  rw [dependentStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl dependentEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The non-dependent reading refuses it**: the head's type is dependent. -/
theorem dependent_not_telescope :
    (spineUnder [] dependentEquation.1.1.code dependentEquation.1.2.code dependentEquation.2.2.code).isNone = true := by
  decide +kernel

/-- **The dependent reading takes it**, into two pieces. -/
theorem dependent_read :
    ((dependentUnder [] dependentEquation.1.1.code dependentEquation.1.2.code dependentEquation.2.2.code).map
      List.length) = some 2 := by
  decide +kernel

/-- **The ranked occurs solver leaves it suspended.** -/
theorem dependent_rankedOccurs_suspended : (run rankedOccursOnly dependentStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked abstraction solver commits on it.** -/
theorem dependent_solved : (run anyOnly dependentStore 5).readout = .commit := by decide +kernel

/-- **With a principal answer.** -/
theorem dependent_principal :
    ∃ state finished, run anyOnly dependentStore 5 = .solved state finished ∧
      (frames setting.levels).Principal dependentStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit dependent_solved
  exact ⟨state, finished, solved, drive_solved_principal anyOnly solved⟩

/-- **So this fragment store is decided, with a principal answer.** -/
theorem dependent_in_fragment_principal :
    InFragmentStore dependentStore ∧ ∃ state finished, run anyOnly dependentStore 5 = .solved state finished ∧
      (frames setting.levels).Principal dependentStore state.answer :=
  ⟨dependent_in_fragment, dependent_principal⟩

end ContextualDependentSpinesMany.DependentControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
