import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyDependentControls

/-!
# Rigid clashes under abstractions on concrete stores

Over `A X : U0`:

* **`λ x. Π x x ≐ λ x. Σ x x`** at `U0 → U0` is in the dynamic pattern fragment and has no solution: a Π
  type is never a Σ type. R75's clash test reads outermost codes only, so the ranked occurs solver
  leaves it suspended; the ranked abstraction solver refutes it with a certificate.
* **`λ f g. f A ≐ λ f g. g A`** at `(U0 → U0) → (U0 → U0) → U0` is in the fragment and has no solution:
  two spines of distinct locals. It is refuted in the same way.
* **`λ Y p. p ≐ λ Y p. refl Y`** at `(Y : U0) → Id U0 Y Y → Id U0 Y Y` is in the fragment and has no
  solution: a variable of an identity type is never reflexivity. It is refuted in the same way.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragmentDecisive.ClashControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentOccursFull.UnderControls ContextualDependentSpinesMany.Controls

/-- A type over `A X : U0`, formed by the budgeted formation of types. -/
def formedAt (code : Tower.Tm 2)
    (accepted : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes code).isSome) :
    TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes code).get accepted).val

/-- A term over `A X` at a formed type, checked by the executable checker. -/
def checkedAt (type : TypeOver twoTypes) (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 twoTypes.raw code type.code).isSome = true) :
    Term twoTypes type :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 twoTypes.raw code type.code).get accepted).down twoTypes.formed type.isType⟩

/-! ## Two formers under an abstraction -/

theorem endo_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))).isSome := by decide +kernel

/-- `U0 → U0`. -/
def endo : TypeOver twoTypes := formedAt _ endo_formed

theorem piFamily_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.lam (.pi (.var 0) (.var 1))) endo.code).isSome =
    true := by decide +kernel

theorem sigmaFamily_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.lam (.sigma (.var 0) (.var 1))) endo.code).isSome =
    true := by decide +kernel

/-- `λ x. Π x x ≐ λ x. Σ x x`. -/
def formersStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨endo, checkedAt endo _ piFamily_checked⟩, ⟨endo, checkedAt endo _ sigmaFamily_checked⟩)]

theorem formersStore_length : formersStore.length = 1 := rfl

def formersEquation : Equation (TotalTerm twoTypes) :=
  formersStore.head (List.ne_nil_of_length_pos (by rw [formersStore_length]; decide))

theorem formersStore_eq : formersStore = [formersEquation] := rfl

theorem formers_in_fragment : InFragmentStore formersStore := by
  rw [formersStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl formersEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The ranked occurs solver leaves it suspended.** -/
theorem formers_rankedOccurs_suspended : (run rankedOccursOnly formersStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked abstraction solver refutes it.** -/
theorem formers_refuted : (run anyOnly formersStore 2).readout = .refuted := by decide +kernel

theorem formers_unsolvable : ¬ (frames setting.levels).Solvable formersStore :=
  drive_refuted anyOnly 2 _ formers_refuted

/-! ## Two distinct locals under abstractions -/

theorem binary_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))
      (.pi (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (.head (.sort Tower.zero))))).isSome := by
  decide +kernel

/-- `(U0 → U0) → (U0 → U0) → U0`. -/
def binary : TypeOver twoTypes := formedAt _ binary_formed

theorem first_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.lam (.lam (.app (.var 1) (.var 3))))
    binary.code).isSome = true := by decide +kernel

theorem second_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.lam (.lam (.app (.var 0) (.var 3))))
    binary.code).isSome = true := by decide +kernel

/-- `λ f g. f A ≐ λ f g. g A`. -/
def localsStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨binary, checkedAt binary _ first_checked⟩, ⟨binary, checkedAt binary _ second_checked⟩)]

theorem localsStore_length : localsStore.length = 1 := rfl

def localsEquation : Equation (TotalTerm twoTypes) :=
  localsStore.head (List.ne_nil_of_length_pos (by rw [localsStore_length]; decide))

theorem localsStore_eq : localsStore = [localsEquation] := rfl

theorem locals_in_fragment : InFragmentStore localsStore := by
  rw [localsStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl localsEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The ranked occurs solver leaves it suspended.** -/
theorem locals_rankedOccurs_suspended : (run rankedOccursOnly localsStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked abstraction solver refutes it.** -/
theorem locals_refuted : (run anyOnly localsStore 2).readout = .refuted := by decide +kernel

theorem locals_unsolvable : ¬ (frames setting.levels).Solvable localsStore :=
  drive_refuted anyOnly 2 _ locals_refuted

/-! ## Reflexivity against a local -/

theorem paths_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.head (.sort Tower.zero)) (.pi (.id (.head (.sort Tower.zero)) (.var 0) (.var 0))
      (.id (.head (.sort Tower.zero)) (.var 1) (.var 1))))).isSome := by
  decide +kernel

/-- `(Y : U0) → Id U0 Y Y → Id U0 Y Y`. -/
def paths : TypeOver twoTypes := formedAt _ paths_formed

theorem identity_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.lam (.lam (.var 0))) paths.code).isSome = true := by
  decide +kernel

theorem reflexivity_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.lam (.lam (.refl (.var 1)))) paths.code).isSome =
    true := by
  decide +kernel

/-- `λ Y p. p ≐ λ Y p. refl Y`. -/
def reflStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨paths, checkedAt paths _ identity_checked⟩, ⟨paths, checkedAt paths _ reflexivity_checked⟩)]

theorem reflStore_length : reflStore.length = 1 := rfl

def reflEquation : Equation (TotalTerm twoTypes) :=
  reflStore.head (List.ne_nil_of_length_pos (by rw [reflStore_length]; decide))

theorem reflStore_eq : reflStore = [reflEquation] := rfl

theorem refl_in_fragment : InFragmentStore reflStore := by
  rw [reflStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl reflEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The ranked occurs solver leaves it suspended.** -/
theorem refl_rankedOccurs_suspended : (run rankedOccursOnly reflStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked abstraction solver refutes it**: reflexivity is never a variable of an identity type. -/
theorem refl_refuted : (run anyOnly reflStore 2).readout = .refuted := by decide +kernel

theorem refl_unsolvable : ¬ (frames setting.levels).Solvable reflStore :=
  drive_refuted anyOnly 2 _ refl_refuted

/-- **So the three fragment stores are decided, by certified refutations.** -/
theorem clashes_decided :
    (InFragmentStore formersStore ∧ ¬ (frames setting.levels).Solvable formersStore) ∧
      (InFragmentStore localsStore ∧ ¬ (frames setting.levels).Solvable localsStore) ∧
      (InFragmentStore reflStore ∧ ¬ (frames setting.levels).Solvable reflStore) :=
  ⟨⟨formers_in_fragment, formers_unsolvable⟩, ⟨locals_in_fragment, locals_unsolvable⟩,
    ⟨refl_in_fragment, refl_unsolvable⟩⟩

end ContextualDependentFragmentDecisive.ClashControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
