import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyFormersControls

/-!
# Spines with three arguments on concrete stores

Over `A X : U0`, with a local `g : U0 → U0 → U0 → U0` bound by the abstraction:

* **`λ g. g X A A ≐ λ g. g A A A`** is in the dynamic pattern fragment and is solved by `X := A`. R94's
  spine rule reads two arguments only, so the full occurs and ranked occurs solvers leave it suspended.
  The ranked abstraction solver decomposes it into the three argument equations under the abstraction,
  discharges the two trivial ones by conversion and solves the first by the pattern rule, with a
  principal answer.
* **`λ g. g X A A ≐ λ g. g A A (Π A A)`** has no solution: its third argument equation is `A ≐ Π A A`.
  The ranked abstraction solver decomposes it and refutes it by the occurs check under the abstraction.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSpinesMany.NeutralControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentOccursFull.UnderControls ContextualDependentSpinesMany.Controls

/-- `U0`. -/
abbrev small : Tower.Tm 2 := .head (.sort Tower.zero)

theorem ternaryAt_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero))
      (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))) (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `(U0 → U0 → U0 → U0) → U0` over `A X : U0`. -/
def ternaryAt : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero))
      (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))) (.head (.sort Tower.zero)))).get
      ternaryAt_formed).val

/-- A function over `A X` at `(U0 → U0 → U0 → U0) → U0`, checked by the executable checker. -/
def checkedTernary (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 twoTypes.raw code ternaryAt.code).isSome = true) :
    Term twoTypes ternaryAt :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 twoTypes.raw code ternaryAt.code).get accepted).down twoTypes.formed ternaryAt.isType⟩

theorem flexTernary_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw
    (.lam (.app (.app (.app (.var 0) (.var 1)) (.var 2)) (.var 2))) ternaryAt.code).isSome = true := by
  decide +kernel

theorem rigidTernary_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw
    (.lam (.app (.app (.app (.var 0) (.var 2)) (.var 2)) (.var 2))) ternaryAt.code).isSome = true := by
  decide +kernel

theorem loopTernary_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw
    (.lam (.app (.app (.app (.var 0) (.var 2)) (.var 2)) (.pi (.var 2) (.var 3)))) ternaryAt.code).isSome = true := by
  decide +kernel

/-! ## A solvable store -/

/-- `λ g. g X A A ≐ λ g. g A A A`. -/
def ternaryStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨ternaryAt, checkedTernary _ flexTernary_checked⟩, ⟨ternaryAt, checkedTernary _ rigidTernary_checked⟩)]

theorem ternaryStore_length : ternaryStore.length = 1 := rfl

def ternaryEquation : Equation (TotalTerm twoTypes) :=
  ternaryStore.head (List.ne_nil_of_length_pos (by rw [ternaryStore_length]; decide))

theorem ternaryStore_eq : ternaryStore = [ternaryEquation] := rfl

/-- **`λ g. g X A A ≐ λ g. g A A A` is in the dynamic pattern fragment.** -/
theorem ternary_in_fragment : InFragmentStore ternaryStore := by
  rw [ternaryStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl ternaryEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The full occurs solver leaves it suspended**: R94's spine rule reads two arguments only. -/
theorem ternary_occursFull_suspended :
    (run ContextualDependentOccursFull.Controls.occursFullOnly ternaryStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked occurs solver leaves it suspended.** -/
theorem ternary_rankedOccurs_suspended : (run rankedOccursOnly ternaryStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked abstraction solver commits on it.** -/
theorem ternary_solved : (run anyOnly ternaryStore 5).readout = .commit := by decide +kernel

/-- **With a principal answer.** -/
theorem ternary_principal :
    ∃ state finished, run anyOnly ternaryStore 5 = .solved state finished ∧
      (frames setting.levels).Principal ternaryStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit ternary_solved
  exact ⟨state, finished, solved, drive_solved_principal anyOnly solved⟩

/-! ## An unsolvable store -/

/-- `λ g. g X A A ≐ λ g. g A A (Π A A)`. -/
def ternaryLoopStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨ternaryAt, checkedTernary _ flexTernary_checked⟩, ⟨ternaryAt, checkedTernary _ loopTernary_checked⟩)]

/-- **The ranked abstraction solver refutes it.** -/
theorem ternaryLoop_refuted : (run anyOnly ternaryLoopStore 3).readout = .refuted := by decide +kernel

theorem ternaryLoop_unsolvable : ¬ (frames setting.levels).Solvable ternaryLoopStore :=
  drive_refuted anyOnly 3 _ ternaryLoop_refuted

/-- **The ranked occurs solver leaves it suspended.** -/
theorem ternaryLoop_rankedOccurs_suspended : (run rankedOccursOnly ternaryLoopStore 4).readout = .suspended := by
  decide +kernel

end ContextualDependentSpinesMany.NeutralControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
