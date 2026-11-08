import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyFormersRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFullUnderControls

/-!
# Decomposition under abstractions on concrete stores

* **A fragment store decided only under its abstraction.** Over `A : U0, G : U0 → U0`, the equation
  `λ x. Π (G x) x ≐ λ x. Π x x` at `U0 → U0` is in the dynamic pattern fragment and is solved by
  `G := λ x. x`. Its formers sit under an abstraction, so R94's decomposition, which reads formers at a
  universe only, never sees them: the full occurs, ranked and ranked occurs solvers leave it suspended.
  The ranked abstraction solver decomposes it into `λ x. G x ≐ λ x. x` and the family twin, solves the
  first by the pattern rule, and discharges the twin by conversion, with a principal answer.
* **The earlier witnesses keep their readouts.**

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSpinesMany.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentOccursFull.UnderControls

/-- The ranked abstraction solver of the tower controls, as a fuel-indexed family. -/
noncomputable def anyTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  anyFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The ranked abstraction solver at budget 16. -/
noncomputable def anyOnly : Solver setting.levels := anyTower.solver 16

/-! ## Formers under an abstraction -/

theorem diagonal_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withFamily.raw (.lam (.pi (.var 0) (.var 1)))
    familyAt.code).isSome = true := by
  decide +kernel

/-- `λ x. Π (G x) x ≐ λ x. Π x x` at `U0 → U0`. -/
def underStore : EquationStore (TotalTerm withFamily) :=
  [(⟨familyAt, checkedFamily _ loopFamily_checked⟩, ⟨familyAt, checkedFamily _ diagonal_checked⟩)]

theorem underStore_length : underStore.length = 1 := rfl

def underEquation : Equation (TotalTerm withFamily) :=
  underStore.head (List.ne_nil_of_length_pos (by rw [underStore_length]; decide))

theorem underStore_eq : underStore = [underEquation] := rfl

/-- **`λ x. Π (G x) x ≐ λ x. Π x x` is in the dynamic pattern fragment.** -/
theorem under_in_fragment : InFragmentStore underStore := by
  rw [underStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl underEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The full occurs solver leaves it suspended.** -/
theorem under_occursFull_suspended :
    (run ContextualDependentOccursFull.Controls.occursFullOnly underStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked occurs solver leaves it suspended.** -/
theorem under_rankedOccurs_suspended : (run rankedOccursOnly underStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked abstraction solver commits on it.** -/
theorem under_solved : (run anyOnly underStore 5).readout = .commit := by decide +kernel

/-- **With a principal answer.** -/
theorem under_principal :
    ∃ state finished, run anyOnly underStore 5 = .solved state finished ∧
      (frames setting.levels).Principal underStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit under_solved
  exact ⟨state, finished, solved, drive_solved_principal anyOnly solved⟩

/-- **So this fragment store is decided, with a principal answer.** -/
theorem under_in_fragment_principal :
    InFragmentStore underStore ∧ ∃ state finished, run anyOnly underStore 5 = .solved state finished ∧
      (frames setting.levels).Principal underStore state.answer :=
  ⟨under_in_fragment, under_principal⟩

/-! ## Pairs under an abstraction -/

theorem pairFamily_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 withFamily
    (.pi (.head (.sort Tower.zero)) (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))).isSome := by
  decide +kernel

/-- `U0 → Σ U0 U0` over `A : U0, G : U0 → U0`. -/
def pairFamilyAt : TypeOver withFamily :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withFamily
    (.pi (.head (.sort Tower.zero)) (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))).get
      pairFamily_formed).val

/-- A function `U0 → Σ U0 U0` over `A G`, checked by the executable checker. -/
def checkedPairs (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 withFamily.raw code pairFamilyAt.code).isSome = true) :
    Term withFamily pairFamilyAt :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 withFamily.raw code pairFamilyAt.code).get accepted).down withFamily.formed pairFamilyAt.isType⟩

theorem flexPair_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withFamily.raw (.lam (.pair (.app (.var 1) (.var 0)) (.var 0)))
    pairFamilyAt.code).isSome = true := by
  decide +kernel

theorem diagonalPair_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withFamily.raw (.lam (.pair (.var 0) (.var 0)))
    pairFamilyAt.code).isSome = true := by
  decide +kernel

/-- `λ x. (G x, x) ≐ λ x. (x, x)` at `U0 → Σ U0 U0`. -/
def pairStore : EquationStore (TotalTerm withFamily) :=
  [(⟨pairFamilyAt, checkedPairs _ flexPair_checked⟩, ⟨pairFamilyAt, checkedPairs _ diagonalPair_checked⟩)]

theorem pairStore_length : pairStore.length = 1 := rfl

def pairEquation : Equation (TotalTerm withFamily) :=
  pairStore.head (List.ne_nil_of_length_pos (by rw [pairStore_length]; decide))

theorem pairStore_eq : pairStore = [pairEquation] := rfl

/-- **`λ x. (G x, x) ≐ λ x. (x, x)` is in the dynamic pattern fragment.** -/
theorem pair_in_fragment : InFragmentStore pairStore := by
  rw [pairStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl pairEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The ranked occurs solver leaves it suspended**: R94's pair decomposition reads pairs at a Σ
annotation only. -/
theorem pair_rankedOccurs_suspended : (run rankedOccursOnly pairStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked abstraction solver commits on it.** -/
theorem pair_solved : (run anyOnly pairStore 5).readout = .commit := by decide +kernel

theorem pair_principal :
    ∃ state finished, run anyOnly pairStore 5 = .solved state finished ∧
      (frames setting.levels).Principal pairStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit pair_solved
  exact ⟨state, finished, solved, drive_solved_principal anyOnly solved⟩

/-! ## The earlier witnesses -/

theorem loop_refuted : (run anyOnly loopStore 2).readout = .refuted := by decide +kernel

theorem crossedDomains_refuted :
    (run anyOnly ContextualDependentRank.Controls.crossedDomainsStore 3).readout = .refuted := by
  decide +kernel

theorem codomain_refuted :
    (run anyOnly ContextualDependentFragmentComplete.Controls.codomainStore 2).readout = .refuted := by
  decide +kernel

theorem id_refuted : (run anyOnly idStore 2).readout = .refuted := by decide +kernel

theorem blocked_solved : (run anyOnly blockedStore 2).readout = .commit := by decide +kernel

theorem crossed_solved : (run anyOnly crossedStore 2).readout = .commit := by decide +kernel

theorem flexible_run_not_refuted : (run anyOnly flexibleStore 4).readout ≠ .refuted := by decide +kernel

theorem repeated_suspended : (run anyOnly repeatedStore 4).readout = .suspended := by decide +kernel

end ContextualDependentSpinesMany.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
