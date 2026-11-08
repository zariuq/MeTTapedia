import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFullUnder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRankControls

/-!
# The occurs check under abstractions on concrete stores

* **A fragment store refused under its abstraction.** Over `A : U0, G : U0 → U0`, the equation
  `λ x. G x ≐ λ x. Π (G x) x` at `U0 → U0` is in the dynamic pattern fragment and has no solution: its
  body would make `G x` contain itself. The full occurs solver and the recognition solver leave it
  suspended; the ranked occurs solver refutes it with a certificate.
* **The earlier witnesses keep their readouts**, including the ranked solver's.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentOccursFull.UnderControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment

/-- The ranked occurs solver of the tower controls, as a fuel-indexed family. -/
noncomputable def rankedOccursTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  rankedOccursFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The ranked occurs solver at budget 16. -/
noncomputable def rankedOccursOnly : Solver setting.levels := rankedOccursTower.solver 16

/-! ## The store -/

theorem familyAt_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16
    withFamily (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))).isSome := by
  decide +kernel

/-- `U0 → U0` over `A : U0, G : U0 → U0`. -/
def familyAt : TypeOver withFamily :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withFamily
    (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))).get familyAt_formed).val

/-- A function `U0 → U0` over `A G`, checked by the executable checker. -/
def checkedFamily (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 withFamily.raw code familyAt.code).isSome = true) :
    Term withFamily familyAt :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 withFamily.raw code familyAt.code).get accepted).down withFamily.formed familyAt.isType⟩

theorem selfFamily_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withFamily.raw (.lam (.app (.var 1) (.var 0)))
    familyAt.code).isSome = true := by
  decide +kernel

theorem loopFamily_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withFamily.raw (.lam (.pi (.app (.var 1) (.var 0)) (.var 1)))
    familyAt.code).isSome = true := by
  decide +kernel

/-- `λ x. G x ≐ λ x. Π (G x) x` at `U0 → U0`. -/
def loopStore : EquationStore (TotalTerm withFamily) :=
  [(⟨familyAt, checkedFamily _ selfFamily_checked⟩, ⟨familyAt, checkedFamily _ loopFamily_checked⟩)]

theorem loopStore_length : loopStore.length = 1 := rfl

def loopEquation : Equation (TotalTerm withFamily) :=
  loopStore.head (List.ne_nil_of_length_pos (by rw [loopStore_length]; decide))

theorem loopStore_eq : loopStore = [loopEquation] := rfl

/-- **`λ x. G x ≐ λ x. Π (G x) x` is in the dynamic pattern fragment.** -/
theorem loop_in_fragment : InFragmentStore loopStore := by
  rw [loopStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl loopEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The full occurs solver leaves it suspended.** -/
theorem loop_occursFull_suspended :
    (run ContextualDependentOccursFull.Controls.occursFullOnly loopStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked solver leaves it suspended.** -/
theorem loop_ranked_suspended : (run ContextualDependentRank.Controls.rankedOnly loopStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked occurs solver refutes it.** -/
theorem loop_refuted : (run rankedOccursOnly loopStore 2).readout = .refuted := by decide +kernel

/-- **`λ x. G x ≐ λ x. Π (G x) x` has no solution**: the refutation is certified. -/
theorem loop_unsolvable : ¬ (frames setting.levels).Solvable loopStore :=
  drive_refuted rankedOccursOnly 2 _ loop_refuted

/-- **So this fragment store is decided, by a certified refutation.** -/
theorem loop_in_fragment_refuted :
    InFragmentStore loopStore ∧ ¬ (frames setting.levels).Solvable loopStore :=
  ⟨loop_in_fragment, loop_unsolvable⟩

/-! ## The earlier witnesses -/

theorem crossedDomains_refuted :
    (run rankedOccursOnly ContextualDependentRank.Controls.crossedDomainsStore 3).readout = .refuted := by
  decide +kernel

theorem codomain_refuted :
    (run rankedOccursOnly ContextualDependentFragmentComplete.Controls.codomainStore 2).readout = .refuted := by
  decide +kernel

theorem id_refuted : (run rankedOccursOnly idStore 2).readout = .refuted := by decide +kernel

theorem blocked_solved : (run rankedOccursOnly blockedStore 2).readout = .commit := by decide +kernel

theorem crossed_solved : (run rankedOccursOnly crossedStore 2).readout = .commit := by decide +kernel

theorem flexible_run_not_refuted : (run rankedOccursOnly flexibleStore 4).readout ≠ .refuted := by decide +kernel

theorem repeated_suspended : (run rankedOccursOnly repeatedStore 4).readout = .suspended := by decide +kernel

end ContextualDependentOccursFull.UnderControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
