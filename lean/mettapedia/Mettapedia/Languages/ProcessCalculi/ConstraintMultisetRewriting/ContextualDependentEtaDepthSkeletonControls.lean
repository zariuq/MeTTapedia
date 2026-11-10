import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthSkeletonFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthGap

/-!
# Controls for the η-long prepared family and the skeleton family

* **The η-long prepared family** (`etaTower`) refutes `λ g. g ≐ λ g x. x`, `λ g x. x ≐ λ g. g`,
  `λ g. g ≐ λ g x. g (g x)` and `λ g h. g ≐ λ g h x. h x`, commits on `λ g x. g (F g x) ≐ λ g. g`, and is stuck in its
  first round on `λ g. g ≐ λ g x. x` at the flexible base `(A → A) → A → A`.
* **The skeleton family** (`skeletonTower`) refutes that store with a certified refutation, so it is unsolvable
  (`flexible_unsolvable`), and keeps the other outcomes.
* Both families decide R119's 44 census stores as the in-place family does (`eta_of_final`, `skeleton_of_final`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentIntersectionGeneral.InPlaceControls ContextualDependentIntersectionGeneral.DeadControls

/-! ## The η-long prepared family -/

theorem shallow_eta_refuted : (run (etaTower.solver 16) shallowStore 8).readout = .refuted := by decide +kernel
theorem deep_eta_refuted : (run (etaTower.solver 16) deepStore 8).readout = .refuted := by decide +kernel
theorem twice_eta_refuted : (run (etaTower.solver 16) twiceStore 8).readout = .refuted := by decide +kernel
theorem other_eta_refuted : (run (etaTower.solver 16) otherStore 8).readout = .refuted := by decide +kernel
theorem solvable_eta_committed : (run (etaTower.solver 16) solvableStore 8).readout = .commit := by decide +kernel
/-- **The η-long prepared family is stuck at the flexible base.** -/
theorem flexible_eta_stuck : isStuck (run (etaTower.solver 16) flexibleStore 1) = true := by decide +kernel

/-! ## The skeleton family -/

/-- **The skeleton family refutes `λ g. g ≐ λ g x. x` at a flexible base.** -/
theorem flexible_skeleton_refuted : (run (skeletonTower.solver 16) flexibleStore 8).readout = .refuted := by
  decide +kernel
theorem flexible_unsolvable : ¬ (frames setting.levels).Solvable flexibleStore :=
  Outcome.readout_eq_refuted flexible_skeleton_refuted
theorem shallow_skeleton_refuted : (run (skeletonTower.solver 16) shallowStore 8).readout = .refuted := by
  decide +kernel
theorem solvable_skeleton_committed : (run (skeletonTower.solver 16) solvableStore 8).readout = .commit := by
  decide +kernel

/-! ## R119's census -/

/-- **R119's census under the η-long prepared family.** -/
theorem eta_of_final {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (final : ContextualDependentAcceptance3.Controls.finalDecided problem = true) :
    (run inPlaceOnly problem 8).Decided ∧ run (etaTower.solver 16) problem 8 = run inPlaceOnly problem 8 := by
  obtain ⟨decided, same⟩ := under_of_final final
  refine ⟨decided, ?_⟩
  have underDecided : (run (underTower.solver 16) problem 8).Decided := by rw [same]; exact decided
  rw [← same]
  exact eta_run_of_under (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening 16 8 problem
    underDecided

/-- **R119's census under the skeleton family.** -/
theorem skeleton_of_final {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (final : ContextualDependentAcceptance3.Controls.finalDecided problem = true) :
    (run inPlaceOnly problem 8).Decided ∧ run (skeletonTower.solver 16) problem 8 = run inPlaceOnly problem 8 := by
  obtain ⟨decided, same⟩ := eta_of_final final
  refine ⟨decided, ?_⟩
  have etaDecided : (run (etaTower.solver 16) problem 8).Decided := by rw [same]; exact decided
  rw [← same]
  exact skeleton_run_of_eta (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening 16 8 problem
    etaDecided

end ContextualDependentEtaDepth.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
