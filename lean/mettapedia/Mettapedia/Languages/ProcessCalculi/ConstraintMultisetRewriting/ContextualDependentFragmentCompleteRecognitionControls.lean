import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRecognitionConversionControls

/-!
# The last composite solver on the witnesses

The recognition family extends the deep family by the conversion pattern rule; it is the last
composite of R94. At budget 16 it decides every witness that the deep family decides, with the same
readout, and leaves the codomain occurrence `X ≐ Π A X` suspended.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragmentComplete.RecognitionControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentRecognitionConversion ContextualDependentGeneralPattern

/-- The recognition solver of the tower controls, as a fuel-indexed family. -/
abbrev recognitionTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  recognitionFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The recognition solver at budget 16. -/
def recognitionOnly : Solver setting.levels := recognitionTower.solver 16

theorem id_refuted : (run recognitionOnly idStore 2).readout = .refuted := by decide +kernel

theorem blocked_solved : (run recognitionOnly blockedStore 2).readout = .commit := by decide +kernel

theorem pi_solved : (run recognitionOnly piStore 2).readout = .commit := by decide +kernel

theorem crossed_solved : (run recognitionOnly crossedStore 2).readout = .commit := by decide +kernel

theorem carriers_solved :
    (run recognitionOnly ContextualDependentRigidFormers.Controls.carriersStore 4).readout = .commit := by decide +kernel

theorem pair_solved :
    (run recognitionOnly ContextualDependentRigidFormers.Controls.pairStore 3).readout = .commit := by decide +kernel

theorem nested_domains_solved :
    (run recognitionOnly ContextualDependentRigidFormers.DeepControls.nestedDomainsStore 3).readout = .commit := by
  decide +kernel

theorem crossed_spine_refuted :
    (run recognitionOnly ContextualDependentRigidFormers.SpineControls.crossedSpineStore 2).readout = .refuted := by
  decide +kernel

theorem domain_occurs_refuted : (run recognitionOnly domainStore 2).readout = .refuted := by decide +kernel

theorem repeated_suspended : (run recognitionOnly repeatedStore 4).readout = .suspended := by decide +kernel

theorem codomain_suspended :
    (run recognitionOnly ContextualDependentFragmentComplete.Controls.codomainStore 4).readout = .suspended := by
  decide +kernel

end ContextualDependentFragmentComplete.RecognitionControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
