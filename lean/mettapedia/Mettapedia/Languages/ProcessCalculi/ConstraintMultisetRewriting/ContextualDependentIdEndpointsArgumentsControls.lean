import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpointsArguments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusControls

/-!
# The occurs check at spine arguments, on concrete stores

Over `A : U0, F : (U0 → U0) → U0`, at `(U0 → U0) → U0`:

* **`λ g. F g ≐ λ g. g (F g)`** and **`λ g. F g ≐ λ g. g (g (F g))`** are in the dynamic pattern fragment and
  have no solution. The projections solver leaves them suspended; the arguments solver refutes them with a
  certificate.

**Regressions** keep their readouts, and the three census rows still unread stay suspended at budget 16:
a spine at a flexible base type, nested projections, and a projection applied to arguments.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIdEndpointsArguments.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern ContextualDependentDynamicFragment
open ContextualDependentSpinesMany.Controls ContextualDependentFragmentDecisive.ClashControls
open ContextualDependentConstantHeads.Controls ContextualDependentCensusPairEta.Controls
open ContextualDependentConstantHeadsProjections.Controls ContextualDependentCensus.Controls

/-- The arguments solver of the tower controls, as a fuel-indexed family. -/
noncomputable def argumentsTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  argumentsFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The arguments solver at budget 16. -/
noncomputable def argumentsOnly : Solver setting.levels := argumentsTower.solver 16

/-! ## Occurrences in spine arguments -/

theorem argument_refuted : (run argumentsOnly argumentStore 8).readout = .refuted := by decide +kernel

theorem argument_unsolvable : ¬ (frames setting.levels).Solvable argumentStore :=
  drive_refuted argumentsOnly 8 _ argument_refuted

/-- **`λ g. F g ≐ λ g. g (F g)` is in the fragment and has no solution.** -/
theorem argument_in_fragment_refuted : InFragmentStore argumentStore ∧ ¬ (frames setting.levels).Solvable argumentStore :=
  ⟨argument_in_fragment, argument_unsolvable⟩

theorem deepArgument_refuted : (run argumentsOnly deepArgumentStore 8).readout = .refuted := by decide +kernel

theorem deepArgument_unsolvable : ¬ (frames setting.levels).Solvable deepArgumentStore :=
  drive_refuted argumentsOnly 8 _ deepArgument_refuted

/-! ## Regressions -/

theorem projectionSpine_arguments_committed : (run argumentsOnly projectionSpineStore 8).readout = .commit := by
  decide +kernel
theorem clashSpine_arguments_refuted : (run argumentsOnly clashSpineStore 8).readout = .refuted := by decide +kernel
theorem endpoint_arguments_refuted : (run argumentsOnly endpointStore 8).readout = .refuted := by decide +kernel
theorem projector_arguments_committed : (run argumentsOnly projectorStore 8).readout = .commit := by decide +kernel
theorem pairEta_arguments_refuted : (run argumentsOnly pairEtaStore 8).readout = .refuted := by decide +kernel
theorem projections_arguments_refuted : (run argumentsOnly projectionsStore 8).readout = .refuted := by decide +kernel
theorem twin_arguments_committed :
    (run argumentsOnly ContextualDependentTwinsUnder.Controls.twinStore 8).readout = .commit := by decide +kernel
theorem clashTwin_arguments_refuted :
    (run argumentsOnly ContextualDependentTwinsUnder.Controls.clashTwinStore 8).readout = .refuted := by decide +kernel
theorem sameHeads_arguments_committed : (run argumentsOnly sameHeadsStore 8).readout = .commit := by decide +kernel

/-! ## Still unread, at budget 16 -/

theorem flexibleBase_arguments_suspended : (run argumentsOnly flexibleBaseStore 8).readout = .suspended := by
  decide +kernel
theorem nested_arguments_suspended :
    (run argumentsOnly ContextualDependentCensus.Controls.nestedStore 8).readout = .suspended := by decide +kernel
theorem applied_arguments_suspended : (run argumentsOnly appliedStore 8).readout = .suspended := by decide +kernel

end ContextualDependentIdEndpointsArguments.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
