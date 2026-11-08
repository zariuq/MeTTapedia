import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance3Controls

/-!
# The census under the last family: constant heads, twins, endpoints, refutations

The second part of the census of `ContextualDependentAcceptance3Controls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance3.Controls

open ContextualDependentPatternFiring.Controls

theorem sameHeads_final : finalDecided ContextualDependentConstantHeads.Controls.sameHeadsStore = true := by
  decide +kernel
theorem projectionSpine_final :
    finalDecided ContextualDependentConstantHeads.Controls.projectionSpineStore = true := by decide +kernel
theorem twinsUnder_final : finalDecided ContextualDependentTwinsUnder.Controls.twinStore = true := by decide +kernel
theorem homogeneous_final : finalDecided ContextualDependentTwinsUnder.Controls.homogeneousStore = true := by
  decide +kernel
theorem endpointsCommit_final :
    finalDecided ContextualDependentIdEndpoints.Controls.endpointsCommitStore = true := by decide +kernel
theorem secondSpine_final :
    finalDecided ContextualDependentConstantHeadsProjections.Controls.secondSpineStore = true := by decide +kernel
theorem projector_final : finalDecided ContextualDependentCensusPairEta.Controls.projectorStore = true := by
  decide +kernel
theorem occurs_final : finalDecided occursStore = true := by decide +kernel
theorem headFree_final : finalDecided headFreeStore = true := by decide +kernel
theorem rigid_final : finalDecided rigidStore = true := by decide +kernel
theorem older_final : finalDecided olderStore = true := by decide +kernel
theorem swapped_final : finalDecided swappedStore = true := by decide +kernel
theorem nestedClash_final : finalDecided ContextualDependentCensus.Controls.nestedClashStore = true := by
  decide +kernel
theorem argument_final : finalDecided ContextualDependentCensus.Controls.argumentStore = true := by decide +kernel
theorem deepArgument_final : finalDecided ContextualDependentCensus.Controls.deepArgumentStore = true := by
  decide +kernel

end ContextualDependentAcceptance3.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
