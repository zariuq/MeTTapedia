import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance3Controls

/-!
# The census under the last family: projections, clashes, and the gap witnesses

The third part of the census of `ContextualDependentAcceptance3Controls`, with R110's gap witnesses (`cumulativeStore`,
`twiceStore`, `witnessStore`) and R116's twin witness (`twinStore`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance3.Controls

open ContextualDependentPatternFiring.Controls ContextualDependentShortClosure.Controls

theorem projections_final : finalDecided ContextualDependentConstantHeads.Controls.projectionsStore = true := by
  decide +kernel
theorem former_final : finalDecided ContextualDependentConstantHeads.Controls.formerStore = true := by decide +kernel
theorem refl_final : finalDecided ContextualDependentConstantHeads.Controls.reflStore = true := by decide +kernel
theorem local_final : finalDecided ContextualDependentConstantHeads.Controls.localStore = true := by decide +kernel
theorem pairEta_final : finalDecided ContextualDependentConstantHeads.Controls.pairEtaStore = true := by
  decide +kernel
theorem pairConstant_final : finalDecided ContextualDependentConstantHeads.Controls.pairConstantStore = true := by
  decide +kernel
theorem endpoint_final : finalDecided ContextualDependentConstantHeads.Controls.endpointStore = true := by
  decide +kernel
theorem clashTwin_final : finalDecided ContextualDependentTwinsUnder.Controls.clashTwinStore = true := by
  decide +kernel
theorem idNested_final : finalDecided ContextualDependentIdEndpoints.Controls.nestedStore = true := by decide +kernel
theorem underLocal_final : finalDecided ContextualDependentIdEndpoints.Controls.underLocalStore = true := by
  decide +kernel
theorem under_final : finalDecided ContextualDependentIdEndpoints.Controls.underStore = true := by decide +kernel
theorem clashSpine_final :
    finalDecided ContextualDependentConstantHeadsProjections.Controls.clashSpineStore = true := by decide +kernel
theorem cumulative_final : finalDecided cumulativeStore = true := by decide +kernel
theorem twice_final : finalDecided ContextualDependentIntersection.Controls.twiceStore = true := by decide +kernel
theorem witness_final : finalDecided ContextualDependentInPlaceClosure.witnessStore = true := by decide +kernel
theorem twin_final : finalDecided twinStore = true := by decide +kernel

end ContextualDependentAcceptance3.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
