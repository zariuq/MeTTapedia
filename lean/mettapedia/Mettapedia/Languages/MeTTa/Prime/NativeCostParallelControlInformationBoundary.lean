import Mettapedia.Languages.MeTTa.Prime.NativeObservationControlledCostWaves
import Mettapedia.Languages.MeTTa.Prime.NativeCostLayerReceiptPolicyNIKAdmission
import Mettapedia.Languages.MeTTa.Prime.SelectedCostLayerIterationBoundary

/-!
# Information boundary for native Cost/parallel control

This module records the joint boundary exposed by three independently proved
parts of the Prime theory.

* A complete final-state bag may activate an exactly separated family as one
  bulk wave.
* The same occurrence family is not permutation-invariant when exact event
  chronology is requested.
* `WorkSpan` is a sufficient implementation key for a WorkSpan-only consumer,
  but is insufficient for chronological receipts.
* The selected compact cost-layer key is runnable for its declared policy but
  is not an exact replay key.

Consequently no scalar schedule value and no compact elaboration key may be
treated as a universal control key.  Key selection is request-scoped, while
wave activation is observation- and resource-scoped.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeCostParallelControlInformationBoundary

open Mettapedia.Algebra
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeObservationControlledCostWaves
open Mettapedia.Languages.MeTTa.Prime.NativeObservationControlledCostWaves.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeCostLayerReceiptObservation
open Mettapedia.Languages.MeTTa.Prime.NativeCostLayerReceiptPolicyNIKAdmission
open Mettapedia.Languages.MeTTa.Prime.CostElaborationKeyContract
open Mettapedia.Languages.MeTTa.Prime.SelectedCostLayerIterationBoundary

/-! ## Exact runtime-control boundary -/

/-- The concrete two-event family simultaneously exhibits legal bulk
activation at final-bag observation, refusal at exact chronology, and
request-scoped WorkSpan-key admission. -/
theorem final_bag_bulk_but_chronology_requires_a_richer_key
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    ((CertifiedFamilyBridge.toCompleteResourceBudgetCertified
        NativeInteractionFamilyFibration.Examples.oneColourFamily).plan
          .general).activation = .bulk ∧
      ¬ (chronologicalExecutionSemantics
          NativeInteractionFibration.Examples.Ground).SerializesTo
        (NativeInteractionFibration.Examples.source, [])
        [NativeInteractionFibration.Examples.leftEvent,
          NativeInteractionFibration.Examples.rightEvent]
        (NativeInteractionFamilyFibration.Examples.oneColourFamily.target,
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.costWaveTrace
            [NativeInteractionFibration.Examples.leftEvent,
              NativeInteractionFibration.Examples.rightEvent]) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (workOnlyRequest NativeInteractionFibration.Examples.Ground)
          (historyWorkSpan :
            History NativeInteractionFibration.Examples.Ground → WorkSpan)) ∧
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (receiptRequest NativeInteractionFibration.Examples.Ground)
          (historyWorkSpan :
            History NativeInteractionFibration.Examples.Ground → WorkSpan)) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (receiptRequest NativeInteractionFibration.Examples.Ground)
          (policyVectorKey
            (receiptRequest NativeInteractionFibration.Examples.Ground))) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (receiptRequest NativeInteractionFibration.Examples.Ground)
          (id : History NativeInteractionFibration.Examples.Ground →
            History NativeInteractionFibration.Examples.Ground)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact CertifiedBatch.completeBag_dispatches_bulk
      (CertifiedFamilyBridge.toCompleteResourceBudgetCertified
        NativeInteractionFamilyFibration.Examples.oneColourFamily) rfl
  · exact separated_pair_not_serializable_at_exact_chronology
  · exact request_scoped_key_boundary dependencies revision

/-! ## Cost-layer iteration boundary -/

/-- The selected compact cost-layer key remains useful for its declared hot
policy, but exact replay still requires the displayed state.  This is the
elaboration-level analogue of the runtime chronology boundary above. -/
theorem compact_policy_key_is_not_a_universal_replay_key
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostLayerConfiguration.source) False)
          (compactCarrierKey rhoSelectedCostLayerConfiguration.source)) ∧
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostLayerConfiguration.source) True)
          (compactCarrierKey rhoSelectedCostLayerConfiguration.source)) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (singlePolicyRequest
            (compactCarrierKey rhoSelectedCostLayerConfiguration.source) True)
          (id : RhoSelectedCostLayerIterationState →
            RhoSelectedCostLayerIterationState)) :=
  rhoSelectedCostLayerIteration_global_key_boundary dependencies revision

/-! ## Axiom audit -/

#print axioms final_bag_bulk_but_chronology_requires_a_richer_key
#print axioms compact_policy_key_is_not_a_universal_replay_key

end Mettapedia.Languages.MeTTa.Prime.NativeCostParallelControlInformationBoundary
