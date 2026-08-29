import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultPresentCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoStackCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoLookupCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoPendingCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoMachineCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissResultCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultPresentCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoStackCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoPendingCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissNoMachineCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInputData

/-- The wrong-owner path ends exclusively in the source-bound missing-index
fault: it cannot manufacture a stack result and leaves no live lookup request. -/
theorem speculative_miss_frontier_fault_is_exclusive :
    missingOneFault ∈ speculativeMissAfterFrontierFault ∧
      resolvedStackCell ∉ speculativeMissAfterFrontierFault ∧
      directLookupOne ∉ speculativeMissAfterFrontierFault ∧
      frontierLookupOne ∉ speculativeMissAfterFrontierFault ∧
      directStepPending ∉ speculativeMissAfterFrontierFault ∧
      machineWithOneHeapEntry ∉ speculativeMissAfterFrontierFault := by
  exact ⟨speculative_miss_fault_present,
    speculative_miss_has_no_resolved_stack_cell,
    speculative_miss_has_no_live_lookup,
    speculative_miss_has_no_frontier_lookup,
    speculative_miss_has_no_pending_step,
    speculative_miss_has_no_live_machine⟩

#print axioms speculative_miss_frontier_fault_is_exclusive

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissResultCanary
