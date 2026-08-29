import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissTerminalCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectProofCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertPlanCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFrontierFaultStepCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultPresentCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissResultCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissContinuousCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissTerminalCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectProofCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertPlanCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFrontierProofStepCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFrontierFaultStepCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultPresentCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissResultCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- After the two generated direct probes, the retained cursor verifier walks
to the first-free heap frontier and emits the missing-reference fault along
one continuous seven-step execution suffix. -/
theorem speculative_miss_after_direct_to_fault_reachable :
    CReflectiveReachable .leaveInert 7 speculativeMissAfterDirectProof
      speculativeMissAfterFrontierFault := by
  have afterAdvanceToProof :
      CReflectiveReachable .leaveInert 6 speculativeMissAfterDirectProof
        speculativeMissAfterFrontierProofProbe :=
    speculative_miss_inert_probes_then_advance_reachable.then_step
      speculative_miss_frontier_proof_probe_selected
  exact afterAdvanceToProof.then_step
    speculative_miss_frontier_fault_selected

/-- The complete foreign-owner miss starts from the transformed program,
threads every scheduler successor into the next transition, and ends in the
authored compact-heap fault observation. -/
theorem speculative_wrong_owner_miss_faults_continuously :
    CReflectiveReachable .leaveInert 9 speculativeMissProgram
        speculativeMissAfterFrontierFault ∧
      missingOneFault ∈ speculativeMissAfterFrontierFault := by
  constructor
  · exact .step speculative_miss_terminal_selected
      (.step speculative_miss_direct_proof_selected
        speculative_miss_after_direct_to_fault_reachable)
  · exact speculative_miss_fault_present

/-- The continuous wrong-owner path has the exact consume/emit result: the
source-bound fault is present, no stack result is invented, and neither the
old nor frontier lookup, pending step, or live machine remains. -/
theorem speculative_wrong_owner_miss_has_exclusive_fault_result :
    CReflectiveReachable .leaveInert 9 speculativeMissProgram
        speculativeMissAfterFrontierFault ∧
      (missingOneFault ∈ speculativeMissAfterFrontierFault ∧
        resolvedStackCell ∉ speculativeMissAfterFrontierFault ∧
        directLookupOne ∉ speculativeMissAfterFrontierFault ∧
        MM2CompressedProofSpeculativeHeapLookupMissFaultInputData.frontierLookupOne ∉
          speculativeMissAfterFrontierFault ∧
        directStepPending ∉ speculativeMissAfterFrontierFault ∧
        machineWithOneHeapEntry ∉ speculativeMissAfterFrontierFault) := by
  exact ⟨speculative_wrong_owner_miss_faults_continuously.1,
    speculative_miss_frontier_fault_is_exclusive⟩

#print axioms speculative_miss_after_direct_to_fault_reachable
#print axioms speculative_wrong_owner_miss_faults_continuously
#print axioms speculative_wrong_owner_miss_has_exclusive_fault_result

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissContinuousCanary
