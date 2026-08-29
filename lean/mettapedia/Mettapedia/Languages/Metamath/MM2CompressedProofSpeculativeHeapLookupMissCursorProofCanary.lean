import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultProbeCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofScheduling

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorProofCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectAssertionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultProbeCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- No proof-valued heap cell owned by the requested proof exists at cursor
zero, so the retained cursor proof probe is inert. -/
theorem speculative_miss_cursor_proof_no_matches :
    cmatchInputSpec []
        (compressedProofStepDirective.atom ::
          (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
            speculativeDirectAssertionDirective).erase
              compressedProofStepDirective.atom)
        compressedProofStepDirective.rule.input = [] := by
  decide +kernel

theorem speculative_miss_fault_selected_after_cursor_proof_erasure :
    selectNextScheduled
        (([compressedProofStepDirective, compressedAssertionLaunchDirective,
           compressedHeapLookupFaultDirective,
           compressedHeapLookupAdvanceDirective,
           speculativeDirectAssertionDirective].erase
            speculativeDirectAssertionDirective).erase
              compressedProofStepDirective) =
      some compressedHeapLookupFaultDirective := by
  have firstErase :
      [compressedProofStepDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
       speculativeDirectAssertionDirective].erase
          speculativeDirectAssertionDirective =
        [compressedProofStepDirective, compressedAssertionLaunchDirective,
         compressedHeapLookupFaultDirective,
         compressedHeapLookupAdvanceDirective] := by
    decide +kernel
  rw [firstErase, List.erase_cons_head]
  exact select_cursor_fault_after_proof_probe

/-- The direct assertion miss, ordinary proof-cell miss, and cursor fault
probe are one state-threaded three-step suffix over the transformed program. -/
theorem speculative_miss_direct_assertion_then_cursor_proof_then_fault :
    cReflectiveSourceWorkQueueStep .leaveInert
        (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
          speculativeDirectAssertionDirective) =
        some
          (cFireReflectiveSourceExecFact
            (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
              speculativeDirectAssertionDirective)
            compressedProofStepDirective) ∧
      cReflectiveSourceWorkQueueStep .leaveInert
        (cFireReflectiveSourceExecFact
          (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
            speculativeDirectAssertionDirective)
          compressedProofStepDirective) =
        some
          (cFireReflectiveSourceExecFact
            (cFireReflectiveSourceExecFact
              (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
                speculativeDirectAssertionDirective)
              compressedProofStepDirective)
            compressedHeapLookupFaultDirective) := by
  exact cReflectiveSourceWorkQueueStep_after_two_inert
    speculativeMissAfterDirectProof speculativeDirectAssertionDirective
    compressedProofStepDirective compressedHeapLookupFaultDirective
    [compressedProofStepDirective, compressedAssertionLaunchDirective,
     compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
     speculativeDirectAssertionDirective]
    extract_speculativeDirectAssertionDirective_exact
    speculative_miss_direct_assertion_no_matches
    speculative_miss_after_direct_proof_supported_exact
    speculative_miss_cursor_proof_selected_from_direct_interface
    extract_compressedProofStepRule_exact
    speculative_miss_cursor_proof_no_matches
    speculative_miss_fault_selected_after_cursor_proof_erasure

#print axioms speculative_miss_cursor_proof_no_matches
#print axioms speculative_miss_fault_selected_after_cursor_proof_erasure
#print axioms speculative_miss_direct_assertion_then_cursor_proof_then_fault

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorProofCanary
