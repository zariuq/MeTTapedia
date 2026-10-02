import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultAdvanceCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProofProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

theorem lookup_fault_after_advance_supported_exact :
    cSupportedSourceExecFacts lookupFaultAfterAdvance =
      [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
       compressedProofStepDirective, compressedAssertionLaunchDirective] := by
  decide +kernel

/-- No proof-valued heap row exists at the first-free frontier. -/
theorem lookup_fault_proof_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupFaultAfterAdvance =
      some lookupFaultAfterProofProbe := by
  exact lookup_step_of_selected lookupFaultAfterAdvance compressedProofStepDirective
    (Eq.trans (congrArg selectNextScheduled lookup_fault_after_advance_supported_exact)
      lookup_select_fault_initial_proof)

theorem lookup_fault_frontier_proof_no_matches :
    cmatchInputSpec []
        (compressedProofStepDirective.atom ::
          lookupFaultAfterAdvance.erase compressedProofStepDirective.atom)
        compressedProofStepDirective.rule.input = [] := by
  decide +kernel

theorem lookup_fault_after_proof_supported_exact :
    cSupportedSourceExecFacts lookupFaultAfterProofProbe =
      [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
       compressedAssertionLaunchDirective] := by
  exact Eq.trans
    (cSupportedSourceExecFacts_after_inert lookupFaultAfterAdvance
      compressedProofStepDirective _ extract_compressedProofStepRule_exact
      lookup_fault_frontier_proof_no_matches lookup_fault_after_advance_supported_exact)
    (by decide +kernel)

#print axioms lookup_fault_proof_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProofProbeCanary
