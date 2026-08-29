import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertFaultPlanCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertProofPlanCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorProofCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorFaultCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertPlanData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertFaultPlanCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem speculative_miss_after_cursor_fault_supported_exact :
    cSupportedSourceExecFacts
        (cFireReflectiveSourceExecFact
          (cFireReflectiveSourceExecFact
            (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
              speculativeDirectAssertionDirective)
            compressedProofStepDirective)
          compressedHeapLookupFaultDirective) =
      missAfterCursorFaultCandidates := by
  exact cSupportedSourceExecFacts_after_inert
    (cFireReflectiveSourceExecFact
      (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
        speculativeDirectAssertionDirective)
      compressedProofStepDirective)
    compressedHeapLookupFaultDirective missAfterCursorProofCandidates
    extract_compressedHeapLookupFaultRule_exact
    speculative_miss_cursor_fault_no_matches
    speculative_miss_after_cursor_proof_supported_exact

#print axioms speculative_miss_after_cursor_fault_supported_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertProofPlanCanary
