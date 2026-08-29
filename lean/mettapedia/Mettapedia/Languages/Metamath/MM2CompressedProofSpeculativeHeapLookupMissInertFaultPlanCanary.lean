import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertAssertionPlanCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertFaultPlanCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorProofCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertPlanData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertAssertionPlanCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem speculative_miss_after_cursor_proof_supported_exact :
    cSupportedSourceExecFacts
        (cFireReflectiveSourceExecFact
          (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
            speculativeDirectAssertionDirective)
          compressedProofStepDirective) =
      missAfterCursorProofCandidates := by
  exact cSupportedSourceExecFacts_after_inert
    (cFireReflectiveSourceExecFact
      speculativeMissAfterDirectProof speculativeDirectAssertionDirective)
    compressedProofStepDirective missAfterDirectAssertionCandidates
    extract_compressedProofStepRule_exact
    speculative_miss_cursor_proof_no_matches
    speculative_miss_after_direct_assertion_supported_exact

#print axioms speculative_miss_after_cursor_proof_supported_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertFaultPlanCanary
