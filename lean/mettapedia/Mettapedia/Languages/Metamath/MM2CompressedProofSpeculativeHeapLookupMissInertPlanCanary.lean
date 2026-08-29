import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorAssertionStepCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorAdvanceStepCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertPlanCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectAssertionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorProofCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorAssertionStepCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorAdvanceStepCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- The four inert probes followed by the cursor advance are one continuous
five-step execution prefix through the transformed verifier. -/
theorem speculative_miss_inert_probes_then_advance_reachable :
    CReflectiveReachable .leaveInert 5 speculativeMissAfterDirectProof
      speculativeMissAfterAdvance :=
  .step speculative_miss_direct_assertion_selected
    (.step speculative_miss_cursor_proof_probe_selected
      (.step
        speculative_miss_direct_assertion_then_cursor_proof_then_fault.2
        (.step speculative_miss_cursor_assertion_selected_continuously
          (.step speculative_miss_cursor_advance_selected_continuously .refl))))

#print axioms speculative_miss_inert_probes_then_advance_reachable

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissInertPlanCanary
