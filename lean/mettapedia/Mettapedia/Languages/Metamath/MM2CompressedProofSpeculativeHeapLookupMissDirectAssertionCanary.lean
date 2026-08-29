import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectProofCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveInertFiring

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectAssertionCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- After the inert proof probe, the direct assertion probe remains ahead of
the untouched cursor verifier. -/
theorem speculative_miss_after_direct_proof_supported_exact :
    cSupportedSourceExecFacts speculativeMissAfterDirectProof =
      [compressedProofStepDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
       speculativeDirectAssertionDirective] := by
  rfl

theorem speculative_miss_direct_assertion_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        speculativeMissAfterDirectProof =
      some speculativeMissAfterDirectAssertion := by
  decide +kernel

/-- The second owner-mismatched probe also leaves the ordinary lookup request
and pending stack step intact for the cursor fallback. -/
theorem speculative_miss_direct_assertion_is_inert :
    directLookupOne ∈ speculativeMissAfterDirectAssertion ∧
      directStepPending ∈ speculativeMissAfterDirectAssertion := by
  decide +kernel

/-- With no assertion-valued cell at the requested owner/index, firing the
generated assertion handler performs exactly the scheduler's inert-shell
consumption and adds no row. -/
theorem speculative_miss_direct_assertion_no_matches :
    cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          speculativeMissAfterDirectProof.erase
            speculativeDirectAssertionDirective.atom)
        speculativeDirectAssertionDirective.rule.input = [] := by
  decide +kernel

theorem speculative_miss_direct_assertion_eq_erase :
    speculativeMissAfterDirectAssertion =
      speculativeMissAfterDirectProof.erase
        speculativeDirectAssertionDirective.atom := by
  exact cFireReflectiveSourceExecFact_eq_erase_of_no_matches _ _
    speculative_miss_direct_assertion_no_matches

#print axioms speculative_miss_after_direct_proof_supported_exact
#print axioms speculative_miss_direct_assertion_selected
#print axioms speculative_miss_direct_assertion_is_inert
#print axioms speculative_miss_direct_assertion_no_matches
#print axioms speculative_miss_direct_assertion_eq_erase

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectAssertionCanary
