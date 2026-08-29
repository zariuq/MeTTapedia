import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectAssertionScheduling

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Once the generated proof-valued direct probe is consumed, the generated
assertion-valued probe is the next physical scheduler candidate. -/
theorem select_direct_assertion_after_direct_proof :
    selectNextScheduled
        [compressedProofStepDirective, compressedAssertionLaunchDirective,
         compressedHeapLookupFaultDirective,
         compressedHeapLookupAdvanceDirective,
         speculativeDirectAssertionDirective] =
      some speculativeDirectAssertionDirective := by
  decide +kernel

#print axioms select_direct_assertion_after_direct_proof

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectAssertionScheduling
