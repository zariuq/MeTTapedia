import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitAdvanceCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem lookup_hit_advance_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupHitAfterAssertionProbe =
      some lookupHitAfterAdvance := by
  exact lookup_step_of_selected lookupHitAfterAssertionProbe compressedHeapLookupAdvanceDirective
    (Eq.trans (congrArg selectNextScheduled lookup_hit_after_assertion_supported_exact)
      (by rfl))

#print axioms lookup_hit_advance_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitAdvanceCanary
