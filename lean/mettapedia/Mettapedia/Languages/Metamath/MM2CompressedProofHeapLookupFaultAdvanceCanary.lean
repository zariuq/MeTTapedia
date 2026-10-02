import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProbeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultAdvanceCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem lookup_fault_advance_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupFaultAfterAssertionProbe =
      some lookupFaultAfterAdvance := by
  exact lookup_step_of_selected lookupFaultAfterAssertionProbe compressedHeapLookupAdvanceDirective
    (Eq.trans (congrArg selectNextScheduled lookup_fault_after_assertion_supported_exact)
      (by rfl))

#print axioms lookup_fault_advance_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultAdvanceCanary
