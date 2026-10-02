import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultProbeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultAdvanceCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem reserved_fault_advance_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        lookupReservedFaultAfterAssertionProbe =
      some lookupReservedFaultAfterAdvance := by
  exact lookup_step_of_selected lookupReservedFaultAfterAssertionProbe
    compressedHeapLookupAdvanceDirective
    (Eq.trans (congrArg selectNextScheduled reserved_after_initial_assertion_supported_exact)
      (by rfl))

#print axioms reserved_fault_advance_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultAdvanceCanary
