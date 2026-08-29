import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultAdvanceCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem reserved_fault_advance_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        lookupReservedFaultAfterProbe =
      some lookupReservedFaultAfterAdvance := by
  decide +kernel

#print axioms reserved_fault_advance_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultAdvanceCanary
