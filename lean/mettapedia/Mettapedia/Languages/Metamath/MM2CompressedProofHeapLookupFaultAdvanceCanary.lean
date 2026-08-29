import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultAdvanceCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem lookup_fault_advance_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupFaultAfterProbe =
      some lookupFaultAfterAdvance := by
  decide +kernel

#print axioms lookup_fault_advance_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultAdvanceCanary
