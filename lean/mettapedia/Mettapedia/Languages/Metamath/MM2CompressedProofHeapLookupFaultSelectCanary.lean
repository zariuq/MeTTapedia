import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultSelectCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem lookup_frontier_fault_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupFaultAfterProofProbe =
      some lookupFaultAfterFault := by
  decide +kernel

#print axioms lookup_frontier_fault_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultSelectCanary
