import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFrontierProofStepCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFrontierFaultStepCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- Once cursor one equals the first-free heap frontier, the retained fault
handler consumes the unresolved request. -/
theorem speculative_miss_frontier_fault_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        speculativeMissAfterFrontierProofProbe =
      some speculativeMissAfterFrontierFault := by
  decide +kernel

#print axioms speculative_miss_frontier_fault_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFrontierFaultStepCanary
