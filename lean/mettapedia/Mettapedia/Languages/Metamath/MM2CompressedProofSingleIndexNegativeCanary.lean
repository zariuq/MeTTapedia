import Mettapedia.Languages.Metamath.MM2CompressedProofSingleIndexAcceptCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSingleIndexNegativeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- Keeping the compact `A` input fixed while severing heap entry zero cannot
manufacture target acceptance. -/
theorem compressed_single_index_without_heap_does_not_accept :
    canaryAccepted ∉
      (cReflectiveSourceWorkQueueRunN .leaveInert 16
        (compressedSingleIndexProgram.erase canaryHeapZero)).1 := by
  decide +kernel

#print axioms compressed_single_index_without_heap_does_not_accept

end Mettapedia.Languages.Metamath.MM2CompressedProofSingleIndexNegativeCanary
