import Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSingleIndexAcceptCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- One compact `A` reference is decoded, resolved through heap entry zero,
and accepted by the scheduled MM2 verifier without source-side expansion. -/
theorem compressed_single_index_run_accepts :
    canaryAccepted ∈
      (cReflectiveSourceWorkQueueRunN .leaveInert 16
        compressedSingleIndexProgram).1 := by
  decide +kernel

#print axioms compressed_single_index_run_accepts

end Mettapedia.Languages.Metamath.MM2CompressedProofSingleIndexAcceptCanary
