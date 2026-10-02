import Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary

/-!
# Incomplete-prefix compressed proof control
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofIncompletePrefixCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- An unfinished U--Y prefix produces an explicit proof fault at end of
input; it is not accepted and does not silently become index zero.  The
physical queue also consumes the reinstalled, inert prefix probe. -/
theorem compressedIncompletePrefix_run_faults :
    canaryAccepted ∉
        (cReflectiveSourceWorkQueueRunN .leaveInert 4
          compressedIncompletePrefixProgram).1 ∧
      canaryIncompletePrefixFault ∈
        (cReflectiveSourceWorkQueueRunN .leaveInert 4
          compressedIncompletePrefixProgram).1 := by
  decide +kernel

/-- Three steps leave the incomplete-index handler queued: the original
shorter bound cannot already have emitted the explicit fault. -/
theorem compressedIncompletePrefix_three_steps_not_faulted :
    canaryIncompletePrefixFault ∉
      (cReflectiveSourceWorkQueueRunN .leaveInert 3
        compressedIncompletePrefixProgram).1 := by
  decide +kernel

#print axioms compressedIncompletePrefix_run_faults
#print axioms compressedIncompletePrefix_three_steps_not_faulted

end Mettapedia.Languages.Metamath.MM2CompressedProofIncompletePrefixCanary
