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
input; it is not accepted and does not silently become index zero. -/
theorem compressedIncompletePrefix_run_faults :
    canaryAccepted ∉
        (cReflectiveSourceWorkQueueRunN .leaveInert 3
          compressedIncompletePrefixProgram).1 ∧
      canaryIncompletePrefixFault ∈
        (cReflectiveSourceWorkQueueRunN .leaveInert 3
          compressedIncompletePrefixProgram).1 := by
  constructor <;> rfl

#print axioms compressedIncompletePrefix_run_faults

end Mettapedia.Languages.Metamath.MM2CompressedProofIncompletePrefixCanary
