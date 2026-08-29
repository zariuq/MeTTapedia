import Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary

/-!
# Continuous compressed A/Z proof control

This file keeps the kernel replay for one proof-reference byte followed by a
save byte separate from the reusable compressed machine and other controls.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAZCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- `AZ` is interpreted byte by byte in one scheduled MM2 run.  A selects
heap entry zero; Z saves the same node identity at heap entry one; terminal
acceptance observes the unchanged single-node stack. -/
theorem compressedAZ_run_accepts_and_save_reuses_identity :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 20
        compressedAZProgram).1
    canaryAccepted ∈ final ∧
      canarySavedHeapOne ∈ final ∧
      canaryUnexpectedNodeOne ∉ final := by
  decide +kernel

/-- Removing the source heap entry keeps the compact bytes identical but
prevents target acceptance. -/
theorem compressedAZ_without_heap_entry_does_not_accept :
    canaryAccepted ∉
      (cReflectiveSourceWorkQueueRunN .leaveInert 20
        (compressedAZProgram.erase canaryHeapZero)).1 := by
  decide +kernel

#print axioms compressedAZ_run_accepts_and_save_reuses_identity
#print axioms compressedAZ_without_heap_entry_does_not_accept

end Mettapedia.Languages.Metamath.MM2CompressedProofAZCanary
