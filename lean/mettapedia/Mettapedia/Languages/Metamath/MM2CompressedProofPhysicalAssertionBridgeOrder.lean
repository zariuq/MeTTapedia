import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff

/-!
# Scheduler order at the compressed assertion handoff

The normal-dispatch bridge must run before the dormant assertion rejoin.  This
module records the exact physical MORK scheduler comparison independently of
the surrounding assertion state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeOrder

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.ProcessCalculi.MORK

theorem normalDispatchBridge_scheduler_preempts_assertionRejoin :
    lexLt (SchedulerKey.key compressedNormalDispatchBridgeDirective)
      (SchedulerKey.key compressedAssertionRejoinDirective) = true := by
  decide +kernel

#print axioms normalDispatchBridge_scheduler_preempts_assertionRejoin

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeOrder
