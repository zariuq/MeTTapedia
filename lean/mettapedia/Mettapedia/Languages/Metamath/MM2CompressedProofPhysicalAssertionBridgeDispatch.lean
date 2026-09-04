import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSelection

/-!
# Scheduled dispatch after the compressed assertion drain

Once the normal-dispatch bridge has been selected after the four-probe drain,
the rule-scoped work queue performs its exact physical firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDispatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSelection
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- The fifth physical transition after assertion launch is the captured
normal-dispatch bridge. -/
theorem normalDispatchBridge_steps_after_predecessor_drain
    (space final : List Atom) (ready : AssertionPredecessorDrainReady space)
    (drain : PhysicalAssertionPredecessorDrain space final)
    (bridgeMember : compressedNormalDispatchBridgeRule ∈ final) :
    cRuleScopedSourceWorkQueueStep .leaveInert final =
      some (cFireRuleScopedSourceExecFact final
        compressedNormalDispatchBridgeDirective) := by
  exact cRuleScopedSourceWorkQueueStep_of_selected _ _
    (normalDispatchBridge_selected_after_predecessor_drain space final ready
      drain bridgeMember)

#print axioms normalDispatchBridge_steps_after_predecessor_drain

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDispatch
