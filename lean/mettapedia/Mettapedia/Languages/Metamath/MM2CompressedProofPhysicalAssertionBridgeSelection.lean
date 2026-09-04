import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeOrder
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionPostDrainInventory
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalBridgeSupportedMembership

/-!
# Normal-bridge selection after the assertion drain

After the four obsolete assertion-launch probes are erased, exact bridge
membership determines the least scheduler candidate independently of physical
list order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSelection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeOrder
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionPostDrainInventory
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalBridgeSupportedMembership
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- Exact bridge membership after the drain determines the scheduler result,
independently of list order. -/
theorem normalDispatchBridge_selected_after_predecessor_drain
    (space final : List Atom) (ready : AssertionPredecessorDrainReady space)
    (drain : PhysicalAssertionPredecessorDrain space final)
    (bridgeMember : compressedNormalDispatchBridgeRule ∈ final) :
    selectNextScheduled
        (cSupportedSourceExecFacts final) =
      some compressedNormalDispatchBridgeDirective := by
  apply selectNextScheduled_eq_some_of_mem_of_strict_minimum _ _
    (normalDispatchBridge_supported_of_mem bridgeMember)
  intro candidate member different
  have allowed :=
    postDrain_candidates_within_rejoin_bridge space final ready drain
      candidate member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
  rcases allowed with rejoinEqual | bridgeEqual
  · subst candidate
    exact normalDispatchBridge_scheduler_preempts_assertionRejoin
  · exact (different bridgeEqual).elim

#print axioms normalDispatchBridge_selected_after_predecessor_drain

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSelection
