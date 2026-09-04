import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
import Mettapedia.Languages.ProcessCalculi.MORK.ScheduledFourErasures

/-!
# Executable inventory after the assertion predecessor drain

The four scheduled erasures reduce the source-authorized executable inventory
to the dormant assertion rejoin and the normal-dispatch bridge.  This module
keeps that finite-list calculation opaque to downstream scheduler proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionPostDrainInventory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- Every executable candidate at the four-drain endpoint is one of the two
handoff continuations. -/
theorem postDrain_candidates_within_rejoin_bridge
    (space final : List Atom) (ready : AssertionPredecessorDrainReady space)
    (drain : PhysicalAssertionPredecessorDrain space final) :
    ∀ candidate ∈
      cSupportedSourceExecFacts final,
      candidate ∈ [compressedAssertionRejoinDirective,
        compressedNormalDispatchBridgeDirective] := by
  exact candidatesWithin_pair_after_four_erasures
    (cSupportedSourceExecFacts_nodup_of_space_nodup ready.listNodup)
    ready.candidatesWithin drain.finalCandidates

#print axioms postDrain_candidates_within_rejoin_bridge

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionPostDrainInventory
