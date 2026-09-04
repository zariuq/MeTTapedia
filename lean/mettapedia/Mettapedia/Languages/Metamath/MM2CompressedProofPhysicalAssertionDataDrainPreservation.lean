import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation

/-!
# Non-executable data preservation across the assertion drain

The four obsolete compressed-proof probes erase executable shells.  This
module proves once that an exact non-executable symbolic row survives all four
erasures.  Clients can instantiate the result without exposing their payloads
to the physical executor proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionDataDrainPreservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Every exact non-executable symbolic row survives the four physical
predecessor erasures. -/
theorem expression_symbol_row_survives_predecessor_drain
    (space : List Atom) (ready : AssertionPredecessorDrainReady space)
    (rowHead : String) (rowTail : List Atom)
    (rowHeadPositive : 0 < (morkUtf8Bytes rowHead).length)
    (rowHeadBound : (morkUtf8Bytes rowHead).length < 64)
    (nonExecutable : rowHead ≠ "exec")
    (rowMember : .expression (.symbol rowHead :: rowTail) ∈ space) :
    .expression (.symbol rowHead :: rowTail) ∈
      afterLookupAdvanceProbe space := by
  have proofDrains := compressedProofStep_drains_of_no_predecessor_heads space
    ready.noPredecessorHeads
  have proofNoHeads : NoAssertionPredecessorHeads (afterProofProbe space) :=
    atomsWithin_of_eq_morkEraseSupport proofDrains ready.noPredecessorHeads
  have proofMember : .expression (.symbol rowHead :: rowTail) ∈
      afterProofProbe space :=
    mem_of_eq_morkEraseSupport proofDrains rowMember
      (symbolicRow_key_ne_compressedProofStep rowHead rowTail rowHeadPositive
        rowHeadBound nonExecutable)

  have faultDrains := compressedHeapLookupFault_drains_of_no_predecessor_heads
    (afterProofProbe space) proofNoHeads
  have faultNoHeads : NoAssertionPredecessorHeads
      (afterLookupFaultProbe space) :=
    atomsWithin_of_eq_morkEraseSupport faultDrains proofNoHeads
  have faultMember : .expression (.symbol rowHead :: rowTail) ∈
      afterLookupFaultProbe space :=
    mem_of_eq_morkEraseSupport faultDrains proofMember
      (symbolicRow_key_ne_compressedHeapLookupFault rowHead rowTail
        rowHeadPositive rowHeadBound nonExecutable)

  have cursorDrains := decoratedCursorAssertion_drains_of_no_predecessor_heads
    (afterLookupFaultProbe space) faultNoHeads
  have cursorNoHeads : NoAssertionPredecessorHeads
      (afterCursorAssertionProbe space) :=
    atomsWithin_of_eq_morkEraseSupport cursorDrains faultNoHeads
  have cursorMember : .expression (.symbol rowHead :: rowTail) ∈
      afterCursorAssertionProbe space :=
    mem_of_eq_morkEraseSupport cursorDrains faultMember
      (symbolicRow_key_ne_decoratedCursorAssertion rowHead rowTail
        rowHeadPositive rowHeadBound nonExecutable)

  have advanceDrains :=
    compressedHeapLookupAdvance_drains_of_no_predecessor_heads
      (afterCursorAssertionProbe space) cursorNoHeads
  exact mem_of_eq_morkEraseSupport advanceDrains cursorMember
    (symbolicRow_key_ne_compressedHeapLookupAdvance rowHead rowTail
      rowHeadPositive rowHeadBound nonExecutable)

/-- The explicit endpoint relation transports a surviving symbolic row without
unfolding the four nested physical workspaces. -/
theorem expression_symbol_row_survives_physical_predecessor_drain
    (space final : List Atom) (ready : AssertionPredecessorDrainReady space)
    (drain : PhysicalAssertionPredecessorDrain space final)
    (rowHead : String) (rowTail : List Atom)
    (rowHeadPositive : 0 < (morkUtf8Bytes rowHead).length)
    (rowHeadBound : (morkUtf8Bytes rowHead).length < 64)
    (nonExecutable : rowHead ≠ "exec")
    (rowMember : .expression (.symbol rowHead :: rowTail) ∈ space) :
    .expression (.symbol rowHead :: rowTail) ∈ final := by
  rw [drain.finalExact]
  exact expression_symbol_row_survives_predecessor_drain space ready rowHead
    rowTail rowHeadPositive rowHeadBound nonExecutable rowMember

#print axioms expression_symbol_row_survives_predecessor_drain
#print axioms expression_symbol_row_survives_physical_predecessor_drain

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionDataDrainPreservation
