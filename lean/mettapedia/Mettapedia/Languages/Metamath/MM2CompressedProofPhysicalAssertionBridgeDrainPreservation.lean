import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeExactMembership

/-!
# Exact bridge preservation across the physical assertion drain

The compact assertion launcher leaves four obsolete executable probes behind.
They fire inertly in the real least-key MORK schedule.  This module proves that
their four physical erasures preserve the exact normal-dispatch bridge row.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrainPreservation

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeExactMembership
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

/-- The exact bridge representative survives all four inert predecessor probes.
Each step uses the physical-key separation of the bridge from the selected
shell, not nominal inequality alone. -/
theorem normalDispatchBridge_survives_predecessor_drain
    (space : List Atom) (ready : AssertionPredecessorDrainReady space)
    (bridgeMember : compressedNormalDispatchBridgeRule ∈ space) :
    compressedNormalDispatchBridgeRule ∈ afterLookupAdvanceProbe space := by
  have proofDrains := compressedProofStep_drains_of_no_predecessor_heads space
    ready.noPredecessorHeads
  have proofNoHeads : NoAssertionPredecessorHeads (afterProofProbe space) := by
    exact atomsWithin_of_eq_morkEraseSupport proofDrains
      ready.noPredecessorHeads
  have proofMember : compressedNormalDispatchBridgeRule ∈
      afterProofProbe space := by
    exact mem_of_eq_morkEraseSupport proofDrains bridgeMember
      (Ne.symm compressedProofStep_key_ne_normalDispatchBridge)

  have faultDrains := compressedHeapLookupFault_drains_of_no_predecessor_heads
    (afterProofProbe space) proofNoHeads
  have faultNoHeads : NoAssertionPredecessorHeads
      (afterLookupFaultProbe space) := by
    exact atomsWithin_of_eq_morkEraseSupport faultDrains proofNoHeads
  have faultMember : compressedNormalDispatchBridgeRule ∈
      afterLookupFaultProbe space := by
    exact mem_of_eq_morkEraseSupport faultDrains proofMember
      (Ne.symm compressedHeapLookupFault_key_ne_normalDispatchBridge)

  have cursorDrains := decoratedCursorAssertion_drains_of_no_predecessor_heads
    (afterLookupFaultProbe space) faultNoHeads
  have cursorNoHeads : NoAssertionPredecessorHeads
      (afterCursorAssertionProbe space) := by
    exact atomsWithin_of_eq_morkEraseSupport cursorDrains faultNoHeads
  have cursorMember : compressedNormalDispatchBridgeRule ∈
      afterCursorAssertionProbe space := by
    exact mem_of_eq_morkEraseSupport cursorDrains faultMember
      (Ne.symm decoratedCursorAssertion_key_ne_normalDispatchBridge)

  have advanceDrains :=
    compressedHeapLookupAdvance_drains_of_no_predecessor_heads
      (afterCursorAssertionProbe space) cursorNoHeads
  exact mem_of_eq_morkEraseSupport advanceDrains cursorMember
    (Ne.symm compressedHeapLookupAdvance_key_ne_normalDispatchBridge)

/-- The endpoint relation transports exact bridge membership without exposing
the nested implementation of the four intermediate workspaces. -/
theorem normalDispatchBridge_survives_physical_predecessor_drain
    (space final : List Atom) (ready : AssertionPredecessorDrainReady space)
    (drain : PhysicalAssertionPredecessorDrain space final)
    (bridgeMember : compressedNormalDispatchBridgeRule ∈ space) :
    compressedNormalDispatchBridgeRule ∈ final := by
  rw [drain.finalExact]
  exact normalDispatchBridge_survives_predecessor_drain space ready bridgeMember

/-- The scheduled four-step drain and exact bridge preservation hold together,
so the membership result refers to the endpoint of the actual MORK trace. -/
theorem physical_assertion_predecessor_drain_preserves_bridge
    (space : List Atom) (ready : AssertionPredecessorDrainReady space)
    (bridgeMember : compressedNormalDispatchBridgeRule ∈ space) :
    ∃ final, PhysicalAssertionPredecessorDrain space final ∧
      compressedNormalDispatchBridgeRule ∈ final := by
  exact ⟨afterLookupAdvanceProbe space,
    physical_assertion_predecessor_drain space ready,
    normalDispatchBridge_survives_predecessor_drain space ready bridgeMember⟩

#print axioms normalDispatchBridge_survives_physical_predecessor_drain
#print axioms physical_assertion_predecessor_drain_preserves_bridge

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrainPreservation
