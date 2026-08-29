import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSemanticBridge
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitTerminalCanary

/-!
# Inhabited control for the symbolic speculative proof-hit frame

The symbolic frame is instantiated by the existing generated post-terminal
space.  This receipt is deliberately separate from the general theorem: it
shows that the scheduler, matcher, semantic request, and representation
premises hold simultaneously in one actual assembled MM2 state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrameCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInstantiationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSemanticBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitTerminalCanary
open Mettapedia.Languages.Metamath.MM2DataEncoding

/-- Concrete parameters extracted from the generated direct-hit fixture. -/
def canaryDirectProofContext : DirectProofContext where
  scopeOwner := scopeOwner
  proofOwner := MM2CompressedProofHeapLookupCanary.proofOwner
  wordPosition := natAtom 0
  remainingBytes := listAtom natAtom []
  index := 1
  cursor := 0
  heapNext := 2
  nodeNext := 2
  stackPosition := 0
  nextStackPosition := 1

@[simp] theorem canary_semantic_hit_after_exact :
    semanticHitAfter canaryDirectProofContext semanticOccurrence semanticBefore =
      semanticAfter := by
  rfl

theorem canary_heap_row_in_live :
    heapProofRow canaryDirectProofContext.proofOwner
        canaryDirectProofContext.index semanticOccurrence ∈
      directProofLive speculativeHitAfterTerminal := by
  have member := direct_hit_slice_in_full_read heapOne (by
    simp [directHitInputSlice])
  simp only [List.mem_cons] at member
  rcases member with equal | member
  · exact False.elim ((by decide :
      heapOne ≠ speculativeDirectProofDirective.atom) equal)
  · simpa [canaryDirectProofContext, directProofLive] using member

theorem canary_node_row_in_live :
    MM2CompressedProofHeapEncoding.nodeRow
        canaryDirectProofContext.proofOwner semanticOccurrence ∈
      directProofLive speculativeHitAfterTerminal := by
  have member := direct_hit_slice_in_full_read nodeOneRow (by
    simp [directHitInputSlice])
  simp only [List.mem_cons] at member
  rcases member with equal | member
  · exact False.elim ((by decide :
      nodeOneRow ≠ speculativeDirectProofDirective.atom) equal)
  · simpa [canaryDirectProofContext, directProofLive] using member

theorem canary_exact_direct_proof_match :
    ExactDirectProofMatch canaryDirectProofContext semanticOccurrence
      speculativeHitAfterTerminal := by
  simpa [ExactDirectProofMatch, directProofMatcherRows, directProofLive,
    directHitFullRows, canaryDirectProofContext,
    DirectProofContext.pendingRow, DirectProofContext.lookupRow,
    DirectProofContext.machineRow, DirectProofContext.nextMachineRow,
    DirectProofContext.resumedScanRow, directStepPending, directLookupOne,
    machineWithTwoHeapEntries, directNextMachine, directResumedScan,
    code] using direct_hit_full_instantiates_frame

theorem canary_direct_proof_request_frame :
    DirectProofRequestFrame canaryDirectProofContext semanticOccurrence
      semanticBefore speculativeHitAfterTerminal where
  control := rfl
  found := by simp [canaryDirectProofContext, semanticBefore, semanticHeap]
  heapRow := canary_heap_row_in_live
  nodeRow := canary_node_row_in_live
  supported := speculative_hit_after_terminal_supported_exact
  exactMatch := canary_exact_direct_proof_match

/-- The repaired symbolic theorem has a real generated inhabitant. -/
theorem generated_hit_inhabits_symbolic_commuting_square :
    DirectProofHitCommutingSquare canaryDirectProofContext semanticOccurrence
      semanticBefore speculativeHitAfterTerminal :=
  direct_proof_hit_commutes_of_exact_frame canaryDirectProofContext
    semanticOccurrence semanticBefore speculativeHitAfterTerminal
    canary_direct_proof_request_frame

#print axioms canary_semantic_hit_after_exact
#print axioms canary_heap_row_in_live
#print axioms canary_node_row_in_live
#print axioms canary_exact_direct_proof_match
#print axioms canary_direct_proof_request_frame
#print axioms generated_hit_inhabits_symbolic_commuting_square

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrameCanary
