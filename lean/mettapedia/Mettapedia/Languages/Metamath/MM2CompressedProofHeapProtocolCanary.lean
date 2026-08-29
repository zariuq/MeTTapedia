import Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
import Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
import Mettapedia.GSLT.Core.FiniteHeapLookupRealization

/-!
# Semantic A/Z heap canary

This canary connects the reusable occurrence-heap GSLT to the exact atoms used
by the bounded compressed-proof fixture.  It does not normalize the combined
MM2 program; concrete lookup and save directives are qualified separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapProtocolCanary

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedIndexSpine

def canaryProofOccurrence : ProofOccurrence :=
  ⟨canaryNode, ⟨canaryFormula, canaryOccurrence⟩⟩

def canarySemanticHeap : List (HeapEntry Unit) :=
  [.occurrence canaryProofOccurrence]

/-- An assertion-like opaque entry occupies heap position zero; the proof
occurrence therefore remains at position one. -/
def canaryMixedHeap : List (HeapEntry Atom) :=
  [.opaque (.symbol "compressed-canary-assertion-entry"),
    .occurrence canaryProofOccurrence]

def canarySemanticPath :=
  lookupThenSaveProofPath canaryProof canarySemanticHeap 0
    canaryProofOccurrence rfl

def canaryMixedSemanticPath :=
  lookupThenSaveProofPath canaryProof canaryMixedHeap 1
    canaryProofOccurrence rfl

/-- The same semantic lookup lowers through the reusable finite cursor GSLT.
Its terminal observation retains heap position zero and the exact proof-node
occurrence used by the MM2 row encoding below. -/
theorem canaryFiniteLookupPath :
    Nonempty
      (Mettapedia.GSLT.IndexedOperational.ExecutionPath
        (Mettapedia.GSLT.FiniteOccurrenceLookup.gslt Nat
          (Entry Atom ProofNodeValue Unit))
        (Mettapedia.GSLT.FiniteHeapLookupRealization.scanState
          ⟨canarySemanticHeap,
            Mettapedia.GSLT.FiniteHeapLookupRealization.Control.lookup 0⟩)
        (Mettapedia.GSLT.FiniteHeapLookupRealization.scanState
          ⟨canarySemanticHeap,
            Mettapedia.GSLT.FiniteHeapLookupRealization.Control.foundOccurrence
              0 canaryProofOccurrence⟩)) :=
  Mettapedia.GSLT.FiniteHeapLookupRealization.scan_step_has_path
    (Mettapedia.GSLT.FiniteHeapLookupRealization.Step.occurrence
      canarySemanticHeap 0 canaryProofOccurrence rfl)

theorem canary_finite_lookup_observation_exact :
    Mettapedia.GSLT.FiniteOccurrenceLookup.lookup 0
        (Mettapedia.GSLT.FiniteHeapLookupRealization.indexedHeap
          canarySemanticHeap) =
      .found 0 (.occurrence canaryProofOccurrence) := by
  decide

/-- The mixed semantic heap reaches its proof occurrence at position one
through the exact compact successor edge supplied to the MM2 heap walker. -/
theorem canary_mixed_lookup_uses_exact_target_successor :
    compressedIndexSuccessorRow (compressedHeapOwner canaryProof)
        (CompressedIndexCode.ofNat 0).atom
        (CompressedIndexCode.ofNat 1).atom ∈
      compressedIndexSuccessorRows (compressedHeapOwner canaryProof)
        canaryMixedHeap.length := by
  exact compressedIndexSuccessorRow_mem _ canaryMixedHeap.length 0 (by decide)

/-- Negative control: the exact live mixed-heap spine does not invent a
successor beyond its two source occurrences. -/
theorem canary_mixed_lookup_has_no_frontier_successor :
    compressedIndexSuccessorRow (compressedHeapOwner canaryProof)
        (CompressedIndexCode.ofNat canaryMixedHeap.length).atom
        (CompressedIndexCode.ofNat (canaryMixedHeap.length + 1)).atom ∉
      compressedIndexSuccessorRows (compressedHeapOwner canaryProof)
        canaryMixedHeap.length := by
  exact compressedIndexFrontier_has_no_successor _ canaryMixedHeap.length

/-- The semantic `A` lookup followed by `Z` save is a three-transition path
whose final heap contains the same occurrence at positions zero and one. -/
theorem canary_semantic_AZ_exact :
    canarySemanticPath.length = 3 ∧
      canarySemanticHeap ++ [.occurrence canaryProofOccurrence] =
        [.occurrence canaryProofOccurrence,
          .occurrence canaryProofOccurrence] := by
  constructor <;> rfl

/-- The initial compact heap row is exactly the representation of semantic
heap position zero. -/
theorem canary_heap_zero_is_encoded_occurrence :
    heapProofRow canaryProof 0 canaryProofOccurrence = canaryHeapZero := by
  rfl

/-- Saving reuses the same node identity at the fresh heap position. -/
theorem canary_saved_heap_one_is_encoded_occurrence :
    heapProofRow canaryProof 1 canaryProofOccurrence =
      canarySavedHeapOne := by
  rfl

def canarySaveReceiptOne : Atom :=
  .expression
    [.symbol "mm-compressed-save-receipt", canaryProof,
      compressedIndexCodeAtom [] 1, canaryNode, canaryOccurrence]

theorem canary_save_receipt_is_encoded_occurrence :
    saveReceiptRow canaryProof 1 canaryProofOccurrence =
      canarySaveReceiptOne := by
  rfl

/-- Negative control: changing only the source occurrence changes the receipt
even when node formula and heap position stay fixed. -/
theorem canary_changed_source_occurrence_changes_receipt :
    let changed : ProofOccurrence :=
      ⟨canaryNode,
        ⟨canaryFormula, .symbol "compressed-canary-occurrence-other"⟩⟩
    saveReceiptRow canaryProof 1 changed ≠ canarySaveReceiptOne := by
  simp [saveReceiptRow, canarySaveReceiptOne, canaryProof,
    canaryNode, canaryOccurrence]

/-- Opaque entries retain their heap positions while the MM2 proof-row view
emits only the proof occurrence at its true heterogeneous index. -/
theorem canary_mixed_heap_preserves_proof_index :
    heapProofRows canaryProof canaryMixedHeap =
        [heapProofRow canaryProof 1 canaryProofOccurrence] ∧
      nodeRows canaryProof canaryMixedHeap =
        [nodeRow canaryProof canaryProofOccurrence] ∧
      canaryMixedSemanticPath.length = 3 := by
  decide

/-- Negative control: the opaque entry at position zero cannot be interpreted
as a proof occurrence. -/
theorem canary_opaque_entry_cannot_be_read_as_proof :
    ¬ ∃ item, Step
      ⟨canaryProof, canaryMixedHeap, .lookup canaryProof 0⟩
      ⟨canaryProof, canaryMixedHeap, .holding canaryProof 0 item⟩ := by
  exact opaque_lookup_cannot_hit canaryProof canaryMixedHeap 0
    (.symbol "compressed-canary-assertion-entry") rfl

#print axioms canary_semantic_AZ_exact
#print axioms canaryFiniteLookupPath
#print axioms canary_finite_lookup_observation_exact
#print axioms canary_mixed_lookup_uses_exact_target_successor
#print axioms canary_mixed_lookup_has_no_frontier_successor
#print axioms canary_heap_zero_is_encoded_occurrence
#print axioms canary_saved_heap_one_is_encoded_occurrence
#print axioms canary_save_receipt_is_encoded_occurrence
#print axioms canary_changed_source_occurrence_changes_receipt
#print axioms canary_mixed_heap_preserves_proof_index
#print axioms canary_opaque_entry_cannot_be_read_as_proof

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapProtocolCanary
