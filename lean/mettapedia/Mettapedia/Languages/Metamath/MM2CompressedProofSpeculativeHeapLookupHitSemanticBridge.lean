import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

/-!
# Semantic/concrete bridge for one generated speculative proof hit

This module closes the first bounded commuting instance between the reusable
speculative finite-heap GSLT and the generated reflective MM2 proof-cell
handler.  The representation relations are general in the semantic state and
concrete space; the final theorem instantiates them at the smallest complete
direct-hit execution.  It is not yet an arbitrary-heap realization theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSemanticBridge

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitDirectCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInstantiationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitResultCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

def semanticOccurrence : ProofOccurrence :=
  ⟨nodeOne, ⟨formula, occurrence⟩⟩

def semanticHeap : List (SemanticCell Unit) :=
  [.opaque (), .occurrence semanticOccurrence]

def semanticBefore : SemanticState Unit :=
  ⟨semanticHeap, 0,
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request 1⟩

def semanticAfter : SemanticState Unit :=
  ⟨semanticHeap, 0,
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.finished 1
      (.found 1 (.occurrence semanticOccurrence))⟩

@[simp] theorem semantic_heap_row_exact :
    heapProofRow proofOwner 1 semanticOccurrence = heapOne := by
  rfl

@[simp] theorem semantic_node_row_exact :
    nodeRow proofOwner semanticOccurrence = nodeOneRow := by
  rfl

@[simp] theorem semantic_compact_stack_row_exact :
    compressedStackRow proofOwner 0 semanticOccurrence = resolvedStackCell := by
  rfl

@[simp] theorem semantic_normal_stack_row_exact :
    normalStackRow proofOwner 0 semanticOccurrence = directNormalStackCell := by
  rfl

theorem semantic_direct_hit :
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step
      semanticBefore semanticAfter := by
  exact Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step.hit
    semanticHeap 0 1 (.occurrence semanticOccurrence) (by
      simp [semanticHeap])

@[simp] theorem semantic_encoded_heap_rows_exact :
    encodedHeapRows proofOwner semanticBefore = [heapOne, nodeOneRow] := by
  rfl

private theorem member_before_direct_of_slice {candidate : Atom}
    (sliceMember : candidate ∈ directHitInputSlice)
    (notDirective : candidate ≠ speculativeDirectProofDirective.atom) :
    candidate ∈ speculativeHitAfterTerminal := by
  have readMember := direct_hit_slice_in_full_read candidate sliceMember
  simp only [List.mem_cons] at readMember
  rcases readMember with equal | erased
  · exact False.elim (notDirective equal)
  · exact List.mem_of_mem_erase erased

private theorem member_in_direct_read_erase_of_slice {candidate : Atom}
    (sliceMember : candidate ∈ directHitInputSlice)
    (notDirective : candidate ≠ speculativeDirectProofDirective.atom) :
    candidate ∈
      speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom := by
  have readMember := direct_hit_slice_in_full_read candidate sliceMember
  simp only [List.mem_cons] at readMember
  rcases readMember with equal | erased
  · exact False.elim (notDirective equal)
  · exact erased

theorem semantic_before_is_represented :
    RepresentsProofRequest proofOwner semanticBefore
      speculativeHitAfterTerminal := by
  apply RepresentsProofRequest.mono
    (semantic_request_has_canonical_representation
      (owner := proofOwner) (state := semanticBefore) (index := 1)
      (item := semanticOccurrence) rfl (by simp [semanticBefore, semanticHeap]))
  intro row member
  rw [semantic_encoded_heap_rows_exact] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact member_before_direct_of_slice (by
      simp [directHitInputSlice]) (by decide)
  · exact member_before_direct_of_slice (by
      simp [directHitInputSlice]) (by decide)

private theorem directProofSinks_preserve_expression_head
    (candidateHead : String) (candidateTail : List Atom)
    (notPending : "mm-compressed-step-pending" ≠ candidateHead)
    (notLookup : "mm-compressed-heap-lookup" ≠ candidateHead)
    (notMachine : "mm-compressed-machine" ≠ candidateHead) :
    ∀ sink ∈ directProofSinks,
      (∃ authored, sink = .add authored) ∨
        ∃ authored, sink = .remove authored ∧
          ∀ substitution ∈ directHitFullRows,
            instantiateTemplateAtom? substitution authored ≠
              some (.expression (.symbol candidateHead :: candidateTail)) := by
  intro sink member
  simp only [directProofSinks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨directPendingTemplate, rfl, fun substitution _ => by
      unfold directPendingTemplate
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      exact notPending⟩
  · exact Or.inr ⟨directLookupTemplate, rfl, fun substitution _ => by
      unfold directLookupTemplate
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      exact notLookup⟩
  · exact Or.inr ⟨directMachineTemplate, rfl, fun substitution _ => by
      unfold directMachineTemplate
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      exact notMachine⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

theorem direct_hit_retains_semantic_heap_row :
    heapOne ∈ speculativeHitAfterDirect := by
  have present : heapOne ∈
      speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom :=
    member_in_direct_read_erase_of_slice (by
      simp [directHitInputSlice]) (by decide)
  unfold speculativeHitAfterDirect cFireReflectiveSourceExecFact
    cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  exact mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
    directHitFullRows
      (directProofSinks_preserve_expression_head
        "mm-compressed-heap-proof" [proofOwner, code 1, nodeOne]
        (by decide) (by decide) (by decide)) present

theorem direct_hit_retains_semantic_node_row :
    nodeOneRow ∈ speculativeHitAfterDirect := by
  have present : nodeOneRow ∈
      speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom :=
    member_in_direct_read_erase_of_slice (by
      simp [directHitInputSlice]) (by decide)
  unfold speculativeHitAfterDirect cFireReflectiveSourceExecFact
    cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  exact mem_cApplyReflectiveSinkBatch_of_add_or_nonremoving_remove
    directHitFullRows
      (directProofSinks_preserve_expression_head
        "mm-compressed-node" [proofOwner, nodeOne, formula, occurrence]
        (by decide) (by decide) (by decide)) present

theorem semantic_after_is_represented :
    RepresentsProofHit proofOwner 0 semanticAfter
      speculativeHitAfterDirect := by
  refine ⟨1, semanticOccurrence, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [semanticAfter, semanticHeap]
  · simpa using direct_hit_retains_semantic_heap_row
  · simpa using direct_hit_retains_semantic_node_row
  · simpa using speculative_hit_pushes_exact_node
  · have frame := speculative_hit_has_exact_observable_frame
    simpa using frame.2.1

/-- The concrete request frame includes the semantic occurrence relation and
the three live control rows consumed by the generated direct handler. -/
def DirectProofRequestFrame (state : SemanticState Unit)
    (space : List Atom) : Prop :=
  RepresentsProofRequest proofOwner state space ∧
    directStepPending ∈ space ∧
    directLookupOne ∈ space ∧
    machineWithTwoHeapEntries ∈ space

theorem complete_direct_request_frame :
    DirectProofRequestFrame semanticBefore speculativeHitAfterTerminal := by
  refine ⟨semantic_before_is_represented, ?_, ?_, ?_⟩
  · exact member_before_direct_of_slice (by
      simp [directHitInputSlice]) (by decide)
  · exact member_before_direct_of_slice (by
      simp [directHitInputSlice]) (by decide)
  · exact member_before_direct_of_slice (by
      simp [directHitInputSlice]) (by decide)

/-- First bounded commuting instance.  The semantic hit and concrete
scheduled transition start from related states and finish in related states;
the concrete frame additionally records exact consumption and continuation. -/
structure DirectProofHitCommutingInstance : Prop where
  semanticStep :
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step
      semanticBefore semanticAfter
  concreteStep :
    cReflectiveSourceWorkQueueStep .leaveInert speculativeHitAfterTerminal =
      some speculativeHitAfterDirect
  inputRepresentation :
    DirectProofRequestFrame semanticBefore speculativeHitAfterTerminal
  outputRepresentation :
    RepresentsProofHit proofOwner 0 semanticAfter speculativeHitAfterDirect
  exactConcreteFrame :
    DirectProofHitFrame speculativeHitAfterDirect

theorem generated_direct_proof_hit_commutes :
    DirectProofHitCommutingInstance where
  semanticStep := semantic_direct_hit
  concreteStep := speculative_hit_direct_selected
  inputRepresentation := complete_direct_request_frame
  outputRepresentation := semantic_after_is_represented
  exactConcreteFrame := speculative_hit_has_exact_observable_frame

/-- Negative control: an opaque heap entry at the requested position cannot
satisfy the proof-request representation relation. -/
def semanticOpaqueRequest : SemanticState Unit :=
  ⟨[.opaque (), .opaque ()], 0,
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request 1⟩

theorem opaque_heap_entry_is_not_a_proof_request (space : List Atom) :
    ¬ RepresentsProofRequest proofOwner semanticOpaqueRequest space := by
  exact opaque_entry_is_not_represented_as_proof_request
    (state := semanticOpaqueRequest) (index := 1) (value := ())
      (by rfl) (by simp [semanticOpaqueRequest])

#print axioms semantic_direct_hit
#print axioms semantic_encoded_heap_rows_exact
#print axioms semantic_before_is_represented
#print axioms direct_hit_retains_semantic_heap_row
#print axioms direct_hit_retains_semantic_node_row
#print axioms semantic_after_is_represented
#print axioms complete_direct_request_frame
#print axioms generated_direct_proof_hit_commutes
#print axioms opaque_heap_entry_is_not_a_proof_request

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSemanticBridge
