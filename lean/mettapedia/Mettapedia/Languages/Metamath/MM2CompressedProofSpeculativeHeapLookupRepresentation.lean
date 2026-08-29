import Mettapedia.GSLT.Core.SpeculativeFiniteHeapLookup
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding

/-!
# Representation relation for speculative compressed-proof heap lookup

This module relates the reusable speculative finite-heap GSLT to the MM2 row
vocabulary used by compressed Metamath proof lookup.  The relation is
parameterized by the opaque heap-cell carrier and does not select a fixture,
scheduler, or execution engine state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding

abbrev SemanticCell (Other : Type) := HeapEntry Other

abbrev SemanticState (Other : Type) :=
  Mettapedia.GSLT.SpeculativeFiniteHeapLookup.State (SemanticCell Other)

/-- Canonical MM2 data view of the semantic heterogeneous heap.  Opaque
entries retain their positions but emit no proof/node rows. -/
def encodedHeapRows {Other : Type} (owner : Atom)
    (state : SemanticState Other) : List Atom :=
  heapProofRows owner state.heap ++ nodeRows owner state.heap

/-- Compact-stack observation of a semantic proof occurrence. -/
def compressedStackRow (owner : Atom) (position : Nat)
    (item : ProofOccurrence) : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", owner,
      (CompressedIndexCode.ofNat position).atom, item.identity]

/-- Normal-stack observation of the same semantic proof occurrence. -/
def normalStackRow (owner : Atom) (position : Nat)
    (item : ProofOccurrence) : Atom :=
  .expression
    [.symbol "mm-stack-cell", owner,
      (CompressedIndexCode.ofNat position).atom,
      item.value.formula, item.value.sourceOccurrence]

/-- The concrete space represents a proof request only when its indexed heap
and node rows encode the exact semantic occurrence at the requested index. -/
def RepresentsProofRequest {Other : Type} (owner : Atom)
    (state : SemanticState Other) (space : List Atom) : Prop :=
  ∃ index item,
    state.control =
        Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request index ∧
      state.heap[index]? = some (.occurrence item) ∧
      heapProofRow owner index item ∈ space ∧
      nodeRow owner item ∈ space

/-- A represented proof hit retains the indexed heap and node evidence and
publishes both stack views of that exact occurrence. -/
def RepresentsProofHit {Other : Type} (owner : Atom)
    (stackPosition : Nat) (state : SemanticState Other)
    (space : List Atom) : Prop :=
  ∃ index item,
    state.control =
        Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.finished index
          (.found index (.occurrence item)) ∧
      state.heap[index]? = some (.occurrence item) ∧
      heapProofRow owner index item ∈ space ∧
      nodeRow owner item ∈ space ∧
      compressedStackRow owner stackPosition item ∈ space ∧
      normalStackRow owner stackPosition item ∈ space

/-- The row encoder constructively establishes the request representation for
every occurrence-valued semantic lookup.  Target data is therefore derived
from the semantic heap rather than supplied as an unrelated packet. -/
theorem semantic_request_has_canonical_representation
    {Other : Type} {owner : Atom} {state : SemanticState Other}
    {index : Nat} {item : ProofOccurrence}
    (control : state.control =
      Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request index)
    (found : state.heap[index]? = some (.occurrence item)) :
    RepresentsProofRequest owner state (encodedHeapRows owner state) := by
  refine ⟨index, item, control, found, ?_, ?_⟩
  · simp only [encodedHeapRows, List.mem_append]
    exact Or.inl (by
      simpa [heapProofRows] using
        heapProofRow_mem_heapProofRowsFrom_of_getElem_occurrence
          owner 0 index state.heap item found)
  · simp only [encodedHeapRows, List.mem_append]
    exact Or.inr
      (nodeRow_mem_nodeRows_of_getElem_occurrence
        owner index state.heap item found)

/-- Request representation is monotone under addition of unrelated concrete
rows. -/
theorem RepresentsProofRequest.mono
    {Other : Type} {owner : Atom} {state : SemanticState Other}
    {smaller larger : List Atom}
    (represented : RepresentsProofRequest owner state smaller)
    (included : ∀ row ∈ smaller, row ∈ larger) :
    RepresentsProofRequest owner state larger := by
  rcases represented with
    ⟨index, item, control, found, heapRow, nodeRow⟩
  exact ⟨index, item, control, found,
    included _ heapRow, included _ nodeRow⟩

/-- Hit representation has the same frame monotonicity. -/
theorem RepresentsProofHit.mono
    {Other : Type} {owner : Atom} {stackPosition : Nat}
    {state : SemanticState Other} {smaller larger : List Atom}
    (represented : RepresentsProofHit owner stackPosition state smaller)
    (included : ∀ row ∈ smaller, row ∈ larger) :
    RepresentsProofHit owner stackPosition state larger := by
  rcases represented with
    ⟨index, item, control, found, heapRow, nodeRow, compactStack,
      normalStack⟩
  exact ⟨index, item, control, found, included _ heapRow,
    included _ nodeRow, included _ compactStack, included _ normalStack⟩

/-- Opaque entries cannot be reclassified as proof occurrences by the
representation relation, even when they occupy the requested index. -/
theorem opaque_entry_is_not_represented_as_proof_request
    {Other : Type} {owner : Atom} {state : SemanticState Other}
    {space : List Atom} {index : Nat} {value : Other}
    (control : state.control =
      Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request index)
    (foundOpaque : state.heap[index]? = some (.opaque value)) :
    ¬ RepresentsProofRequest owner state space := by
  rintro ⟨otherIndex, item, otherControl, foundOccurrence, _heapRow,
    _nodeRow⟩
  have indexEqual : index = otherIndex := by
    simpa using control.symm.trans otherControl
  subst otherIndex
  rw [foundOpaque] at foundOccurrence
  cases foundOccurrence

#print axioms opaque_entry_is_not_represented_as_proof_request
#print axioms semantic_request_has_canonical_representation
#print axioms RepresentsProofRequest.mono
#print axioms RepresentsProofHit.mono

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
