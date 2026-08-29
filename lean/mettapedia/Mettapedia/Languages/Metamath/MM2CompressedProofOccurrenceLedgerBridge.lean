import Mettapedia.Languages.Metamath.MM2CompressedProofHeapSourceBridge
import Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation

/-!
# Displayed occurrence heap over the source compressed machine

This module enriches the source machine's `Nat × Unit` proof heap with the
canonical MM2 node identity, formula, and derivation-generated occurrence.
Forgetting that decoration returns the original source semantic heap exactly.
No caller supplies occurrence rows or a parallel heap.
-/

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef

namespace Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapSourceBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- Assertion schemas remain opaque in the rich heap.  A dangling proof
identity is also retained explicitly, so enrichment preserves every source
heap position even before a reachability invariant rules dangling entries
out. -/
inductive DisplayedHeapOpaque where
  | assertion (value : SourceAssertion)
  | danglingProof (nodeId : Nat)
deriving DecidableEq

/-- Canonical rich occurrence for one source proof node and one occurrence
atom computed by the execution ledger. -/
def displayedProofOccurrence (nodeId : Nat)
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (node : ProofNode source target) (sourceOccurrence : Atom) :
    ProofOccurrence :=
  ⟨(CompressedIndexCode.ofNat nodeId).atom,
    ⟨formulaAtom node.formula, sourceOccurrence⟩⟩

/-- Enrich one source heap entry without changing its position. -/
def displayedHeapEntry
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) :
    SourceGSLTCompressedTheorem.HeapEntry source →
      MM2CompressedProofHeapEncoding.HeapEntry DisplayedHeapOpaque
  | .assertion assertion => .opaque (.assertion assertion)
  | .proof nodeId =>
      match state.nodes[nodeId]?, ledger.occurrences[nodeId]? with
      | some node, some sourceOccurrence =>
          .occurrence
            (displayedProofOccurrence nodeId node sourceOccurrence)
      | _, _ => .opaque (.danglingProof nodeId)

/-- Position-preserving rich view of the complete source heap. -/
def displayedHeap
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) :
    List (MM2CompressedProofHeapEncoding.HeapEntry DisplayedHeapOpaque) :=
  state.heap.map (displayedHeapEntry state ledger)

@[simp] theorem displayedHeap_length
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) :
    (displayedHeap state ledger).length = state.heap.length := by
  simp [displayedHeap]

/-- Forget the rich target decoration.  Canonical compact node identities
decode to their source natural-number identities. -/
def forgetDisplayedHeapEntry? :
    MM2CompressedProofHeapEncoding.HeapEntry DisplayedHeapOpaque →
      Option (Entry Nat Unit SourceAssertion)
  | .occurrence occurrence => do
      let nodeId ←
        CompressedIndexCode.decodeCompressedIndexAtom occurrence.identity
      pure (.occurrence ⟨nodeId, ()⟩)
  | .opaque (.assertion assertion) => some (.opaque assertion)
  | .opaque (.danglingProof nodeId) =>
      some (.occurrence ⟨nodeId, ()⟩)

def forgetDisplayedHeap? :
    List (MM2CompressedProofHeapEncoding.HeapEntry DisplayedHeapOpaque) →
      Option (List (Entry Nat Unit SourceAssertion)) :=
  List.mapM forgetDisplayedHeapEntry?

/-- The displayed entry is a decoration of the exact source entry, including
the otherwise-invalid dangling branch. -/
theorem forget_displayedHeapEntry
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (entry : SourceGSLTCompressedTheorem.HeapEntry source) :
    forgetDisplayedHeapEntry? (displayedHeapEntry state ledger entry) =
      some (sourceHeapEntry entry) := by
  cases entry with
  | assertion assertion => rfl
  | proof nodeId =>
      simp only [displayedHeapEntry]
      split <;>
        simp_all [forgetDisplayedHeapEntry?, displayedProofOccurrence,
          sourceHeapEntry]

/-- The displayed rich heap commutes exactly with the established
`Nat × Unit` semantic projection. -/
theorem forget_displayedHeap
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) :
    forgetDisplayedHeap? (displayedHeap state ledger) =
      some (sourceHeap state.heap) := by
  unfold displayedHeap forgetDisplayedHeap? sourceHeap
  induction state.heap with
  | nil => rfl
  | cons entry entries induction =>
      simp [forget_displayedHeapEntry state ledger entry, induction]

/-- A source proof lookup exposes a unique ledger occurrence at the same node
identity and the same heterogeneous heap position. -/
theorem displayedHeap_get_proof
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node) :
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      GetElem?.getElem? (displayedHeap state ledger) index =
        some (.occurrence
          (displayedProofOccurrence nodeId node sourceOccurrence)) := by
  have nodeBound := (List.getElem?_eq_some_iff.mp nodeLookup).1
  have occurrenceBound : nodeId < ledger.occurrences.length := by
    rw [ledger.aligned]
    exact nodeBound
  let sourceOccurrence := ledger.occurrences[nodeId]'occurrenceBound
  have occurrenceLookup :
      ledger.occurrences[nodeId]? = some sourceOccurrence := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨occurrenceBound, rfl⟩
  refine ⟨sourceOccurrence, occurrenceLookup, ?_⟩
  have mapped :=
    congrArg (Option.map (displayedHeapEntry state ledger)) heapLookup
  simpa [displayedHeap, List.getElem?_map, displayedHeapEntry, nodeLookup,
    occurrenceLookup] using mapped

/-- Canonical semantic request generated by a source machine and its computed
ledger. -/
def displayedProofRequestState
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat) :
    SemanticState DisplayedHeapOpaque :=
  ⟨displayedHeap state ledger, 0,
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request index⟩

/-- Semantic result of a successful displayed-heap lookup.  The heap and
reserve are unchanged; only the generic lookup control records the exact
proof occurrence that was found. -/
def displayedProofHitState
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat)
    (item : ProofOccurrence) : SemanticState DisplayedHeapOpaque :=
  ⟨displayedHeap state ledger, 0,
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.finished index
      (.found index (.occurrence item))⟩

/-- An arbitrary verified source proof constructor generates canonical MM2
heap/node rows for the exact ledger occurrence it reuses. -/
theorem source_proof_constructor_has_canonical_request
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (proofOwner : Atom)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node) :
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      RepresentsProofRequest proofOwner
        (displayedProofRequestState state ledger index)
        (encodedHeapRows proofOwner
          (displayedProofRequestState state ledger index)) := by
  obtain ⟨sourceOccurrence, occurrenceLookup, displayedLookup⟩ :=
    displayedHeap_get_proof state ledger index nodeId node heapLookup nodeLookup
  refine ⟨sourceOccurrence, occurrenceLookup, ?_⟩
  exact semantic_request_has_canonical_representation rfl displayedLookup

/-- An arbitrary verified source proof constructor induces the generic
one-step speculative hit on the displayed heap.  The found occurrence is the
one computed by the derivation ledger, not a caller-supplied witness. -/
theorem source_proof_constructor_realizes_displayed_hit
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node) :
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step
        (displayedProofRequestState state ledger index)
        (displayedProofHitState state ledger index
          (displayedProofOccurrence nodeId node sourceOccurrence)) := by
  obtain ⟨sourceOccurrence, occurrenceLookup, displayedLookup⟩ :=
    displayedHeap_get_proof state ledger index nodeId node heapLookup nodeLookup
  refine ⟨sourceOccurrence, occurrenceLookup, ?_⟩
  exact Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step.hit
    (displayedHeap state ledger) 0 index
      (.occurrence
        (displayedProofOccurrence nodeId node sourceOccurrence))
      displayedLookup

/-- Negative control: an assertion entry remains opaque in the displayed
heap and cannot be reclassified as a proof occurrence. -/
theorem displayedHeap_get_assertion
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (index : Nat) (assertion : SourceAssertion)
    (heapLookup : state.heap[index]? = some (.assertion assertion)) :
    GetElem?.getElem? (displayedHeap state ledger) index =
      some (.opaque (.assertion assertion)) := by
  have mapped :=
    congrArg (Option.map (displayedHeapEntry state ledger)) heapLookup
  simpa [displayedHeap, List.getElem?_map, displayedHeapEntry] using mapped

#print axioms forget_displayedHeapEntry
#print axioms forget_displayedHeap
#print axioms displayedHeap_get_proof
#print axioms source_proof_constructor_has_canonical_request
#print axioms source_proof_constructor_realizes_displayed_hit
#print axioms displayedHeap_get_assertion

end Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
