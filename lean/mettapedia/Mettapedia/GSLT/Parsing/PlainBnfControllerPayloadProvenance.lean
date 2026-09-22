import Mettapedia.GSLT.Parsing.PlainBnfStructuredEnumeration
import Mettapedia.GSLT.Parsing.PlainBnfStructuredReverseDependencies
import Mettapedia.GSLT.Parsing.PlainBnfRunSourceExecution

/-!
# Full candidate provenance of live controller heap payloads

Every live payload is exactly an encoded candidate, including its rank,
name, expression, and span. The predicate below observes the existing heap
contents; it is not another controller state or an execution interpreter.
Membership provenance does not assert unique pending positions or discard
payload multiplicity. Those are separate worklist invariants.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerPayloadProvenance

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Batteries.PairingHeapImp (Heap)
open PlainBnfSourceRank (Rank value)
open PlainBnfStructuredDenotation (Expression LexicalDeclaration)
open PlainBnfStructuredDiscoveryGraph (Definitions Definition)
open PlainBnfStructuredEnumeration (candidates wireItem wireDefinition)
open PlainBnfReverseIndexSourceExecution (Item key)
open PlainBnfGraphNameTrie (Trie)
open PlainBnfWakeSourceExecution (HeapItem Queues Ordered contents heapItem wake)
open PlainBnfHeapSourceExecution (itemLE)

def FromCandidates (input : List Item) (queues : Queues) : Prop :=
  ∀ payload ∈ contents queues, ∃ item ∈ input, payload = heapItem item

theorem empty (input : List Item) (scheduled : Trie SExpr) :
    FromCandidates input (.nil, .nil, scheduled) := by
  simp [FromCandidates, contents, PlainBnfPairingHeapObservation.contents]

theorem heapItem_injective : Function.Injective heapItem := by
  intro left right same
  exact PlainBnfStructuredEnumeration.wireItem_injective same

theorem live_heapItem_member (input : List Item) (queues : Queues)
    (provenance : FromCandidates input queues) (item : Item)
    (member : heapItem item ∈ contents queues) : item ∈ input := by
  obtain ⟨original, present, same⟩ := provenance _ member
  exact heapItem_injective same ▸ present

theorem wake_preserves (input work : List Item) (ready : Expression → Bool)
    (origin : Option Rank) (queues : Queues) (ordered : Ordered queues)
    (provenance : FromCandidates input queues) (workInside : work ⊆ input) :
    FromCandidates input (wake ready origin work queues) := by
  intro payload member
  rw [PlainBnfWakeSourceExecution.wake_contents ready origin work queues ordered] at member
  rcases Multiset.mem_add.mp member with selected | previous
  · obtain ⟨item, chosen, same⟩ := List.mem_map.mp (Multiset.mem_coe.mp selected)
    exact ⟨item, workInside ((PlainBnfWakeSourceExecution.selected_sublist ready work queues.2.2).subset chosen),
      same.symm⟩
  · exact provenance payload previous

theorem initialQueues (productive : Bool) (input : List Item) (lexicals : List LexicalDeclaration) :
    FromCandidates input (PlainBnfRunSourceExecution.initialQueues productive input lexicals) :=
  wake_preserves input input _ none _ ⟨.nil, .nil⟩ (empty input .empty) (List.Subset.refl _)

/-- Combining a forest retains its complete contents, including siblings. -/
theorem combine_preserves (input : List Item) (forest following : Heap HeapItem) (scheduled : Trie SExpr)
    (provenance : FromCandidates input (forest, following, scheduled)) :
    FromCandidates input (forest.combine itemLE, following, scheduled) := by
  intro payload member
  apply provenance payload
  simpa only [contents, PlainBnfPairingHeapObservation.contents_combine] using member

theorem pop_preserves (input : List Item) (current rest following : Heap HeapItem)
    (scheduled : Trie SExpr) (item : HeapItem) (single : current.NoSibling)
    (returned : current.deleteMin itemLE = some (item, rest))
    (provenance : FromCandidates input (current, following, scheduled)) :
    FromCandidates input (rest, following, scheduled) := by
  intro payload member
  apply provenance payload
  have removed := PlainBnfPairingHeapObservation.contents_deleteMin itemLE single returned
  simp only [contents, removed, Multiset.cons_add, Multiset.mem_cons]
  exact Or.inr member

theorem popped_candidate (input : List Item) (current rest following : Heap HeapItem)
    (scheduled : Trie SExpr) (item : HeapItem) (single : current.NoSibling)
    (returned : current.deleteMin itemLE = some (item, rest))
    (provenance : FromCandidates input (current, following, scheduled)) :
    ∃ original ∈ input, item = heapItem original := by
  apply provenance item
  simp only [contents, PlainBnfPairingHeapObservation.contents_deleteMin itemLE single returned,
    Multiset.cons_add, Multiset.mem_cons, true_or]

theorem rollover_preserves (input : List Item) (following : Heap HeapItem) (scheduled : Trie SExpr)
    (provenance : FromCandidates input (.nil, following, scheduled)) :
    FromCandidates input (following, .nil, scheduled) := by
  simpa only [FromCandidates, contents, PlainBnfPairingHeapObservation.contents,
    zero_add, add_zero] using provenance

/-- Publication wakes the exact source bucket. Each repeated reference
still supplies a candidate occurrence; no bucket is silently normalized. -/
theorem publishedQueues (productive : Bool) (input : List Item) (item : Item)
    (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap HeapItem) (scheduled : Trie SExpr)
    (ordered : Ordered (.node (heapItem item) children .nil, following, scheduled))
    (provenance : FromCandidates input (.node (heapItem item) children .nil, following, scheduled)) :
    FromCandidates input (PlainBnfRunSourceExecution.publishedQueues productive item
      (PlainBnfStructuredReverseDependencies.bucket input item.2.name lexicals)
      history lexicals children following scheduled) := by
  unfold PlainBnfRunSourceExecution.publishedQueues
  have returned : (Heap.node (heapItem item) children .nil).deleteMin itemLE =
      some (heapItem item, children.combine itemLE) := rfl
  apply wake_preserves input _ _ (some item.1) (children.combine itemLE, following, scheduled)
    ⟨ordered.1.deleteMin returned, ordered.2⟩
    (pop_preserves input (.node (heapItem item) children .nil) (children.combine itemLE)
      following scheduled (heapItem item) (.node _ _) returned provenance)
  intro dependent member
  exact (PlainBnfStructuredReverseDependencies.mem_bucket input item.2.name lexicals dependent).mp member |>.1

/-- Source-coordinate existence and the entire encoded payload follow from
membership in the actual enumerated candidate image. -/
theorem live_candidate_position (definitions : Definitions) (queues : Queues)
    (provenance : FromCandidates (candidates definitions) queues) (payload : HeapItem)
    (member : payload ∈ contents queues) :
    ∃ position : Fin definitions.length, value payload.1 = position.val ∧
      payload.2 = wireDefinition (definitions.get position) := by
  obtain ⟨item, present, rfl⟩ := provenance payload member
  obtain ⟨position, rankPosition, definition⟩ :=
    PlainBnfStructuredEnumeration.candidate_position definitions item present
  exact ⟨position, rankPosition, congrArg wireDefinition definition⟩

theorem live_rank_coordinate (definitions : Definitions) (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1)
    (queues : Queues) (provenance : FromCandidates (candidates definitions) queues)
    (payload : HeapItem) (member : payload ∈ contents queues) :
    (coordinate payload).val = value payload.1 := by
  obtain ⟨item, present, rfl⟩ := provenance payload member
  exact liveRanks item present

theorem live_payload_at_coordinate (definitions : Definitions) (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1)
    (queues : Queues) (provenance : FromCandidates (candidates definitions) queues)
    (payload : HeapItem) (member : payload ∈ contents queues) :
    payload.2 = wireDefinition (definitions.get (coordinate payload)) := by
  obtain ⟨item, present, rfl⟩ := provenance payload member
  exact congrArg wireDefinition
    (PlainBnfStructuredEnumeration.coordinate_payload definitions coordinate liveRanks item present).symm

/-- The rank comparator orders the same live source coordinates; it need
not interpret unrelated or malformed heap values. -/
theorem live_order (definitions : Definitions) (coordinate : HeapItem → Fin definitions.length)
    (liveRanks : ∀ item ∈ candidates definitions, (coordinate (heapItem item)).val = value item.1)
    (queues : Queues) (provenance : FromCandidates (candidates definitions) queues)
    (left right : HeapItem) (leftMember : left ∈ contents queues) (rightMember : right ∈ contents queues)
    (before : itemLE left right = true) : coordinate left ≤ coordinate right := by
  have ordered := (PlainBnfSourceRank.rankLE_iff left.1 right.1).mp before
  change (coordinate left).val ≤ (coordinate right).val
  rwa [live_rank_coordinate definitions coordinate liveRanks queues provenance left leftMember,
    live_rank_coordinate definitions coordinate liveRanks queues provenance right rightMember]

theorem singleton_iff (input : List Item) (item : Item) (scheduled : Trie SExpr) :
    FromCandidates input (.node (heapItem item) .nil .nil, .nil, scheduled) ↔ item ∈ input := by
  constructor
  · intro provenance
    apply live_heapItem_member input _ provenance item
    simp [contents, PlainBnfPairingHeapObservation.contents]
  · intro present payload member
    have same : payload = heapItem item := by
      simpa [contents, PlainBnfPairingHeapObservation.contents] using member
    exact ⟨item, present, same⟩

private def original : Definition := ⟨"s", ⟨[], ⟨0, 1⟩⟩, ⟨0, 1⟩⟩
private def changedSpan : Definition := ⟨"s", ⟨[], ⟨0, 1⟩⟩, ⟨0, 2⟩⟩

theorem actual_candidate_positive :
    FromCandidates (candidates [original])
      (.node (heapItem (.zero, original)) .nil .nil, .nil, .empty) := by
  rw [singleton_iff]
  simp [candidates, List.zipIdx_cons]

/-- Same rank, name, and expression do not authorize a changed source span. -/
theorem forged_span_negative :
    (heapItem (.zero, original)).1 = (heapItem (.zero, changedSpan)).1 ∧
    (heapItem (.zero, original)).2.name = (heapItem (.zero, changedSpan)).2.name ∧
    (heapItem (.zero, original)).2.expression = (heapItem (.zero, changedSpan)).2.expression ∧
    ¬ FromCandidates (candidates [original])
      (.node (heapItem (.zero, changedSpan)) .nil .nil, .nil, .empty) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [singleton_iff]
  intro member
  have same : changedSpan = original := by
    simpa [candidates, List.zipIdx_cons] using member
  have locations := congrArg (fun definition : Definition => definition.span.stop) same
  cases locations

#print axioms wake_preserves
#print axioms pop_preserves
#print axioms publishedQueues
#print axioms live_candidate_position
#print axioms live_payload_at_coordinate
#print axioms forged_span_negative

end Mettapedia.GSLT.Parsing.PlainBnfControllerPayloadProvenance
