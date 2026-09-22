import Mettapedia.GSLT.Parsing.PlainBnfRunSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfWakeFrontierExactness

/-!
# Queue invariants through actual publication's pop and Wake operations

The state remains the existing current/following heaps and scheduled trie.
Popping removes precisely one complete heap payload; the finite-position
erasure requires unique positions. The published position keeps its persistent
mark. Wake then preserves ordering, cursor placement, uniqueness, and exact
mark provenance under the stated live rank/name coordinate assumptions.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerQueuePreservation

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Batteries.PairingHeapImp (Heap)
open PlainBnfSourceRank (Rank value rankLE_iff rankLE_trans)
open PlainBnfGraphNameTrie (Trie)
open PlainBnfReverseIndexSourceExecution (Item key)
open PlainBnfHeapSourceExecution (itemLE)
open PlainBnfWakeSourceExecution
open PlainBnfTwoHeapWorklist (UniquePositions positions Partitioned)
open PlainBnfWakeFrontierExactness (ExactMarks)
open PlainBnfWakeContextualExecution (NameIndex)

variable {size : Nat}

/-- This equality keeps bodies, spans, and repeated payload occurrences. -/
theorem pop_contents (item : HeapItem) (children following : Heap HeapItem) (scheduled : NameIndex) :
    contents (.node item children .nil, following, scheduled) =
      item ::ₘ contents (children.combine itemLE, following, scheduled) := by
  simp [contents, PlainBnfPairingHeapObservation.contents,
    PlainBnfPairingHeapObservation.contents_combine, Multiset.cons_add]

theorem popped_position_present (coordinate : HeapItem → Fin size)
    (item : HeapItem) (children following : Heap HeapItem) (scheduled : NameIndex) :
    coordinate item ∈ pending coordinate (.node item children .nil, following, scheduled) := by
  rw [pending_from_contents, pop_contents]
  simp

/-- A set erasure is licensed by occurrence uniqueness, not by heap order. -/
theorem pop_pending_unique (coordinate : HeapItem → Fin size)
    (item : HeapItem) (children following : Heap HeapItem) (scheduled : NameIndex)
    (unique : UniquePositions coordinate (.node item children .nil) following) :
    pending coordinate (children.combine itemLE, following, scheduled) =
      (pending coordinate (.node item children .nil, following, scheduled)).erase (coordinate item) ∧
    coordinate item ∉ pending coordinate (children.combine itemLE, following, scheduled) ∧
    UniquePositions coordinate (children.combine itemLE) following := by
  have whole : ((contents (.node item children .nil, following, scheduled)).map coordinate).Nodup := by
    simpa only [UniquePositions, contents, Multiset.map_add] using unique
  rw [pop_contents, Multiset.map_cons, Multiset.nodup_cons] at whole
  have absent : coordinate item ∉ pending coordinate (children.combine itemLE, following, scheduled) := by
    simpa only [pending_from_contents, Multiset.mem_toFinset] using whole.1
  refine ⟨?_, absent, ?_⟩
  · rw [pending_from_contents coordinate (.node item children .nil, following, scheduled),
      pop_contents, Multiset.map_cons, Multiset.toFinset_cons,
      ← pending_from_contents coordinate (children.combine itemLE, following, scheduled)]
    simp [absent]
  · simpa only [UniquePositions, contents, Multiset.map_add] using whole.2

theorem pop_ordered (item : HeapItem) (children following : Heap HeapItem) (scheduled : NameIndex)
    (ordered : Ordered (.node item children .nil, following, scheduled)) :
    Ordered (children.combine itemLE, following, scheduled) :=
  ⟨ordered.1.deleteMin (by rfl), ordered.2⟩

/-- The minimum law and live rank agreement exclude skipped current-round
positions. The cursor moves past the published rank, not merely past the old
cursor, and uniqueness excludes another item at that same position. -/
theorem pop_wellPlaced (coordinate : HeapItem → Fin size) (origin : Option Rank)
    (item : HeapItem) (children following : Heap HeapItem) (scheduled : NameIndex)
    (ordered : Ordered (.node item children .nil, following, scheduled))
    (placed : WellPlaced coordinate origin (.node item children .nil, following, scheduled))
    (unique : UniquePositions coordinate (.node item children .nil) following)
    (liveRanks : ∀ payload ∈ PlainBnfPairingHeapObservation.contents (.node item children .nil),
      value payload.1 = (coordinate payload).val) :
    WellPlaced coordinate (some item.1) (children.combine itemLE, following, scheduled) := by
  have coordinateOrder : ∀ first ∈ PlainBnfPairingHeapObservation.contents (.node item children .nil),
      ∀ second ∈ PlainBnfPairingHeapObservation.contents (.node item children .nil),
      itemLE first second = true → coordinate first ≤ coordinate second := by
    intro first firstMember second secondMember comparison
    have ranks := (rankLE_iff first.1 second.1).mp comparison
    simpa only [liveRanks first firstMember, liveRanks second secondMember, Fin.le_def] using ranks
  have checked := PlainBnfTwoHeapWorklist.pop_current_partition coordinate itemLE
    (fun first second => rankLE_trans first second) ordered.1 coordinateOrder
    (PlainBnfTwoHeapWorklist.unique_current coordinate unique)
    (show (Heap.node item children Heap.nil).deleteMin itemLE = some (item, children.combine itemLE) from rfl)
    (pending coordinate (.node item children .nil, following, scheduled))
    (PlainBnfScheduleWorklistBridge.cursor origin) placed
  have ownRank := liveRanks item (by simp [PlainBnfPairingHeapObservation.contents])
  unfold WellPlaced
  rw [(pop_pending_unique coordinate item children following scheduled unique).1]
  simpa only [PlainBnfScheduleWorklistBridge.cursor, ownRank] using checked

theorem pop_marked (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat)
    (item : HeapItem) (children following : Heap HeapItem) (scheduled : NameIndex)
    (unique : UniquePositions coordinate (.node item children .nil) following)
    (marked : MarkedPositions coordinate nameAt (.node item children .nil, following, scheduled)) :
    MarkedPositions coordinate nameAt (children.combine itemLE, following, scheduled) := by
  intro position member
  rw [(pop_pending_unique coordinate item children following scheduled unique).1] at member
  exact marked position (Finset.mem_of_mem_erase member)

/-- The mark is not deleted when a pending position becomes published. -/
theorem pop_exact_marks (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat)
    (published : Finset (Fin size)) (item : HeapItem)
    (children following : Heap HeapItem) (scheduled : NameIndex)
    (unique : UniquePositions coordinate (.node item children .nil) following)
    (marks : ExactMarks coordinate nameAt published (.node item children .nil, following, scheduled)) :
    ExactMarks coordinate nameAt (insert (coordinate item) published)
      (children.combine itemLE, following, scheduled) := by
  exact PlainBnfWakeFrontierExactness.publish_retains_exact_marks coordinate nameAt published
    (.node item children .nil, following, scheduled) (children.combine itemLE, following, scheduled)
    (coordinate item) marks (popped_position_present coordinate item children following scheduled)
    (pop_pending_unique coordinate item children following scheduled unique).1 rfl

theorem exact_marks_implies_marked (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat)
    (published : Finset (Fin size)) (queues : Queues)
    (marks : ExactMarks coordinate nameAt published queues) :
    MarkedPositions coordinate nameAt queues := by
  intro position member
  have stored : position ∈ PlainBnfWakeFrontierExactness.scheduledPositions nameAt queues.2.2 := by
    rw [marks]
    exact Finset.mem_union_right _ member
  simpa only [PlainBnfWakeFrontierExactness.scheduledPositions, Finset.mem_filter,
    Finset.mem_univ, true_and] using stored

/-- Composition for the exact queue returned by the existing publication
observation: pop, then Wake under the post-publication known history. -/
theorem publishedQueues_invariants (productive : Bool) (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (published : Finset (Fin size)) (origin : Option Rank) (item : Item) (dependents : List Item)
    (history : List SExpr) (lexicals : List PlainBnfStructuredDenotation.LexicalDeclaration)
    (children following : Heap HeapItem) (scheduled : NameIndex)
    (ordered : Ordered (.node (heapItem item) children .nil, following, scheduled))
    (placed : WellPlaced coordinate origin (.node (heapItem item) children .nil, following, scheduled))
    (unique : UniquePositions coordinate (.node (heapItem item) children .nil) following)
    (marks : ExactMarks coordinate nameAt published (.node (heapItem item) children .nil, following, scheduled))
    (liveRanks : ∀ payload ∈ PlainBnfPairingHeapObservation.contents (.node (heapItem item) children .nil),
      value payload.1 = (coordinate payload).val)
    (rankCoordinates : ∀ next ∈ dependents, value next.1 = (coordinate (heapItem next)).val)
    (keyCoordinates : ∀ next ∈ dependents, nameAt (coordinate (heapItem next)) = key next.2.name) :
    let after := PlainBnfRunSourceExecution.publishedQueues productive item dependents history lexicals
      children following scheduled
    Ordered after ∧ WellPlaced coordinate (some item.1) after ∧
      UniquePositions coordinate after.1 after.2.1 ∧ MarkedPositions coordinate nameAt after ∧
      ExactMarks coordinate nameAt (insert (coordinate (heapItem item)) published) after := by
  have poppedOrder := pop_ordered (heapItem item) children following scheduled ordered
  have poppedPlacement := pop_wellPlaced coordinate origin (heapItem item) children following scheduled
    ordered placed unique liveRanks
  have poppedUnique := (pop_pending_unique coordinate (heapItem item) children following scheduled unique).2.2
  have poppedMarks := pop_exact_marks coordinate nameAt published (heapItem item) children following scheduled unique marks
  have invariants := wake_invariants
    (PlainBnfWakeContextualExecution.meaning productive (PlainBnfRunSourceExecution.publishedHistory item history) lexicals)
    coordinate nameAt (some item.1) dependents (children.combine itemLE, following, scheduled)
    poppedOrder poppedPlacement poppedUnique
    (exact_marks_implies_marked coordinate nameAt _ _ poppedMarks) rankCoordinates keyCoordinates
  exact ⟨invariants.1, invariants.2.1, invariants.2.2.1, invariants.2.2.2,
    PlainBnfWakeFrontierExactness.wake_exact_marks coordinate nameAt namesInjective _ _ _ _ _
      poppedOrder poppedMarks keyCoordinates⟩

/-- The finite pending observation is the old frontier minus the popped
position, together with the positions of the actually selected occurrences. -/
theorem publishedQueues_pending (productive : Bool) (coordinate : HeapItem → Fin size)
    (item : Item) (dependents : List Item) (history : List SExpr)
    (lexicals : List PlainBnfStructuredDenotation.LexicalDeclaration)
    (children following : Heap HeapItem) (scheduled : NameIndex)
    (ordered : Ordered (.node (heapItem item) children .nil, following, scheduled))
    (unique : UniquePositions coordinate (.node (heapItem item) children .nil) following) :
    pending coordinate (PlainBnfRunSourceExecution.publishedQueues productive item dependents history lexicals
      children following scheduled) =
      PlainBnfWakeFrontierExactness.occurrencePositions coordinate
        (selected (PlainBnfWakeContextualExecution.meaning productive
          (PlainBnfRunSourceExecution.publishedHistory item history) lexicals) dependents scheduled) ∪
      (pending coordinate (.node (heapItem item) children .nil, following, scheduled)).erase
        (coordinate (heapItem item)) := by
  rw [PlainBnfRunSourceExecution.publishedQueues, wake_pending _ _ _ _ _
    (pop_ordered (heapItem item) children following scheduled ordered),
    (pop_pending_unique coordinate (heapItem item) children following scheduled unique).1]
  rfl

/-- Full payload accounting, before any finite-set projection: the removed
occurrence plus all remaining occurrences equal the old bag plus the selected
new source occurrences. Equal coordinates never stand in for equal payloads. -/
theorem publishedQueues_contents (productive : Bool) (item : Item) (dependents : List Item)
    (history : List SExpr) (lexicals : List PlainBnfStructuredDenotation.LexicalDeclaration)
    (children following : Heap HeapItem) (scheduled : NameIndex)
    (ordered : Ordered (.node (heapItem item) children .nil, following, scheduled)) :
    heapItem item ::ₘ contents (PlainBnfRunSourceExecution.publishedQueues productive item dependents history lexicals
      children following scheduled) =
      (↑((selected (PlainBnfWakeContextualExecution.meaning productive
        (PlainBnfRunSourceExecution.publishedHistory item history) lexicals) dependents scheduled).map heapItem) :
          Multiset HeapItem) + contents (.node (heapItem item) children .nil, following, scheduled) := by
  rw [PlainBnfRunSourceExecution.publishedQueues, wake_contents _ _ _ _
    (pop_ordered (heapItem item) children following scheduled ordered), pop_contents]
  simp only [Multiset.add_cons]

/-- Every live output retains full provenance from the original candidates.
The input bucket may repeat a candidate; it is not deduplicated here. -/
theorem publishedQueues_payload_provenance (productive : Bool) (item : Item)
    (candidates dependents : List Item) (history : List SExpr)
    (lexicals : List PlainBnfStructuredDenotation.LexicalDeclaration)
    (children following : Heap HeapItem) (scheduled : NameIndex)
    (ordered : Ordered (.node (heapItem item) children .nil, following, scheduled))
    (liveProvenance : ∀ payload ∈ contents (.node (heapItem item) children .nil, following, scheduled),
      payload ∈ candidates.map heapItem)
    (dependentProvenance : ∀ next ∈ dependents, next ∈ candidates) :
    ∀ payload ∈ contents (PlainBnfRunSourceExecution.publishedQueues productive item dependents history lexicals
      children following scheduled), payload ∈ candidates.map heapItem := by
  intro payload inside
  have accounted : payload ∈ heapItem item ::ₘ contents
      (PlainBnfRunSourceExecution.publishedQueues productive item dependents history lexicals
        children following scheduled) := Multiset.mem_cons_of_mem inside
  rw [publishedQueues_contents productive item dependents history lexicals children following scheduled ordered] at accounted
  rcases Multiset.mem_add.mp accounted with selectedMember | oldMember
  · have listMember : payload ∈ (selected (PlainBnfWakeContextualExecution.meaning productive
        (PlainBnfRunSourceExecution.publishedHistory item history) lexicals) dependents scheduled).map heapItem := by
      simpa only [Multiset.mem_coe] using selectedMember
    obtain ⟨next, nextMember, rfl⟩ := List.mem_map.mp listMember
    exact List.mem_map.mpr ⟨next, dependentProvenance next
      ((selected_sublist _ _ _).subset nextMember), rfl⟩
  · exact liveProvenance payload oldMember

/-- A singleton with no dependent input is really removed; the existing
scheduled trie is retained unchanged rather than cleared with the queue. -/
theorem singleton_publication_preserves_marks (productive : Bool) (item : Item)
    (history : List SExpr) (lexicals : List PlainBnfStructuredDenotation.LexicalDeclaration)
    (scheduled : NameIndex) :
    PlainBnfRunSourceExecution.publishedQueues productive item [] history lexicals .nil .nil scheduled =
      (.nil, .nil, scheduled) := rfl

/-- Heap ordering alone does not justify position erasure: two equal-priority
occurrences survive as separate payloads and only one is popped. -/
theorem duplicate_position_refuses_erasure (coordinate : HeapItem → Fin size) (item : HeapItem) :
    Ordered (.node item (.node item .nil .nil) .nil, .nil, Trie.empty) ∧
    ¬ UniquePositions coordinate (.node item (.node item .nil .nil) .nil) .nil ∧
    pending coordinate ((Heap.node item .nil .nil).combine itemLE, .nil, Trie.empty) ≠
      (pending coordinate (.node item (.node item .nil .nil) .nil, .nil, Trie.empty)).erase (coordinate item) := by
  refine ⟨⟨Heap.WF.node ?_, Heap.WF.nil⟩, ?_, ?_⟩
  · simp [Heap.NodeWF, itemLE, rankLE_iff]
  · simp [UniquePositions, PlainBnfPairingHeapObservation.contents]
  · simp [pending, positions, Heap.combine, PlainBnfPairingHeapObservation.contents]

end Mettapedia.GSLT.Parsing.PlainBnfControllerQueuePreservation
