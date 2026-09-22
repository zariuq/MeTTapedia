import Mettapedia.GSLT.Parsing.PlainBnfWakeSourceExecution

/-!
# Exact finite-coordinate frontier of the existing Wake fold

Finite sets observe only which source positions are pending. The source
occurrence ledger, its order, full heap payloads, and the underlying Wake
operations remain those of `PlainBnfWakeSourceExecution`.

A mark must denote a published or pending position before it can justify
suppression. Mere coverage of pending positions does not exclude stale marks.
The source name/position correspondence is explicit throughout.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfWakeFrontierExactness

open Algorithms.MeTTa.Simple.Parser (SExpr)
open PlainBnfStructuredDenotation (Expression)
open PlainBnfReverseIndexSourceExecution (Item key)
open PlainBnfGraphNameTrie (Trie lookup insertFirst)
open PlainBnfCollectorSourceExecution (name)
open PlainBnfSourceRank (Rank)
open PlainBnfWakeSourceExecution

/-- Selection is complete for ready, initially unmarked names, even when an
earlier occurrence of that name was unready. No input deduplication is used. -/
theorem ready_name_selected (ready : Expression → Bool) (input : List Item)
    (scheduled : Trie SExpr) (query : List Nat)
    (missing : lookup query scheduled = none)
    (candidate : ∃ item ∈ input, key item.2.name = query ∧ ready item.2.expression = true) :
    query ∈ (selected ready input scheduled).map (fun item => key item.2.name) := by
  induction input generalizing scheduled with
  | nil => simp at candidate
  | cons first rest ih =>
    by_cases firstMissing : lookup (key first.2.name) scheduled = none
    · by_cases firstReady : ready first.2.expression = true
      · simp only [selected, firstMissing, firstReady, ↓reduceIte, List.map_cons, List.mem_cons]
        by_cases same : key first.2.name = query
        · exact Or.inl same.symm
        · apply Or.inr
          apply ih
          · rw [PlainBnfGraphNameTrie.lookup_insertFirst]
            simp [Ne.symm same, missing]
          · obtain ⟨item, member, itemKey, itemReady⟩ := candidate
            rcases List.mem_cons.mp member with equal | inside
            · subst item
              exact False.elim (same itemKey)
            · exact ⟨item, inside, itemKey, itemReady⟩
      · simp only [selected, firstMissing, firstReady, ↓reduceIte]
        apply ih scheduled missing
        obtain ⟨item, member, itemKey, itemReady⟩ := candidate
        rcases List.mem_cons.mp member with equal | inside
        · subst item
          exact False.elim (firstReady itemReady)
        · exact ⟨item, inside, itemKey, itemReady⟩
    · simp only [selected, firstMissing, ↓reduceIte]
      apply ih scheduled missing
      obtain ⟨item, member, itemKey, itemReady⟩ := candidate
      rcases List.mem_cons.mp member with equal | inside
      · subst item
        exact False.elim (firstMissing (itemKey ▸ missing))
      · exact ⟨item, inside, itemKey, itemReady⟩

theorem selected_name_iff (ready : Expression → Bool) (input : List Item)
    (scheduled : Trie SExpr) (query : List Nat) :
    query ∈ (selected ready input scheduled).map (fun item => key item.2.name) ↔
      query ∈ ((input.filter fun item => ready item.2.expression).map fun item => key item.2.name) ∧
        lookup query scheduled = none := by
  constructor
  · intro member
    obtain ⟨item, inside, same⟩ := List.mem_map.mp member
    refine ⟨List.mem_map.mpr ⟨item, List.mem_filter.mpr ⟨?_, ?_⟩, same⟩, ?_⟩
    · exact (selected_sublist ready input scheduled).subset inside
    · exact selected_is_ready ready input scheduled item inside
    · rw [← same]
      exact selected_initially_missing ready input scheduled item inside
  · rintro ⟨member, missing⟩
    obtain ⟨item, inside, same⟩ := List.mem_map.mp member
    obtain ⟨present, enabled⟩ := List.mem_filter.mp inside
    exact ready_name_selected ready input scheduled query missing ⟨item, present, same, enabled⟩

variable {size : Nat}

/-- Scheduling-position observation of an unchanged occurrence list. -/
def occurrencePositions (coordinate : HeapItem → Fin size) (input : List Item) : Finset (Fin size) :=
  (input.map fun item => coordinate (heapItem item)).toFinset

def readyCandidatePositions (coordinate : HeapItem → Fin size) (ready : Expression → Bool)
    (input : List Item) : Finset (Fin size) :=
  occurrencePositions coordinate (input.filter fun item => ready item.2.expression)

def scheduledPositions (nameAt : Fin size → List Nat) (scheduled : Trie SExpr) : Finset (Fin size) :=
  Finset.univ.filter fun position => lookup (nameAt position) scheduled ≠ none

theorem mem_occurrencePositions_iff_name (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (input : List Item)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name)
    (position : Fin size) :
    position ∈ occurrencePositions coordinate input ↔
      nameAt position ∈ input.map (fun item => key item.2.name) := by
  simp only [occurrencePositions, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨item, member, same⟩
    exact ⟨item, member, (keyCoordinates item member).symm.trans (congrArg nameAt same)⟩
  · rintro ⟨item, member, same⟩
    exact ⟨item, member, namesInjective ((keyCoordinates item member).trans same)⟩

theorem selected_positions_exact (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (ready : Expression → Bool) (input : List Item) (scheduled : Trie SExpr)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name) :
    occurrencePositions coordinate (selected ready input scheduled) =
      readyCandidatePositions coordinate ready input \ scheduledPositions nameAt scheduled := by
  ext position
  rw [mem_occurrencePositions_iff_name coordinate nameAt namesInjective _
    (fun item member => keyCoordinates item ((selected_sublist ready input scheduled).subset member))]
  simp only [Finset.mem_sdiff, readyCandidatePositions]
  rw [mem_occurrencePositions_iff_name coordinate nameAt namesInjective _
    (fun item member => keyCoordinates item (List.mem_filter.mp member).1)]
  simp [selected_name_iff, scheduledPositions]

theorem wake_pending_exact (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (ready : Expression → Bool) (origin : Option Rank) (input : List Item) (queues : Queues)
    (ordered : Ordered queues)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name) :
    pending coordinate (wake ready origin input queues) =
      pending coordinate queues ∪
        (readyCandidatePositions coordinate ready input \ scheduledPositions nameAt queues.2.2) := by
  rw [wake_pending ready coordinate origin input queues ordered]
  change occurrencePositions coordinate (selected ready input queues.2.2) ∪ pending coordinate queues = _
  rw [selected_positions_exact coordinate nameAt namesInjective ready input queues.2.2 keyCoordinates,
    Finset.union_comm]

/-- A provenance invariant for marks in the admitted finite name universe.
Marks outside that universe are inert for coordinate-correct candidates. -/
def ExactMarks (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat)
    (published : Finset (Fin size)) (queues : Queues) : Prop :=
  scheduledPositions nameAt queues.2.2 = published ∪ pending coordinate queues

theorem scheduled_positions_wake (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (ready : Expression → Bool) (origin : Option Rank) (input : List Item) (queues : Queues)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name) :
    scheduledPositions nameAt (wake ready origin input queues).2.2 =
      scheduledPositions nameAt queues.2.2 ∪
        occurrencePositions coordinate (selected ready input queues.2.2) := by
  ext position
  rw [Finset.mem_union, mem_occurrencePositions_iff_name coordinate nameAt namesInjective _
    (fun item member => keyCoordinates item ((selected_sublist ready input queues.2.2).subset member))]
  simp only [scheduledPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [wake_marks_exact]
  cases lookup (nameAt position) queues.2.2 <;>
    by_cases chosen : nameAt position ∈ (selected ready input queues.2.2).map (fun item => key item.2.name) <;>
    simp [chosen]

theorem wake_exact_marks (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (ready : Expression → Bool) (origin : Option Rank) (input : List Item) (queues : Queues)
    (published : Finset (Fin size)) (ordered : Ordered queues)
    (marks : ExactMarks coordinate nameAt published queues)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name) :
    ExactMarks coordinate nameAt published (wake ready origin input queues) := by
  unfold ExactMarks at marks ⊢
  rw [scheduled_positions_wake coordinate nameAt namesInjective ready origin input queues keyCoordinates,
    marks, wake_pending ready coordinate origin input queues ordered]
  simp only [occurrencePositions]
  ac_rfl

theorem wake_pending_unpublished (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (ready : Expression → Bool) (origin : Option Rank) (input : List Item) (queues : Queues)
    (published : Finset (Fin size)) (ordered : Ordered queues)
    (marks : ExactMarks coordinate nameAt published queues)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name) :
    pending coordinate (wake ready origin input queues) =
      pending coordinate queues ∪ (readyCandidatePositions coordinate ready input \ published) := by
  rw [wake_pending_exact coordinate nameAt namesInjective ready origin input queues ordered keyCoordinates,
    marks]
  ext position
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- Every selected occurrence has a fresh position: neither already published
nor already pending. This does not discard that occurrence's body or span. -/
theorem selected_position_fresh (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (ready : Expression → Bool) (input : List Item)
    (queues : Queues) (published : Finset (Fin size))
    (marks : ExactMarks coordinate nameAt published queues)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name)
    (item : Item) (selectedItem : item ∈ selected ready input queues.2.2) :
    coordinate (heapItem item) ∉ published ∧ coordinate (heapItem item) ∉ pending coordinate queues := by
  have missing := selected_initially_missing ready input queues.2.2 item selectedItem
  have aligned := keyCoordinates item ((selected_sublist ready input queues.2.2).subset selectedItem)
  have absent : coordinate (heapItem item) ∉ scheduledPositions nameAt queues.2.2 := by
    simp [scheduledPositions, aligned, missing]
  rw [marks] at absent
  simpa using absent

theorem wake_no_published_pending (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (ready : Expression → Bool) (origin : Option Rank) (input : List Item) (queues : Queues)
    (published : Finset (Fin size)) (ordered : Ordered queues)
    (marks : ExactMarks coordinate nameAt published queues)
    (oldDisjoint : Disjoint published (pending coordinate queues))
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name) :
    Disjoint published (pending coordinate (wake ready origin input queues)) := by
  rw [wake_pending_unpublished coordinate nameAt namesInjective ready origin input queues
    published ordered marks keyCoordinates]
  apply Finset.disjoint_left.mpr
  intro position publishedMember queued
  rcases Finset.mem_union.mp queued with old | new
  · exact Finset.disjoint_left.mp oldDisjoint publishedMember old
  · exact (Finset.mem_sdiff.mp new).2 publishedMember

/-- Publication moves a position from pending to published while retaining
the existing scheduled trie. The actual heap-pop proof supplies the erasure
equation; this lemma does not assume that arbitrary pops preserve uniqueness. -/
theorem publish_retains_exact_marks (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (published : Finset (Fin size))
    (before after : Queues) (position : Fin size)
    (marks : ExactMarks coordinate nameAt published before)
    (wasPending : position ∈ pending coordinate before)
    (removed : pending coordinate after = (pending coordinate before).erase position)
    (retained : after.2.2 = before.2.2) :
    ExactMarks coordinate nameAt (insert position published) after := by
  unfold ExactMarks
  rw [retained, marks, removed,
    PlainBnfTwoHeapWorklist.publish_pop_retains_scheduled published
      (pending coordinate before) position wasPending]

theorem empty_exact_marks (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat) :
    ExactMarks coordinate nameAt ∅ (.nil, .nil, .empty) := by
  simp [ExactMarks, scheduledPositions, pending, PlainBnfTwoHeapWorklist.positions_nil]

theorem empty_wake_exact_frontier (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (ready : Expression → Bool) (origin : Option Rank) (input : List Item)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name) :
    pending coordinate (wake ready origin input (.nil, .nil, .empty)) =
      readyCandidatePositions coordinate ready input := by
  rw [wake_pending_exact coordinate nameAt namesInjective ready origin input _
    ⟨.nil, .nil⟩ keyCoordinates]
  simp [pending, PlainBnfTwoHeapWorklist.positions_nil, scheduledPositions]

/-- Complete candidate coverage and the separate expression/coordinate
readiness correspondence connect initialization to the existing worklist. -/
theorem empty_wake_initialQueue (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (namesInjective : Function.Injective nameAt)
    (ready : Expression → Bool) (origin : Option Rank) (input : List Item)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name)
    (grammar : PlainBnfOrderedGraphDiscovery.Grammar size)
    (known : PlainBnfOrderedGraphDiscovery.Known size)
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position)
    (meaning : ∀ item ∈ input, ready item.2.expression =
      PlainBnfOrderedGraphDiscovery.ready grammar known (coordinate (heapItem item))) :
    pending coordinate (wake ready origin input (.nil, .nil, .empty)) =
      PlainBnfDependencyWorklist.initialQueue grammar known := by
  rw [empty_wake_exact_frontier coordinate nameAt namesInjective ready origin input keyCoordinates]
  ext position
  simp only [readyCandidatePositions, occurrencePositions, List.mem_toFinset,
    List.mem_map, List.mem_filter, PlainBnfDependencyWorklist.initialQueue,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨item, ⟨member, enabled⟩, same⟩
    rw [meaning item member, same] at enabled
    exact enabled
  · intro enabled
    obtain ⟨item, member, same⟩ := covers position
    refine ⟨item, ⟨member, ?_⟩, same⟩
    rw [meaning item member, same]
    exact enabled

/-- A stale mark for a live candidate violates exact provenance, even though
empty heaps satisfy the weaker pending-mark coverage condition. -/
theorem stale_mark_not_exact (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat)
    (item : Item) (payload : SExpr)
    (keyCoordinate : nameAt (coordinate (heapItem item)) = key item.2.name) :
    ¬ ExactMarks coordinate nameAt ∅
      (.nil, .nil, insertFirst (key item.2.name) payload .empty) := by
  intro exactMarks
  have marked : coordinate (heapItem item) ∈
      scheduledPositions nameAt (insertFirst (key item.2.name) payload .empty) := by
    simp [scheduledPositions, keyCoordinate, PlainBnfGraphNameTrie.lookup_inserted]
  rw [exactMarks] at marked
  simp [pending, PlainBnfTwoHeapWorklist.positions_nil] at marked

theorem stale_mark_suppresses_ready_frontier (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (ready : Expression → Bool) (item : Item) (payload : SExpr)
    (keyCoordinate : nameAt (coordinate (heapItem item)) = key item.2.name)
    (available : ready item.2.expression = true) :
    let queues : Queues := (.nil, .nil, insertFirst (key item.2.name) payload .empty)
    pending coordinate (wake ready none [item] queues) = ∅ ∧
      readyCandidatePositions coordinate ready [item] = {coordinate (heapItem item)} ∧
      ¬ ExactMarks coordinate nameAt ∅ queues := by
  dsimp only
  refine ⟨?_, ?_, stale_mark_not_exact coordinate nameAt item payload keyCoordinate⟩
  · rw [stale_mark_can_suppress]
    simp [pending, PlainBnfTwoHeapWorklist.positions_nil]
  · simp [readyCandidatePositions, occurrencePositions, available]

/-- Name-based suppression cannot promise both coordinates when different
positions claim one name. The injective admitted name map excludes this case;
the unchanged occurrence list still contains both payloads. -/
theorem name_alias_prevents_position_completeness (coordinate : HeapItem → Fin size)
    (ready : Expression → Bool) (first second : Item)
    (sameName : first.2.name = second.2.name)
    (differentPositions : coordinate (heapItem first) ≠ coordinate (heapItem second))
    (firstReady : ready first.2.expression = true) (secondReady : ready second.2.expression = true) :
    occurrencePositions coordinate (selected ready [first, second] .empty) ≠
      readyCandidatePositions coordinate ready [first, second] := by
  have picked := (repeated_name_suppressed ready none first second
    (.nil, .nil, .empty) sameName (by simp) firstReady).1
  rw [picked]
  intro equal
  have member : coordinate (heapItem second) ∈ readyCandidatePositions coordinate ready [first, second] := by
    simp [readyCandidatePositions, occurrencePositions, firstReady, secondReady]
  rw [← equal] at member
  simp [occurrencePositions, Ne.symm differentPositions] at member

end Mettapedia.GSLT.Parsing.PlainBnfWakeFrontierExactness
