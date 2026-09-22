import Mettapedia.GSLT.Parsing.PlainBnfPairingHeapObservation

/-!
# Two-heap observations of plain-BNF ordered discovery

The existing current/following pairing heaps represent the pending positions
on the two sides of the source cursor. This module connects their heads to
the independent ordered worklist selection and proves the partition laws for
the existing heap operations. It introduces no queue runtime or parser.

Full payload multiplicity is retained by the imported heap laws. Projection
to positions is used only for scheduling; uniqueness obligations are explicit
where removal must not silently collapse two occurrences. The source GSLT
execution and live name/rank correspondence require their separate bridges.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfTwoHeapWorklist

open Batteries.PairingHeapImp (Heap)
open PlainBnfPairingHeapObservation (contents head_minimum)
open PlainBnfOrderedGraphDiscovery (Event)

variable {α : Type*} {size : Nat}

def positions (position : α → Fin size) (heap : Heap α) : Finset (Fin size) :=
  ((contents heap).map position).toFinset

def Partitioned (position : α → Fin size) (pending : Finset (Fin size))
    (cursor : Nat) (current following : Heap α) : Prop :=
  positions position current = pending.filter (fun p => cursor ≤ p.val) ∧
  positions position following = pending.filter (fun p => p.val < cursor)

theorem positions_nil (position : α → Fin size) : positions position .nil = ∅ := rfl

theorem empty_partition (position : α → Fin size) (cursor : Nat) :
    Partitioned position ∅ cursor .nil .nil := by simp [Partitioned, positions_nil]

/-- Only live contents need a coordinate/order interpretation. This does not
require every possible heap payload to be a member of the current grammar. -/
theorem head_eq_least_on_contents (position : α → Fin size)
    (le : α → α → Bool) [Batteries.TotalBLE le]
    (transitive : ∀ {a b c}, le a b = true → le b c = true → le a c = true)
    (heap : Heap α) (ordered : heap.WF le)
    (coordinates : ∀ a ∈ contents heap, ∀ b ∈ contents heap,
      le a b = true → position a ≤ position b) :
    heap.head?.map position = PlainBnfDependencyWorklist.least (positions position heap) := by
  cases found : heap.head? with
  | none =>
      cases heap with
      | nil => simp [positions_nil, PlainBnfDependencyWorklist.least]
      | node => cases found
  | some item =>
      simp only [Option.map_some]
      symm
      apply (PlainBnfDependencyWorklist.least_some_iff _ _).mpr
      obtain ⟨inside, minimum⟩ := head_minimum (le := le)
        (fun first second => transitive first second) ordered found
      constructor
      · simp only [positions, Multiset.mem_toFinset, Multiset.mem_map]
        exact ⟨item, inside, rfl⟩
      · intro other member
        simp only [positions, Multiset.mem_toFinset, Multiset.mem_map] at member
        obtain ⟨payload, present, rfl⟩ := member
        exact coordinates item inside payload present (minimum payload present)

theorem partition_union (position : α → Fin size) (pending : Finset (Fin size))
    (cursor : Nat) (current following : Heap α)
    (partition : Partitioned position pending cursor current following) :
    positions position current ∪ positions position following = pending := by
  rw [partition.1, partition.2]
  ext p
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨member, _⟩ | ⟨member, _⟩) <;> exact member
  · intro member
    by_cases later : cursor ≤ p.val
    · exact Or.inl ⟨member, later⟩
    · exact Or.inr ⟨member, by omega⟩

theorem partition_disjoint (position : α → Fin size) (pending : Finset (Fin size))
    (cursor : Nat) (current following : Heap α)
    (partition : Partitioned position pending cursor current following) :
    Disjoint (positions position current) (positions position following) := by
  apply Finset.disjoint_left.mpr
  intro p first second
  rw [partition.1] at first
  rw [partition.2] at second
  have later := (Finset.mem_filter.mp first).2
  have earlier := (Finset.mem_filter.mp second).2
  omega

/-- Head observation of the existing current/following heaps. A round wraps
only when the current heap is empty; it does not globally choose the smaller
head across both heaps. -/
theorem select_eq_ordered_worklist (position : α → Fin size)
    (le : α → α → Bool) [Batteries.TotalBLE le]
    (transitive : ∀ {a b c}, le a b = true → le b c = true → le a c = true)
    (current following : Heap α) (currentWF : current.WF le) (followingWF : following.WF le)
    (currentOrder : ∀ a ∈ contents current, ∀ b ∈ contents current,
      le a b = true → position a ≤ position b)
    (followingOrder : ∀ a ∈ contents following, ∀ b ∈ contents following,
      le a b = true → position a ≤ position b)
    (pending : Finset (Fin size)) (round cursor : Nat)
    (partition : Partitioned position pending cursor current following) :
    (match current.head?.map position with
      | some p => some (⟨round, p⟩ : Event size)
      | none => (following.head?.map position).map fun p => (⟨round + 1, p⟩ : Event size)) =
      PlainBnfDependencyWorklist.select pending round cursor := by
  rw [head_eq_least_on_contents position le transitive current currentWF currentOrder,
    head_eq_least_on_contents position le transitive following followingWF followingOrder]
  unfold PlainBnfDependencyWorklist.select
  rw [partition.1]
  cases suffix : PlainBnfDependencyWorklist.least (pending.filter fun p => cursor ≤ p.val) with
  | some p => rfl
  | none =>
      have empty := (PlainBnfDependencyWorklist.least_none_iff _).mp suffix
      have allFollowing := partition_union position pending cursor current following partition
      rw [partition.1, empty, Finset.empty_union] at allFollowing
      rw [allFollowing]

theorem positions_merge_singleton (position : α → Fin size) (le : α → α → Bool)
    (item : α) (heap : Heap α) (single : heap.NoSibling) :
    positions position ((Heap.node item .nil .nil).merge le heap) =
      insert (position item) (positions position heap) := by
  unfold positions
  rw [PlainBnfPairingHeapObservation.contents_merge le (by constructor) single]
  simp [contents]

theorem enqueue_current_partition (position : α → Fin size) (le : α → α → Bool)
    (item : α) (current following : Heap α) (single : current.NoSibling)
    (pending : Finset (Fin size)) (cursor : Nat)
    (partition : Partitioned position pending cursor current following)
    (later : cursor ≤ (position item).val) :
    Partitioned position (insert (position item) pending) cursor
      ((Heap.node item .nil .nil).merge le current) following := by
  constructor
  · rw [positions_merge_singleton _ _ _ _ single, partition.1]
    simp [Finset.filter_insert, later]
  · rw [partition.2]
    have earlier : ¬ (position item).val < cursor := by omega
    simp [Finset.filter_insert, earlier]

theorem enqueue_following_partition (position : α → Fin size) (le : α → α → Bool)
    (item : α) (current following : Heap α) (single : following.NoSibling)
    (pending : Finset (Fin size)) (cursor : Nat)
    (partition : Partitioned position pending cursor current following)
    (earlier : (position item).val < cursor) :
    Partitioned position (insert (position item) pending) cursor
      current ((Heap.node item .nil .nil).merge le following) := by
  constructor
  · rw [partition.1]
    have later : ¬ cursor ≤ (position item).val := by omega
    simp [Finset.filter_insert, later]
  · rw [positions_merge_singleton _ _ _ _ single, partition.2]
    simp [Finset.filter_insert, earlier]

theorem partition_of_union_bounds (position : α → Fin size)
    (pending : Finset (Fin size)) (cursor : Nat) (current following : Heap α)
    (allPositions : positions position current ∪ positions position following = pending)
    (currentBound : ∀ p ∈ positions position current, cursor ≤ p.val)
    (followingBound : ∀ p ∈ positions position following, p.val < cursor) :
    Partitioned position pending cursor current following := by
  constructor
  · ext p
    rw [← allPositions]
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro member
      exact ⟨Or.inl member, currentBound p member⟩
    · rintro ⟨member | member, bound⟩
      · exact member
      · have := followingBound p member
        omega
  · ext p
    rw [← allPositions]
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro member
      exact ⟨Or.inr member, followingBound p member⟩
    · rintro ⟨member | member, bound⟩
      · have := currentBound p member
        omega
      · exact member

/-- Removing one payload occurrence is set erasure only when source positions
are unique in the heap. This premise is not implied by heap ordering. -/
theorem positions_deleteMin (position : α → Fin size) (le : α → α → Bool)
    {heap rest : Heap α} {item : α} (single : heap.NoSibling)
    (unique : ((contents heap).map position).Nodup)
    (returned : heap.deleteMin le = some (item, rest)) :
    positions position rest = (positions position heap).erase (position item) ∧
      position item ∉ positions position rest ∧
      ((contents rest).map position).Nodup := by
  have decomposition := PlainBnfPairingHeapObservation.contents_deleteMin le single returned
  rw [decomposition, Multiset.map_cons, Multiset.nodup_cons] at unique
  have absent : position item ∉ positions position rest := by
    simpa only [positions, Multiset.mem_toFinset] using unique.1
  have whole : positions position heap =
      insert (position item) (positions position rest) := by
    simp only [positions, decomposition, Multiset.map_cons, Multiset.toFinset_cons]
  refine ⟨?_, absent, unique.2⟩
  rw [whole]
  simp [absent]

/-- Deletion advances the cursor past the selected source occurrence. The
minimum law excludes skipped current-round positions; uniqueness excludes a
second occurrence at the same position. -/
theorem pop_current_partition (position : α → Fin size)
    (le : α → α → Bool) [Batteries.TotalBLE le]
    (transitive : ∀ {a b c}, le a b = true → le b c = true → le a c = true)
    {current rest following : Heap α} {item : α} (ordered : current.WF le)
    (coordinates : ∀ a ∈ contents current, ∀ b ∈ contents current,
      le a b = true → position a ≤ position b)
    (unique : ((contents current).map position).Nodup)
    (returned : current.deleteMin le = some (item, rest))
    (pending : Finset (Fin size)) (cursor : Nat)
    (partition : Partitioned position pending cursor current following) :
    Partitioned position (pending.erase (position item)) ((position item).val + 1)
      rest following := by
  have single : current.NoSibling := by cases ordered <;> constructor
  obtain ⟨erased, absent, _⟩ := positions_deleteMin position le single unique returned
  obtain ⟨inside, _, minimum⟩ := PlainBnfPairingHeapObservation.deleteMin_lower_bound
    (le := le) (fun first second => transitive first second) ordered returned
  have headMember : position item ∈ positions position current := by
    simp only [positions, Multiset.mem_toFinset, Multiset.mem_map]
    exact ⟨item, inside, rfl⟩
  have later : cursor ≤ (position item).val := by
    rw [partition.1] at headMember
    exact (Finset.mem_filter.mp headMember).2
  have notFollowing : position item ∉ positions position following := by
    rw [partition.2]
    simp only [Finset.mem_filter]
    rintro ⟨_, earlier⟩
    omega
  apply partition_of_union_bounds
  · rw [erased, ← Finset.erase_eq_of_notMem notFollowing, ← Finset.erase_union_distrib,
      partition_union position pending cursor current following partition]
  · intro p member
    have notSame : p ≠ position item := by
      intro same
      subst p
      exact absent member
    simp only [positions, Multiset.mem_toFinset, Multiset.mem_map] at member
    obtain ⟨payload, present, rfl⟩ := member
    have presentBefore : payload ∈ contents current := by
      rw [PlainBnfPairingHeapObservation.contents_deleteMin le single returned]
      exact Multiset.mem_cons_of_mem present
    have before := coordinates item inside payload presentBefore (minimum payload present)
    have strict : (position item).val < (position payload).val := by
      have different : (position payload).val ≠ (position item).val :=
        fun same => notSame (Fin.ext same)
      change (position item).val ≤ (position payload).val at before
      omega
    omega
  · intro p member
    rw [partition.2] at member
    have earlier := (Finset.mem_filter.mp member).2
    omega

theorem rollover_partition (position : α → Fin size)
    (pending : Finset (Fin size)) (cursor : Nat) (following : Heap α)
    (partition : Partitioned position pending cursor .nil following) :
    Partitioned position pending 0 following .nil := by
  apply partition_of_union_bounds
  · have union := partition_union position pending cursor .nil following partition
    simpa only [positions_nil, Finset.empty_union, Finset.union_empty] using union
  · intro p _
    exact Nat.zero_le p.val
  · simp [positions_nil]

/-- This concerns pending source positions, not equality of grammar rules or
dependency references. Repeated references remain legal source occurrences. -/
def UniquePositions (position : α → Fin size) (current following : Heap α) : Prop :=
  ((contents current).map position + (contents following).map position).Nodup

theorem unique_empty (position : α → Fin size) :
    UniquePositions position .nil .nil := by simp [UniquePositions, contents]

theorem unique_current (position : α → Fin size) {current following : Heap α}
    (unique : UniquePositions position current following) :
    ((contents current).map position).Nodup := (Multiset.nodup_add.mp unique).1

theorem unique_following (position : α → Fin size) {current following : Heap α}
    (unique : UniquePositions position current following) :
    ((contents following).map position).Nodup := (Multiset.nodup_add.mp unique).2.1

theorem enqueue_current_unique (position : α → Fin size) (le : α → α → Bool)
    (item : α) (current following : Heap α) (single : current.NoSibling)
    (unique : UniquePositions position current following)
    (fresh : position item ∉ positions position current ∪ positions position following) :
    UniquePositions position ((Heap.node item .nil .nil).merge le current) following := by
  unfold UniquePositions
  rw [PlainBnfPairingHeapObservation.contents_merge le (by constructor) single]
  simp only [contents, add_zero, Multiset.map_cons,
    Multiset.cons_add, zero_add, Multiset.nodup_cons]
  refine ⟨?_, unique⟩
  simpa only [positions, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_add] using fresh

theorem enqueue_following_unique (position : α → Fin size) (le : α → α → Bool)
    (item : α) (current following : Heap α) (single : following.NoSibling)
    (unique : UniquePositions position current following)
    (fresh : position item ∉ positions position current ∪ positions position following) :
    UniquePositions position current ((Heap.node item .nil .nil).merge le following) := by
  unfold UniquePositions
  rw [PlainBnfPairingHeapObservation.contents_merge le (by constructor) single]
  simp only [contents, add_zero, Multiset.map_cons,
    Multiset.cons_add, zero_add, Multiset.add_cons, Multiset.nodup_cons]
  refine ⟨?_, unique⟩
  simpa only [positions, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_add] using fresh

theorem pop_current_unique (position : α → Fin size) (le : α → α → Bool)
    {current rest following : Heap α} {item : α} (single : current.NoSibling)
    (unique : UniquePositions position current following)
    (returned : current.deleteMin le = some (item, rest)) :
    UniquePositions position rest following := by
  unfold UniquePositions at unique ⊢
  rw [PlainBnfPairingHeapObservation.contents_deleteMin le single returned,
    Multiset.map_cons, Multiset.cons_add, Multiset.nodup_cons] at unique
  exact unique.2

theorem rollover_unique (position : α → Fin size) {following : Heap α}
    (unique : UniquePositions position .nil following) :
    UniquePositions position following .nil := by
  simpa only [UniquePositions, contents, Multiset.map_zero, zero_add, add_zero] using unique

/-- A published position remains in the persistent scheduled set after it
leaves the queue. The source's scheduled index must not be identified with
the pending queue alone. -/
theorem publish_pop_retains_scheduled (published pending : Finset (Fin size))
    (item : Fin size) (queued : item ∈ pending) :
    insert item published ∪ pending.erase item = published ∪ pending := by
  ext p
  by_cases same : p = item
  · subst p
    simp [queued]
  · simp [same]

theorem fresh_scheduled_implies_fresh_pending (published pending : Finset (Fin size))
    (item : Fin size) (fresh : item ∉ published ∪ pending) :
    item ∉ published ∧ item ∉ pending := by
  simpa only [Finset.mem_union, not_or] using fresh

theorem enqueue_extends_scheduled (published pending : Finset (Fin size))
    (item : Fin size) :
    published ∪ insert item pending = insert item (published ∪ pending) := by
  ext p
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

/-- Composition with the independent ordered scan, not merely comparison
with another heap interpreter. The pending/readiness invariant remains an
explicit obligation of the source wake loop. -/
theorem select_eq_nextEvent (position : α → Fin size)
    (le : α → α → Bool) [Batteries.TotalBLE le]
    (transitive : ∀ {a b c}, le a b = true → le b c = true → le a c = true)
    (current following : Heap α) (currentWF : current.WF le) (followingWF : following.WF le)
    (currentOrder : ∀ a ∈ contents current, ∀ b ∈ contents current,
      le a b = true → position a ≤ position b)
    (followingOrder : ∀ a ∈ contents following, ∀ b ∈ contents following,
      le a b = true → position a ≤ position b)
    (grammar : PlainBnfOrderedGraphDiscovery.Grammar size)
    (known : PlainBnfOrderedGraphDiscovery.Known size) (round cursor : Nat)
    (partition : Partitioned position (PlainBnfDependencyWorklist.initialQueue grammar known)
      cursor current following) :
    (match current.head?.map position with
      | some p => some (⟨round, p⟩ : Event size)
      | none => (following.head?.map position).map fun p => (⟨round + 1, p⟩ : Event size)) =
      PlainBnfOrderedGraphDiscovery.nextEvent grammar known round cursor := by
  rw [select_eq_ordered_worklist position le transitive current following currentWF followingWF
    currentOrder followingOrder _ round cursor partition,
    PlainBnfDependencyWorklist.select_eq_nextEvent]

open PlainBnfSourceRank (Rank value compareRank)

theorem rank_greater_iff_current (origin target : Rank) :
    compareRank target origin = .gt ↔ value origin + 1 ≤ value target := by
  rw [PlainBnfSourceRank.compareRank_gt_iff]
  omega

theorem rank_not_greater_iff_following (origin target : Rank) :
    compareRank target origin ≠ .gt ↔ value target < value origin + 1 := by
  change (¬ compareRank target origin = .gt) ↔ _
  rw [PlainBnfSourceRank.compareRank_gt_iff]
  omega

/-- A smaller following-round head must not overtake a current-round head. -/
theorem current_round_precedes_smaller_following_position :
    PlainBnfDependencyWorklist.select ({1, 5} : Finset (Fin 7)) 3 4 = some ⟨3, 5⟩ ∧
    PlainBnfDependencyWorklist.least ({1, 5} : Finset (Fin 7)) = some 1 := by decide

theorem emptied_suffix_wraps_round :
    PlainBnfDependencyWorklist.select ({1} : Finset (Fin 7)) 3 6 = some ⟨4, 1⟩ := by decide

theorem equal_rank_is_deferred :
    compareRank (.one .zero) (.one .zero) = .eq ∧
      ¬ (value (.one .zero) + 1 ≤ value (.one .zero)) := by decide

/-- Without uniqueness, erasing the popped position loses a still-pending
occurrence. Full heap contents and the set of positions are different views. -/
theorem duplicate_pop_is_not_position_erasure :
    let heap : Heap (Fin 2) := .node 1 (.node 1 .nil .nil) .nil
    let rest : Heap (Fin 2) := .node 1 .nil .nil
    heap.deleteMin (fun a b => decide (a ≤ b)) = some (1, rest) ∧
      positions id rest ≠ (positions id heap).erase 1 := by
  constructor
  · rfl
  · decide

theorem repeated_schedule_does_not_imply_unique_pending_positions :
    let singleton : Heap (Fin 2) := .node 1 .nil .nil
    ¬ UniquePositions id (singleton.merge (fun a b => decide (a ≤ b)) singleton) .nil := by
  dsimp only
  unfold UniquePositions
  decide

theorem scheduled_is_not_only_pending :
    let published : Finset (Fin 2) := {1}
    let pending : Finset (Fin 2) := ∅
    published ∪ pending ≠ pending := by decide

#print axioms positions_deleteMin
#print axioms pop_current_partition
#print axioms select_eq_nextEvent
#print axioms enqueue_current_unique
#print axioms publish_pop_retains_scheduled

end Mettapedia.GSLT.Parsing.PlainBnfTwoHeapWorklist
