import Mettapedia.Machines.Cursor.OwnedLifecycle
import Mettapedia.Machines.ResourceTraceWork
import Mettapedia.Machines.ResourceCollectionSchedule

/-!
# Live resources over an unbounded session

This layer reuses the finite graph heap and owner roots of `ResourceOwnership`,
and the publication/cancellation operations of `Cursor.OwnedLifecycle`.
Native roots, foreign handles, resumable continuations and published answers
are separate owner classes of the same graph. Shared descendants and cycles
are counted by address once, not once per owner or answer occurrence.

An allocation transition names its fresh addresses and preserves the byte
weights of existing cells; references and payloads may change. Its byte delta
is derived from those fresh cells. A session trace can allocate, cancel,
publish and collect in any number of iterations. Collection resets allocation
debt. A bound on the surviving *transitive* footprint at collections, together
with allocation headroom, bounds every event boundary, including the allocation
immediately before collection, independently of elapsed interaction count.

This is a sequential retained-cell-byte contract, not a bound on allocator RSS,
foreign allocator internals, collector scratch space, or transient instructions
inside an event. Root-registry metadata and the semantic `World` are not
implicitly charged; their retained runtime representations must themselves be
accounted for by heap cells when bounding total live storage. A native implementation must account for those separately,
enumerate every strong root, and refine each allocation event without hiding
an unbounded internal peak. Keeping an unbounded published history legitimately
violates the bounded-footprint hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.LiveResources

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.Machines.Cursor.OwnedLifecycle

/-- Identities identify individual holders within each root class. -/
inductive Owner where
  | native (id : Nat)
  | foreign (id : Nat)
  | continuation (id : Nat)
  | published (id : Nat)
  deriving DecidableEq, Repr

variable {Address Value World : Type} [DecidableEq Address]

/-- Existing cells are not copied or resized by this transition. Resizing must
be represented by new charged storage (and its old storage later reclaimed).
Outgoing references may change, subject to the target heap's closure law. -/
structure Allocation (before after : Heap Address Value) where
  fresh : Finset Address
  disjoint : Disjoint before.allocated fresh
  domain : after.allocated = before.allocated ∪ fresh
  oldBytes : ∀ a ∈ before.allocated, cellBytes after a = cellBytes before a

def Allocation.bytes {before after : Heap Address Value}
    (step : Allocation before after) : Nat :=
  ∑ a ∈ step.fresh, cellBytes after a

/-- Physical byte growth follows from the allocation sets and per-cell sizes;
it is not assumed as a recurrence. -/
theorem Allocation.accounting {before after : Heap Address Value}
    (step : Allocation before after) :
    allocatedBytes after = allocatedBytes before + step.bytes := by
  unfold allocatedBytes
  rw [step.domain, Finset.sum_union step.disjoint]
  congr 1
  exact Finset.sum_congr rfl step.oldBytes

/-- Cancelling an owner only removes roots; reclamation happens at collection. -/
def cancelOnly (state : Session Owner Address Value World) (dead : Finset Owner) :
    Session Owner Address Value World :=
  { state with roots := cancel state.roots dead }

/-- Published answer occurrences keep their original multiplicity outside this
root registry. `publish` registers their shared physical resource footprint. -/
def publishOnly (state : Session Owner Address Value World) (owner : Owner)
    (answers : List Address) : Session Owner Address Value World :=
  { state with roots := publish state.roots owner answers }

/-- A resource trace is indexed by fresh bytes allocated since its latest
collection. `work` includes evaluation and new foreign handles; the target
root registry must be complete in any implementation refinement. -/
inductive Run (cells bytes headroom : Nat) :
    Session Owner Address Value World → Nat → Prop where
  | initial (state : Session Owner Address Value World)
      (valid : ValidRoots state.heap state.roots)
      (count : (footprint state.heap state.roots).card ≤ cells)
      (weights : ∀ a ∈ footprint state.heap state.roots,
        cellBytes state.heap a ≤ bytes) :
      Run cells bytes headroom (closeScope state ∅) 0
  | work {state next : Session Owner Address Value World} {debt : Nat}
      (prior : Run cells bytes headroom state debt)
      (allocation : Allocation state.heap next.heap)
      (valid : ValidRoots next.heap next.roots)
      (capacity : debt + allocation.bytes ≤ headroom) :
      Run cells bytes headroom next (debt + allocation.bytes)
  | cancel {state : Session Owner Address Value World} {debt : Nat}
      (prior : Run cells bytes headroom state debt) (dead : Finset Owner) :
      Run cells bytes headroom (cancelOnly state dead) debt
  | publish {state : Session Owner Address Value World} {debt : Nat}
      (prior : Run cells bytes headroom state debt)
      (owner : Owner) (answers : List Address)
      (validAnswers : ∀ a ∈ answers, a ∈ state.heap.allocated) :
      Run cells bytes headroom (publishOnly state owner answers) debt
  | collect {state : Session Owner Address Value World} {debt : Nat}
      (prior : Run cells bytes headroom state debt) (dead : Finset Owner)
      (count : (footprint state.heap (cancel state.roots dead)).card ≤ cells)
      (weights : ∀ a ∈ footprint state.heap (cancel state.roots dead),
        cellBytes state.heap a ≤ bytes) :
      Run cells bytes headroom (closeScope state dead) 0

/-- Complete cancellation preserves validity of the retained root registry. -/
theorem valid_closeScope (state : Session Owner Address Value World)
    (dead : Finset Owner) (valid : ValidRoots state.heap state.roots) :
    ValidRoots (closeScope state dead).heap (closeScope state dead).roots := by
  intro pair member
  change pair.2 ∈ (collect state.heap (cancel state.roots dead)).allocated
  rw [allocated_collect, mem_footprint]
  exact live_of_root state.heap (cancel state.roots dead) member
    (valid pair ((mem_cancel state.roots dead pair).mp member).1)

/-- Every registered native/foreign/continuation/published root names allocated
storage. This rules out counting a dangling root as a harmless empty graph. -/
theorem run_valid_roots {cells bytes headroom debt : Nat}
    {state : Session Owner Address Value World}
    (run : Run cells bytes headroom state debt) :
    ValidRoots state.heap state.roots := by
  induction run with
  | initial state valid count weights => exact valid_closeScope state ∅ valid
  | work prior allocation valid capacity ih => exact valid
  | @cancel state debt prior dead ih =>
      intro pair member
      exact ih pair ((mem_cancel state.roots dead pair).mp member).1
  | @publish state debt prior owner answers validAnswers ih =>
      intro pair member
      rcases Finset.mem_union.mp member with old | answer
      · exact ih pair old
      · rcases pair with ⟨holder, a⟩
        exact validAnswers a ((mem_answerRoots owner holder answers a).mp answer).2
  | collect prior dead count weights ih => exact valid_closeScope _ dead ih

@[simp] theorem cancelOnly_world (state : Session Owner Address Value World)
    (dead : Finset Owner) : (cancelOnly state dead).world = state.world := rfl

@[simp] theorem publishOnly_world (state : Session Owner Address Value World)
    (owner : Owner) (answers : List Address) :
    (publishOnly state owner answers).world = state.world := rfl

/-- The same invariant applies to every finite prefix of a session. Collection
can occur at arbitrary times: no fixed bound on the number of events appears. -/
theorem run_accounting {cells bytes headroom debt : Nat}
    {state : Session Owner Address Value World}
    (run : Run cells bytes headroom state debt) :
    allocatedBytes state.heap ≤ cells * bytes + debt ∧ debt ≤ headroom := by
  induction run with
  | initial state valid count weights =>
      have empty : cancel state.roots ∅ = state.roots := by
        ext pair
        simp
      constructor
      · change allocatedBytes (collect state.heap (cancel state.roots ∅)) ≤ _
        rw [empty, allocatedBytes_collect, Nat.add_zero]
        exact retainedBytes_le state.heap state.roots _ _ count weights
      · exact Nat.zero_le _
  | @work state next debt prior allocation valid capacity ih =>
      constructor
      · rw [allocation.accounting]
        omega
      · exact capacity
  | cancel prior dead ih => exact ih
  | publish prior owner answers validAnswers ih => exact ih
  | @collect state debt prior dead count weights ih =>
      constructor
      · change allocatedBytes (collect state.heap (cancel state.roots dead)) ≤ _
        rw [allocatedBytes_collect, Nat.add_zero]
        exact retainedBytes_le state.heap (cancel state.roots dead) _ _ count weights
      · exact Nat.zero_le _

/-- Event-boundary peak, including an allocation immediately before collection.
The result is independent of interaction count; it includes uncollected debt. -/
theorem run_peak_bound {cells bytes headroom debt : Nat}
    {state : Session Owner Address Value World}
    (run : Run cells bytes headroom state debt) :
    allocatedBytes state.heap ≤ cells * bytes + headroom := by
  obtain ⟨account, capacity⟩ := run_accounting run
  omega

/-- The smaller bound holds just after collection, from the retained graph. -/
theorem after_collection_bound (state : Session Owner Address Value World)
    (dead : Finset Owner) (cells bytes : Nat)
    (count : (footprint state.heap (cancel state.roots dead)).card ≤ cells)
    (weights : ∀ a ∈ footprint state.heap (cancel state.roots dead),
      cellBytes state.heap a ≤ bytes) :
    allocatedBytes (closeScope state dead).heap ≤ cells * bytes := by
  change allocatedBytes (collect state.heap (cancel state.roots dead)) ≤ _
  rw [allocatedBytes_collect]
  exact retainedBytes_le state.heap (cancel state.roots dead) _ _ count weights

/-- A cancelled branch's private graph is reclaimed, including cyclic graphs,
when every owner that could reach the address is among those cancelled. -/
theorem cancel_reclaims_final_graph (state : Session Owner Address Value World)
    (dead : Finset Owner) (address : Address)
    (last : ∀ pair ∈ state.roots,
      Live state.heap {pair} address → pair.1 ∈ dead) :
    (closeScope state dead).heap.lookup address = none :=
  closeScope_reclaims_final_owner state dead address last

/-- Compiling the mathematical collector to the existing finite worklist
tracer retains exactly this same graph; the bound does not demand recursive
traversal or an unbounded enumeration of the address universe. -/
theorem traced_collection_bound {Node Payload : Type} [LinearOrder Node]
    (heap : Heap Node Payload) (roots : Roots Owner Node)
    (cells bytes : Nat) (count : (footprint heap roots).card ≤ cells)
    (weights : ∀ a ∈ footprint heap roots, cellBytes heap a ≤ bytes) :
    allocatedBytes (TraceWork.collectTraced heap roots) ≤ cells * bytes := by
  have same : allocatedBytes (TraceWork.collectTraced heap roots) =
      retainedBytes heap roots := by
    unfold allocatedBytes retainedBytes
    rw [TraceWork.collectTraced_allocated, allocated_collect]
    apply Finset.sum_congr rfl
    intro a member
    unfold cellBytes
    rw [TraceWork.collectTraced_lookup]
    exact congrArg (fun value => (value.map Cell.bytes).getD 0)
      (lookup_collect_of_live heap roots ((mem_footprint heap roots a).mp member))
  rw [same]
  exact retainedBytes_le heap roots _ _ count weights


/-- For the existing threshold schedule with a fixed persistent graph, the
charged full-tracing work is exact: one expansion per reachable cell per
collection. Allocation headroom is measured in one-byte transient cells in
that scheduling model. Root scanning, edge visits and set operations remain
separate costs; this does not prove that full tracing is always preferable. -/
theorem threshold_graph_work {Node Payload : Type} [LinearOrder Node]
    (heap : Heap Node Payload) (roots : Roots Owner Node)
    {headroom : Nat} (positive : 0 < headroom) (requests : Nat) :
    ResourceCollectionSchedule.tracingWork
      (TraceWork.trace heap roots).expanded.length
      (ResourceCollectionSchedule.run headroom requests) =
      (footprint heap roots).card * (requests / headroom) := by
  rw [ResourceCollectionSchedule.exact_work positive, TraceWork.trace_expansion_count]

/-- The threshold schedule amortizes full graph expansion over requests;
collecting on every interaction instead pays that entire graph each time. -/
theorem threshold_graph_amortized {Node Payload : Type} [LinearOrder Node]
    (heap : Heap Node Payload) (roots : Roots Owner Node)
    {headroom : Nat} (positive : 0 < headroom) (requests : Nat) :
    headroom * ResourceCollectionSchedule.tracingWork
      (TraceWork.trace heap roots).expanded.length
      (ResourceCollectionSchedule.run headroom requests) ≤
      (footprint heap roots).card * requests := by
  rw [TraceWork.trace_expansion_count]
  exact ResourceCollectionSchedule.amortized_work positive _ requests


namespace Controls

/-- Independent one-byte resources make a concrete repeated-session control. -/
def flatHeap (cells : Finset Nat) : Heap Nat Unit where
  lookup a := if a ∈ cells then some ⟨(), ∅, 1⟩ else none
  allocated := cells
  allocated_iff a := by
    by_cases member : a ∈ cells <;> simp [member]
  closed := by
    intro a cell found b edge
    split at found
    · cases found
      simp at edge
    · cases found

theorem flat_live (cells : Finset Nat) (roots : Roots Owner Nat) (a : Nat) :
    Live (flatHeap cells) roots a ↔ a ∈ cells ∧ a ∈ rootAddresses roots := by
  constructor
  · intro live
    induction live with
    | root rooted => exact rooted
    | @step a b prior edge ih =>
        obtain ⟨cell, found, edge⟩ := edge
        change (if a ∈ cells then some ⟨(), ∅, 1⟩ else none) = some cell at found
        split at found
        · cases found
          simp at edge
        · cases found
  · intro rooted
    exact .root rooted

theorem flat_footprint (cells : Finset Nat) (roots : Roots Owner Nat) :
    footprint (flatHeap cells) roots = cells ∩ rootAddresses roots := by
  ext a
  simp only [mem_footprint, flat_live, Finset.mem_inter]

theorem flat_bytes (cells : Finset Nat) {a : Nat} (member : a ∈ cells) :
    cellBytes (flatHeap cells) a = 1 := by
  simp [cellBytes, flatHeap, member]

theorem flat_allocated (cells : Finset Nat) :
    allocatedBytes (flatHeap cells) = cells.card := by
  unfold allocatedBytes
  change ∑ a ∈ cells, cellBytes (flatHeap cells) a = cells.card
  calc
    _ = ∑ _a ∈ cells, 1 := Finset.sum_congr rfl (fun _ member => flat_bytes cells member)
    _ = _ := by simp

theorem flat_retained (cells : Finset Nat) (roots : Roots Owner Nat) :
    retainedBytes (flatHeap cells) roots = (cells ∩ rootAddresses roots).card := by
  unfold retainedBytes
  rw [flat_footprint]
  calc
    _ = ∑ _a ∈ cells ∩ rootAddresses roots, 1 := by
      apply Finset.sum_congr rfl
      intro a member
      exact flat_bytes cells (Finset.mem_inter.mp member).1
    _ = _ := by simp

private theorem heap_ext {left right : Heap Nat Unit}
    (lookup : left.lookup = right.lookup) (allocated : left.allocated = right.allocated) :
    left = right := by
  cases left
  cases right
  cases lookup
  cases allocated
  rfl

private theorem session_ext {left right : Session Owner Nat Unit Nat}
    (heap : left.heap = right.heap) (roots : left.roots = right.roots)
    (world : left.world = right.world) : left = right := by
  cases left
  cases right
  cases heap
  cases roots
  cases world
  rfl

/-- A long-lived native value and a completed-interaction counter. -/
def ready (n : Nat) : Session Owner Nat Unit Nat :=
  ⟨flatHeap {0}, {(Owner.native 0, 0)}, n⟩

/-- Each interaction acquires a foreign resource with a distinct holder id.
The previous interaction's address can be reused after reclamation. -/
def busy (n : Nat) : Session Owner Nat Unit Nat :=
  ⟨flatHeap {0, 1}, {(Owner.native 0, 0), (Owner.foreign n, 1)}, n + 1⟩

theorem busy_cancel_roots (n : Nat) :
    cancel (busy n).roots {Owner.foreign n} = (ready (n + 1)).roots := by
  ext pair
  rcases pair with ⟨owner, address⟩
  simp only [busy, ready, mem_cancel, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), surviving⟩
    · exact ⟨rfl, rfl⟩
    · exact False.elim (surviving rfl)
  · rintro ⟨rfl, rfl⟩
    exact ⟨Or.inl ⟨rfl, rfl⟩, by simp⟩

theorem close_busy (n : Nat) :
    closeScope (busy n) {Owner.foreign n} = ready (n + 1) := by
  apply session_ext
  · apply heap_ext
    · funext a
      change (collect (flatHeap {0, 1}) (cancel (busy n).roots {Owner.foreign n})).lookup a = _
      rw [busy_cancel_roots]
      by_cases zero : a = 0
      · subst a
        rw [lookup_collect_of_live]
        · simp [ready, flatHeap]
        · rw [flat_live]
          simp [ready, rootAddresses]
      · rw [lookup_collect_of_not_live]
        · simp [ready, flatHeap, zero]
        · rw [flat_live]
          simp [ready, rootAddresses, zero]
    · change footprint (flatHeap {0, 1}) (cancel (busy n).roots {Owner.foreign n}) = {0}
      rw [busy_cancel_roots, flat_footprint]
      simp [ready, rootAddresses]
  · exact busy_cancel_roots n
  · rfl

def interactionAllocation (n : Nat) : Allocation (ready n).heap (busy n).heap where
  fresh := {1}
  disjoint := by simp [ready, flatHeap]
  domain := by simp [busy, ready, flatHeap]
  oldBytes := by
    intro a member
    have zero : a = 0 := by simpa [ready, flatHeap] using member
    subst a
    simp [ready, busy, cellBytes, flatHeap]

theorem interaction_bytes (n : Nat) : (interactionAllocation n).bytes = 1 := by
  simp [Allocation.bytes, interactionAllocation, busy, cellBytes, flatHeap]

theorem ready_compact (n : Nat) : closeScope (ready n) ∅ = ready n := by
  apply session_ext
  · apply heap_ext
    · funext a
      change (collect (flatHeap {0}) (cancel (ready n).roots ∅)).lookup a = _
      have roots : cancel (ready n).roots ∅ = (ready n).roots := by ext pair; simp
      rw [roots]
      by_cases zero : a = 0
      · subst a
        rw [lookup_collect_of_live]
        · rfl
        · rw [flat_live]
          simp [ready, rootAddresses]
      · rw [lookup_collect_of_not_live]
        · simp [ready, flatHeap, zero]
        · rw [flat_live]
          simp [ready, rootAddresses, zero]
    · change footprint (flatHeap {0}) (cancel (ready n).roots ∅) = {0}
      rw [flat_footprint]
      simp [ready, rootAddresses, cancel]
  · ext pair
    simp [closeScope]
  · rfl

/-- Constructively perform arbitrarily many allocations and foreign releases.
The semantic world records progress; storage does not grow with that count. -/
theorem repeated_interactions (n : Nat) : Run 1 1 1 (ready n) 0 := by
  induction n with
  | zero =>
      rw [← ready_compact 0]
      apply Run.initial
      · intro pair member
        have same : pair = (Owner.native 0, 0) := Finset.mem_singleton.mp member
        rw [same]
        simp [ready, flatHeap]
      · simp [ready, flat_footprint, rootAddresses]
      · intro a member
        have inside := live_allocated _ _ ((mem_footprint _ _ a).mp member)
        exact le_of_eq (flat_bytes {0} inside)
  | succ n ih =>
      have during : Run 1 1 1 (busy n) 1 := by
        have valid : ValidRoots (busy n).heap (busy n).roots := by
          intro pair member
          rcases pair with ⟨owner, a⟩
          simp only [busy, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at member
          rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [busy, flatHeap]
        have step := Run.work ih (interactionAllocation n) valid (by simp [interaction_bytes])
        simpa only [interaction_bytes, Nat.zero_add] using step
      rw [← close_busy n]
      apply Run.collect during {Owner.foreign n}
      · rw [busy_cancel_roots]
        simp [busy, flat_footprint, ready, rootAddresses]
      · intro a member
        have inside := live_allocated _ _ ((mem_footprint _ _ a).mp member)
        exact le_of_eq (flat_bytes {0, 1} inside)

/-- Both the active peak and settled storage are exact for every interaction. -/
theorem repeated_interaction_storage (n : Nat) :
    Run 1 1 1 (ready n) 0 ∧ allocatedBytes (ready n).heap = 1 ∧
      allocatedBytes (busy n).heap = 2 := by
  exact ⟨repeated_interactions n, by simp [ready, flat_allocated],
    by simp [busy, flat_allocated]⟩

/-- One forgotten foreign handle per interaction roots one extra live byte. -/
def leakedRoots (n : Nat) : Roots Owner Nat :=
  (Finset.range n).image (fun a => (Owner.foreign a, a))

theorem leaked_root_addresses (n : Nat) : rootAddresses (leakedRoots n) = Finset.range n := by
  simp only [rootAddresses, leakedRoots, Finset.image_image]
  exact Finset.image_id

theorem collecting_cannot_reclaim_leaked_foreign_handles (n : Nat) :
    allocatedBytes (collect (flatHeap (Finset.range n)) (leakedRoots n)) = n := by
  rw [allocatedBytes_collect, flat_retained, leaked_root_addresses, Finset.inter_self,
    Finset.card_range]

/-- A collector alone cannot fix the retained foreign-root lifecycle error. -/
theorem leaked_foreign_handles_unbounded (bound : Nat) :
    bound < allocatedBytes
      (collect (flatHeap (Finset.range (bound + 1))) (leakedRoots (bound + 1))) := by
  rw [collecting_cannot_reclaim_leaked_foreign_handles]
  omega


/-- Native and foreign holders share a cyclic graph. -/
def sharedCycle : Session Owner (Fin 3) Nat Unit :=
  ⟨ResourceOwnership.Examples.cyclicHeap,
    {(Owner.native 0, 0), (Owner.foreign 0, 2)}, ()⟩

/-- Cancelling the native owner cannot reclaim the cycle still held abroad. -/
theorem foreign_hold_keeps_cycle :
    (closeScope sharedCycle {Owner.native 0}).heap.lookup 1 =
      some (ResourceOwnership.Examples.cyclicCell 1) := by
  apply lookup_collect_of_live
  have atTwo : Live sharedCycle.heap
      (cancel sharedCycle.roots {Owner.native 0}) 2 :=
    live_of_root _ _ (owner := Owner.foreign 0) (by decide) (by decide)
  exact live_step _ _ atTwo rfl (by decide)

/-- Once both holders are cancelled, cycles require no special exception. -/
theorem final_release_reclaims_cycle (a : Fin 3) :
    (closeScope sharedCycle {Owner.native 0, Owner.foreign 0}).heap.lookup a = none := by
  change (collect sharedCycle.heap
    (cancel sharedCycle.roots {Owner.native 0, Owner.foreign 0})).lookup a = none
  have roots : cancel sharedCycle.roots {Owner.native 0, Owner.foreign 0} = ∅ := by decide
  rw [roots, lookup_collect_none_iff]
  exact not_live_empty _ _

/-- Exporting an answer before cancellation keeps its shared cyclic graph. -/
theorem published_answer_keeps_cycle :
    (commit sharedCycle {Owner.native 0, Owner.foreign 0}
      (Owner.published 0) [1]).heap.lookup 1 =
      some (ResourceOwnership.Examples.cyclicCell 1) := by
  apply commit_preserves_answer_graph
  · decide
  · exact live_of_root _ _ (owner := Owner.published 0) (by decide) (by decide)

/-- Bounding the holder count is also insufficient: one holder can retain an
arbitrarily large transitive chain. This is the existing graph counterexample. -/
theorem one_root_is_not_a_space_bound (bound : Nat) :
    ∃ (heap : Heap Nat Nat) (roots : Roots Unit Nat),
      roots.card = 1 ∧ bound < retainedBytes heap roots :=
  ResourceOwnership.Examples.one_root_unbounded bound

end Controls

end Mettapedia.Machines.IncrementalConformance.LiveResources
