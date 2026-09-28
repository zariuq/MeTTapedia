import Mettapedia.Machines.ResourceOwnership

/-!
# Exact tracing minimizes retained cells under complete path observations

The observation class consists of every finite `walk` starting at a valid
source root, including failed walks and complete endpoint cells. A reachable
cell has a successful finite root-path witness, proved by induction on the
existing reachability derivation. Consequently any candidate heap with the
same observations must retain that very cell at that very address.

The exact tracing collector attains the resulting lower bounds on allocated
cell count and declared bytes. This is a storage optimum for fixed-address,
full-cell observations. It is not an optimum for moving or compressing heaps,
recomputation, physical allocator overhead, collection time, or unrestricted
program contexts. A different observation or realization class needs its own
comparison. Each current allocation set is finite; the address universe need
not be finite and no future growth bound is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceOwnership.Optimality

universe uValue uOwner

variable {Address : Type} {Value : Type uValue} {Owner : Type uOwner}
  [DecidableEq Address]

/-- A successful finite walk necessarily observes the actual endpoint lookup. -/
theorem walk_success_lookup (heap : Heap Address Value) (path : List Address)
    {start endpoint : Address} {cell : Cell Address Value}
    (success : walk heap start path = some (endpoint, cell)) :
    heap.lookup endpoint = some cell := by
  induction path generalizing start with
  | nil =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact found
  | cons next rest ih =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.bind_some] at success
          split at success
          next _ => exact ih success
          next _ => cases success

/-- Following a successful prefix continues from its observed endpoint. -/
theorem walk_append_of_success (heap : Heap Address Value) (path suffix : List Address)
    {start endpoint : Address} {cell : Cell Address Value}
    (success : walk heap start path = some (endpoint, cell)) :
    walk heap start (path ++ suffix) = walk heap endpoint suffix := by
  induction path generalizing start with
  | nil =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          rfl
  | cons next rest ih =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.bind_some] at success
          split at success
          next reference =>
            simpa only [List.cons_append, walk, found, Option.bind_some, if_pos reference] using
              ih success
          next _ => cases success

/-- Every reachable resource has a finite successful path from an actual,
allocated owner-root. Shared graphs and cycles need no acyclicity premise. -/
theorem live_path_witness (heap : Heap Address Value) (roots : Roots Owner Address)
    {address : Address} (live : Live heap roots address) :
    ∃ pair ∈ roots, pair.2 ∈ heap.allocated ∧
      ∃ path cell, walk heap pair.2 path = some (address, cell) := by
  induction live with
  | @root address rooted =>
      obtain ⟨pair, member, same⟩ := Finset.mem_image.mp rooted.2
      obtain ⟨cell, found⟩ := (heap.allocated_iff address).mp rooted.1
      refine ⟨pair, member, same.symm ▸ rooted.1, [], cell, ?_⟩
      simp only [walk, same, found, Option.map_some]
  | @step previous address prior edge ih =>
      obtain ⟨pair, member, valid, path, previousCell, reached⟩ := ih
      obtain ⟨edgeCell, found, reference⟩ := edge
      obtain ⟨cell, atAddress⟩ := (heap.allocated_iff address).mp
        (heap.closed previous edgeCell found address reference)
      refine ⟨pair, member, valid, path ++ [address], cell, ?_⟩
      rw [walk_append_of_success heap path [address] reached]
      simp only [walk, found, Option.bind_some, if_pos reference, atAddress, Option.map_some]

/-- All finite path observations at source-valid roots are equal. Invalid
source root addresses are not capabilities to newly allocated candidate cells. -/
def SameRootPaths (source candidate : Heap Address Value) (roots : Roots Owner Address) : Prop :=
  ∀ pair ∈ roots, pair.2 ∈ source.allocated → ∀ path,
    walk candidate pair.2 path = walk source pair.2 path

/-- Complete path observations force full lookup equality at every live
address. Retention is the conclusion, not a premise of the comparison. -/
theorem live_cell_forced (source candidate : Heap Address Value) (roots : Roots Owner Address)
    (observations : SameRootPaths source candidate roots) {address : Address}
    (live : Live source roots address) : candidate.lookup address = source.lookup address := by
  obtain ⟨pair, member, valid, path, cell, reached⟩ := live_path_witness source roots live
  have sourceLookup := walk_success_lookup source path reached
  have candidateLookup := walk_success_lookup candidate path
    ((observations pair member valid path).trans reached)
  exact candidateLookup.trans sourceLookup.symm

/-- Any observationally equivalent fixed-address heap allocates the entire
transitive source footprint, including shared or cyclic descendants. -/
theorem footprint_subset_candidate (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    footprint source roots ⊆ candidate.allocated := by
  intro address member
  have live := (mem_footprint source roots address).mp member
  obtain ⟨cell, found⟩ := (source.allocated_iff address).mp (live_allocated source roots live)
  exact (candidate.allocated_iff address).mpr
    ⟨cell, (live_cell_forced source candidate roots observations live).trans found⟩

theorem retained_cells_le (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    (footprint source roots).card ≤ candidate.allocated.card :=
  Finset.card_le_card (footprint_subset_candidate source candidate roots observations)

/-- Full-cell equality includes the declared byte weight, so extra candidate
allocations cannot reduce the cost of the cells forced by root observations. -/
theorem retained_bytes_le (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    retainedBytes source roots ≤ allocatedBytes candidate := by
  calc
    retainedBytes source roots = ∑ address ∈ footprint source roots, cellBytes candidate address := by
      apply Finset.sum_congr rfl
      intro address member
      simp only [cellBytes, live_cell_forced source candidate roots observations
        ((mem_footprint source roots address).mp member)]
    _ ≤ allocatedBytes candidate :=
      Finset.sum_le_sum_of_subset (footprint_subset_candidate source candidate roots observations)

/-- Exact tracing belongs to the comparison class: all successful and failed
root paths retain their full observations. -/
theorem collect_same_root_paths (source : Heap Address Value) (roots : Roots Owner Address) :
    SameRootPaths source (collect source roots) roots := by
  intro pair member valid path
  exact walk_collect source roots (live_of_root source roots member valid) path

/-- Exact tracing attains the minimum number of allocated cells. -/
theorem collect_minimal_cells (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    (collect source roots).allocated.card ≤ candidate.allocated.card :=
  retained_cells_le source candidate roots observations

/-- Exact tracing attains the minimum declared allocation bytes. -/
theorem collect_minimal_bytes (source candidate : Heap Address Value)
    (roots : Roots Owner Address) (observations : SameRootPaths source candidate roots) :
    allocatedBytes (collect source roots) ≤ allocatedBytes candidate := by
  rw [allocatedBytes_collect]
  exact retained_bytes_le source candidate roots observations

/-- The admissible collector and both lower bounds are stated together; no
runtime or alternative representation optimum is implied. -/
theorem collect_attains_minimum (source : Heap Address Value) (roots : Roots Owner Address) :
    SameRootPaths source (collect source roots) roots ∧
      ∀ candidate, SameRootPaths source candidate roots →
        (collect source roots).allocated.card ≤ candidate.allocated.card ∧
          allocatedBytes (collect source roots) ≤ allocatedBytes candidate := by
  refine ⟨collect_same_root_paths source roots, ?_⟩
  intro candidate observations
  exact ⟨collect_minimal_cells source candidate roots observations,
    collect_minimal_bytes source candidate roots observations⟩

/-! ## Shared cycles and insufficient observation controls -/

namespace Controls

open Examples

/-- Two owners share opposite nodes of the same cycle. Node zero is garbage. -/
def cycleRoots : Roots Nat (Fin 3) := {(0, 1), (1, 2)}

theorem cycle_not_zero {address : Fin 3} (live : Live cyclicHeap cycleRoots address) :
    address ≠ 0 := by
  induction live with
  | @root address rooted =>
      have rootAddress : address = 1 ∨ address = 2 := by
        simpa [Heap.toStore, rootAddresses, cycleRoots] using rooted.2
      rcases rootAddress with rfl | rfl <;> decide
  | @step previous address _ edge _ =>
      obtain ⟨cell, found, reference⟩ := edge
      change some (cyclicCell previous) = some cell at found
      cases found
      by_cases zero : previous = 0
      · have same : address = 1 := by simpa [cyclicCell, zero] using reference
        simp [same]
      · by_cases one : previous = 1
        · have same : address = 2 := by simpa [cyclicCell, zero, one] using reference
          simp [same]
        · have same : address = 1 := by simpa [cyclicCell, zero, one] using reference
          simp [same]

theorem cycle_footprint : footprint cyclicHeap cycleRoots = {1, 2} := by
  ext address
  rw [mem_footprint]
  constructor
  · intro live
    have different := cycle_not_zero live
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro member
    rcases Finset.mem_insert.mp member with rfl | member
    · exact live_of_root cyclicHeap cycleRoots (owner := 0) (by decide) (by decide)
    · have same : address = 2 := Finset.mem_singleton.mp member
      subst address
      exact live_of_root cyclicHeap cycleRoots (owner := 1) (by decide) (by decide)

theorem cycle_minimum_is_two_cells_and_32_bytes :
    (collect cyclicHeap cycleRoots).allocated.card = 2 ∧
      allocatedBytes (collect cyclicHeap cycleRoots) = 32 := by
  constructor
  · rw [allocated_collect, cycle_footprint]
    decide
  · rw [allocatedBytes_collect]
    unfold retainedBytes
    rw [cycle_footprint]
    decide

theorem every_same_cycle_observer_pays (candidate : Heap (Fin 3) Nat)
    (observations : SameRootPaths cyclicHeap candidate cycleRoots) :
    2 ≤ candidate.allocated.card ∧ 32 ≤ allocatedBytes candidate := by
  simpa only [cycle_minimum_is_two_cells_and_32_bytes.1,
    cycle_minimum_is_two_cells_and_32_bytes.2] using
    (collect_attains_minimum cyclicHeap cycleRoots).2 candidate observations

/-- A root-only payload observer cannot see that the root's outgoing edge
was deleted and its descendant was discarded. The candidate is still closed. -/
def isolatedRoot : Heap Nat Nat where
  lookup address := if address = 0 then some ⟨0, ∅, 1⟩ else none
  allocated := {0}
  allocated_iff address := by
    by_cases same : address = 0 <;> simp [same]
  closed address cell found next reference := by
    split at found
    next _ => cases found; simp at reference
    next _ => cases found

theorem root_payload_is_insufficient :
    ((Examples.chainHeap 1).lookup 0).map Cell.value =
        (isolatedRoot.lookup 0).map Cell.value ∧
      isolatedRoot.allocated.card < (footprint (Examples.chainHeap 1) Examples.oneRoot).card ∧
      walk isolatedRoot 0 [1] ≠ walk (Examples.chainHeap 1) 0 [1] := by
  rw [Examples.chain_footprint]
  decide

theorem missing_descendant_rejects_candidate :
    ¬ SameRootPaths (Examples.chainHeap 1) isolatedRoot Examples.oneRoot := by
  intro observations
  have same := observations ((), 0) (by decide) (by decide) [1]
  exact root_payload_is_insufficient.2.2 same

end Controls

end Mettapedia.Machines.ResourceOwnership.Optimality
