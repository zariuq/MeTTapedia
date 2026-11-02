import Mettapedia.Machines.RegionReadStability

/-!
# Necessary information for retained-handle read regions

Every live allocation has a finite path witness from a retained root. A
client that may inspect complete cells along all such paths can distinguish
removal or modification of any live cell. Empty root lookups are observable
too. Consequently the existing local rely condition is both necessary and
sufficient for this future-path observer.

Collection attains the least allocation set among address-faithful heaps
with these observations, and the least sum of the retained cell weights.
This is relative to the existing heap/cell representation and observer. It
does not prove minimum physical bytes under compression, relocation,
recomputation, or a weaker observation contract.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RegionReadInformation

open ResourceOwnership RegionReadCollection RegionReadStability

variable {Address Value Owner : Type} [DecidableEq Address]

/-- Reachability supplies an actual complete path observation, including
the endpoint address and cell, even in shared or cyclic graphs. -/
theorem live_has_path (heap : Heap Address Value) (roots : Roots Owner Address)
    (address : Address) (live : Live heap roots address) :
    ∃ start ∈ rootAddresses roots, ∃ path cell, walk heap start path = some (address, cell) := by
  induction live with
  | @root address rooted =>
      obtain ⟨cell, found⟩ := (heap.allocated_iff address).mp rooted.1
      exact ⟨address, rooted.2, [], cell, by simp [walk, found]⟩
  | @step parent child _ edge ih =>
      obtain ⟨parentCell, parentFound, reference⟩ := edge
      obtain ⟨start, root, path, oldCell, walked⟩ := ih
      obtain ⟨childCell, childFound⟩ := (heap.allocated_iff child).mp
        (heap.closed parent parentCell parentFound child reference)
      refine ⟨start, root, path ++ [child], childCell, ?_⟩
      rw [walk_append_of_success heap path [child] walked]
      simp [walk, parentFound, reference, childFound]

theorem registry_addresses (state : State Address Value) :
    rootAddresses state.registry = state.roots.toFinset := by
  simp [State.registry, rootAddresses, Finset.image_image, Function.comp_def]

theorem agreement_preserves_live_lookup (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) (address : Address) (live : Live before state.registry address) :
    after.lookup address = before.lookup address := by
  obtain ⟨start, root, path, cell, walked⟩ := live_has_path before state.registry address live
  have rootMember : start ∈ state.roots := by simpa only [registry_addresses, List.mem_toFinset] using root
  have afterWalk := (agree start rootMember path).trans walked
  exact (walk_success_lookup after path afterWalk).trans (walk_success_lookup before path walked).symm

theorem agreement_preserves_root_lookup (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) (address : Address) (root : address ∈ state.roots) :
    after.lookup address = before.lookup address := by
  have compared := agree address root []
  cases first : before.lookup address <;> cases second : after.lookup address <;>
    simp_all [walk]

theorem agreement_implies_rely (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) : Rely before after state := by
  intro address needed
  rcases Finset.mem_union.mp needed with live | root
  · exact agreement_preserves_live_lookup before after state agree address
      ((mem_footprint before state.registry address).mp live)
  · exact agreement_preserves_root_lookup before after state agree address (List.mem_toFinset.mp root)

/-- The dependency footprint includes negative roots, not merely allocated
cells. This characterizes the already declared complete future-path observer. -/
theorem agreement_iff_rely (before after : Heap Address Value) (state : State Address Value) :
    AgreesAt before after state ↔ Rely before after state :=
  ⟨agreement_implies_rely before after state, rely_implies_agrees before after state⟩

theorem agreement_symm (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) : AgreesAt after before state :=
  fun address member path => (agree address member path).symm

theorem agreement_trans (first middle last : Heap Address Value) (state : State Address Value)
    (earlier : AgreesAt first middle state) (later : AgreesAt middle last state) :
    AgreesAt first last state := fun address member path =>
  (later address member path).trans (earlier address member path)

theorem required_allocations (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) : footprint before state.registry ⊆ after.allocated := by
  intro address member
  have live := (mem_footprint before state.registry address).mp member
  obtain ⟨cell, found⟩ := (before.allocated_iff address).mp (live_allocated before state.registry live)
  apply (after.allocated_iff address).mpr
  exact ⟨cell, (agreement_preserves_live_lookup before after state agree address live).trans found⟩

theorem collected_allocation_minimal (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) :
    (collect before state.registry).allocated ⊆ after.allocated := required_allocations before after state agree

theorem collected_count_minimal (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) :
    (collect before state.registry).allocated.card ≤ after.allocated.card :=
  Finset.card_le_card (collected_allocation_minimal before after state agree)

theorem agreement_preserves_footprint (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) : footprint before state.registry = footprint after state.registry := by
  apply Finset.Subset.antisymm
  · exact required_allocations before (collect after state.registry) state
      (agreement_trans before after _ state agree (collect_agrees after state))
  · exact required_allocations after (collect before state.registry) state
      (agreement_trans after before _ state (agreement_symm before after state agree) (collect_agrees before state))

theorem agreement_preserves_collected_lookup (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) :
    (collect after state.registry).lookup = (collect before state.registry).lookup := by
  have footprints := agreement_preserves_footprint before after state agree
  funext address
  by_cases live : Live before state.registry address
  · have afterLive : Live after state.registry address := by
      rw [← mem_footprint, ← footprints, mem_footprint]
      exact live
    rw [lookup_collect_of_live after state.registry afterLive, lookup_collect_of_live before state.registry live]
    exact agreement_preserves_live_lookup before after state agree address live
  · have afterDead : ¬Live after state.registry address := by
      intro afterLive
      apply live
      apply (mem_footprint before state.registry address).mp
      rw [footprints]
      exact (mem_footprint after state.registry address).mpr afterLive
    rw [lookup_collect_of_not_live before state.registry live, lookup_collect_of_not_live after state.registry afterDead]

theorem walk_of_lookup_eq (before after : Heap Address Value) (same : after.lookup = before.lookup)
    (address : Address) (path : List Address) : walk after address path = walk before address path := by
  induction path generalizing address with
  | nil => simp [walk, same]
  | cons child rest ih => simp only [walk, same, ih]

/-- The collected lookup is a canonical representative of exactly this
future-path observation, including absent root lookups. -/
theorem collected_lookup_exact (before after : Heap Address Value) (state : State Address Value) :
    (collect after state.registry).lookup = (collect before state.registry).lookup ↔ AgreesAt before after state := by
  constructor
  · intro same address member path
    calc
      walk after address path = walk (collect after state.registry) address path :=
        (collect_agrees after state address member path).symm
      _ = walk (collect before state.registry) address path := walk_of_lookup_eq _ _ same address path
      _ = walk before address path := collect_agrees before state address member path
  · exact agreement_preserves_collected_lookup before after state

/-- Cell weights are retained by this full-cell observer. Root tables,
allocator metadata and alternative representations are not charged here. -/
theorem collected_weight_minimal (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) :
    allocatedBytes (collect before state.registry) ≤ allocatedBytes after := by
  rw [allocatedBytes_collect]
  calc
    retainedBytes before state.registry = ∑ address ∈ footprint before state.registry, cellBytes after address := by
      apply Finset.sum_congr rfl
      intro address member
      rw [cellBytes, cellBytes,
        agreement_preserves_live_lookup before after state agree address
          ((mem_footprint before state.registry address).mp member)]
    _ ≤ allocatedBytes after := Finset.sum_le_sum_of_subset (required_allocations before after state agree)

theorem removing_live_cell_changes_a_future (before after : Heap Address Value) (state : State Address Value)
    (address : Address) (live : Live before state.registry address) (removed : after.lookup address = none) :
    ¬AgreesAt before after state := by
  intro agree
  obtain ⟨cell, found⟩ := (before.allocated_iff address).mp (live_allocated before state.registry live)
  have same := agreement_preserves_live_lookup before after state agree address live
  rw [removed, found] at same
  cases same

namespace Controls

open ResourceOwnership.Examples

def reader : State (Fin 3) Nat := ⟨[.read 1 [2]], [], []⟩

theorem reachable_cycle_survives_minimal_collection :
    AgreesAt cyclicHeap (collect cyclicHeap reader.registry) reader := collect_agrees cyclicHeap reader

theorem live_footprint_is_only_the_cycle : footprint cyclicHeap reader.registry = {1, 2} := by
  rw [← census_eq_footprint cyclicHeap reader.registry (fun pair _ => Finset.mem_univ pair.2)]
  decide +kernel

theorem collection_really_removes_an_allocation :
    (collect cyclicHeap reader.registry).allocated.card = 2 ∧ cyclicHeap.allocated.card = 3 := by
  change (footprint cyclicHeap reader.registry).card = 2 ∧ _
  rw [live_footprint_is_only_the_cycle]
  decide +kernel

theorem retained_cell_weight_is_thirty_two :
    allocatedBytes (collect cyclicHeap reader.registry) = 32 := by
  rw [allocatedBytes_collect, retainedBytes, live_footprint_is_only_the_cycle]
  decide +kernel

theorem changed_reachable_payload_is_observable :
    ¬AgreesAt cyclicHeap (cyclicHeap.writePayload 2 99) reader := by
  intro agree
  have future := agree 1 (by simp [State.roots, reader, Task.roots]) [2]
  have distinct : walk (cyclicHeap.writePayload 2 99) 1 [2] ≠ walk cyclicHeap 1 [2] := by decide +kernel
  exact distinct future

theorem same_current_answer_is_weaker_than_future_agreement :
    (run (cyclicHeap.writePayload 1 99) 1 reader).answers = (run cyclicHeap 1 reader).answers ∧
      ¬AgreesAt cyclicHeap (cyclicHeap.writePayload 1 99) reader := by
  constructor
  · decide +kernel
  · intro agree
    have root := agreement_preserves_root_lookup cyclicHeap (cyclicHeap.writePayload 1 99) reader agree 1
      (by simp [State.roots, reader, Task.roots])
    have different : (cyclicHeap.writePayload 1 99).lookup 1 ≠ cyclicHeap.lookup 1 := by decide +kernel
    exact different root

theorem absent_root_remains_information :
    ¬AgreesAt RegionReadStability.Controls.absentHeap RegionReadStability.Controls.allocatedHeap
      RegionReadStability.Controls.absentReader := by
  intro agree
  have root := agreement_preserves_root_lookup _ _ _ agree 0 (by decide)
  cases root

end Controls

end Mettapedia.Machines.RegionReadInformation
