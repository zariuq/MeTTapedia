import Mettapedia.Machines.RegionReadCollection
import Mettapedia.Machines.RegionReadStability
import Mettapedia.Machines.ResourceOwnershipOptimality

/-! Nested pending reads, returned handles, fallback inputs, cycles and
missing-root controls for operation-level collection. -/

set_option autoImplicit false

namespace Mettapedia.Machines.RegionReadCollection.Controls

open ResourceOwnership ResourceOwnership.Examples

def nested : State (Fin 3) Nat :=
  ⟨[.sequence (.read 1 [2, 1]) (.read 2 [])], [], []⟩

theorem both_nested_sides_are_rooted : nested.roots = [1, 2] := rfl

theorem reference_visits_the_cycle_in_order :
    (run cyclicHeap 3 nested).answers = [some (1, cyclicCell 1), some (2, cyclicCell 2)] ∧
      (run cyclicHeap 3 nested).pending = [] := by decide +kernel

theorem every_operation_can_collect (policy : Nat → Bool) :
    (runHeap policy cyclicHeap 3 nested).2.answers =
      [some (1, cyclicCell 1), some (2, cyclicCell 2)] := by
  rw [(heap_run_preserves_future policy cyclicHeap 3 nested).1]
  exact reference_visits_the_cycle_in_order.1

theorem actual_post_collection_heap_can_resume :
    let page := runHeap (fun _ => true) cyclicHeap 2 nested
    (runHeap (fun _ => true) page.1 1 page.2).2.answers =
      [some (1, cyclicCell 1), some (2, cyclicCell 2)] := by
  have exactPage := resumed_collected_heap_exact (fun _ => true) (fun _ => true) cyclicHeap 2 1 nested
  exact congrArg State.answers exactPage |>.trans reference_visits_the_cycle_in_order.1

theorem footprint_is_shared_not_duplicated : footprint cyclicHeap nested.registry = {1, 2} := by
  have same : rootAddresses nested.registry = rootAddresses Optimality.Controls.cycleRoots := by decide
  have stores : cyclicHeap.toStore nested.registry = cyclicHeap.toStore Optimality.Controls.cycleRoots := by
    simp only [Heap.toStore, same]
  have footprints : footprint cyclicHeap nested.registry = footprint cyclicHeap Optimality.Controls.cycleRoots := by
    ext address
    simp only [mem_footprint, Live, stores]
  exact footprints.trans Optimality.Controls.cycle_footprint

theorem operation_collection_removes_the_unreachable_head :
    (collect cyclicHeap nested.registry).allocated = {1, 2} := footprint_is_shared_not_duplicated

theorem returned_endpoints_remain_roots : (run cyclicHeap 3 nested).roots = [1, 2] := by decide +kernel

theorem returned_handle_allows_later_cycle_reads (policy : Nat → Bool) :
    walk (runHeap policy cyclicHeap 3 nested).1 1 [2, 1] = some (1, cyclicCell 1) := by
  have receipt := heap_run_preserves_future policy cyclicHeap 3 nested
  have member : (1 : Fin 3) ∈ (runHeap policy cyclicHeap 3 nested).2.roots := by
    rw [receipt.1, returned_endpoints_remain_roots]
    decide
  rw [receipt.2 1 member [2, 1]]
  decide +kernel

def fallbackOnly : State (Fin 3) Nat := ⟨[], [0], []⟩

theorem fallback_inputs_are_not_discarded (path : List (Fin 3)) :
    walk (collect cyclicHeap fallbackOnly.registry) 0 path = walk cyclicHeap 0 path :=
  collect_agrees cyclicHeap fallbackOnly 0 (by decide) path

def invalidEdge : State (Fin 3) Nat := ⟨[.read 1 [0]], [], []⟩

theorem a_path_label_is_not_a_root_capability :
    (0 : Fin 3) ∉ invalidEdge.roots ∧ (run cyclicHeap 1 invalidEdge).answers = [none] := by decide +kernel

theorem omitting_pending_roots_changes_the_answer :
    (run (collect cyclicHeap (∅ : Roots Unit (Fin 3))) 3 nested).answers ≠
      (run cyclicHeap 3 nested).answers := by
  have missing (address : Fin 3) : (collect cyclicHeap (∅ : Roots Unit (Fin 3))).lookup address = none :=
    lookup_collect_of_not_live cyclicHeap ∅ (not_live_empty cyclicHeap address)
  have wrong : (run (collect cyclicHeap (∅ : Roots Unit (Fin 3))) 3 nested).answers = [none, none] := by
    simp [run, step, nested, walk, missing]
  rw [wrong, reference_visits_the_cycle_in_order.1]
  decide

theorem a_zero_page_is_not_exhaustion :
    (runHeap (fun _ => true) cyclicHeap 0 nested).2.pending ≠ [] := by decide

theorem returned_handle_omission_breaks_future_reads :
    walk (collect cyclicHeap (∅ : Roots Unit (Fin 3))) 1 [2, 1] ≠
      walk cyclicHeap 1 [2, 1] := by
  rw [walk, lookup_collect_of_not_live cyclicHeap ∅ (not_live_empty cyclicHeap 1)]
  decide +kernel

theorem unrelated_payload_write_is_admitted :
    RegionReadStability.Admitted cyclicHeap nested [(0, 99)] := by
  constructor
  · simp only [RegionReadStability.dependencies, footprint_is_shared_not_duplicated]
    decide
  · trivial

theorem unrelated_write_preserves_nested_pending_work :
    RegionReadStability.interleave cyclicHeap nested [(0, 99)] = run cyclicHeap 1 nested :=
  RegionReadStability.admitted_interleaving_exact cyclicHeap nested [(0, 99)] unrelated_payload_write_is_admitted

theorem collection_and_unrelated_mutation_preserve_the_complete_page :
    (runHeap (fun _ => true) (cyclicHeap.writePayload 0 99) 3 nested).2 = run cyclicHeap 3 nested := by
  apply RegionReadStability.interference_and_collection_compose
  apply RegionReadStability.outside_payload_write
  exact unrelated_payload_write_is_admitted.1

end Mettapedia.Machines.RegionReadCollection.Controls
