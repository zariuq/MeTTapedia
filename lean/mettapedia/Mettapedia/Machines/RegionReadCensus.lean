import Mettapedia.Machines.RegionReadInformation

/-!
# Executable collection for retained read regions

The finite dependency census computes the exact retained allocation set.
Missing root handles remain negative observations; trimming them from the
positive reachability seed does not authorize forgetting them from validity
checks. The executable restriction agrees with the existing semantic
collector and therefore attains its observer-relative allocation minimum.

The operation scheduler may collect before every read-region operation.
This is not a native allocator, a concurrent tracer or a constant-time census.
The lookup closure can retain its input heap in an implementation. The
allocation minimum proved here concerns the registered-cell model, not
physical release by Lean's allocator.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RegionReadCensus

open ResourceOwnership RegionReadCollection RegionReadInformation

variable {Address Value : Type} [DecidableEq Address]

def presentRoots (heap : Heap Address Value) (state : State Address Value) : Roots Unit Address :=
  state.registry.filter (fun pair => pair.2 ∈ heap.allocated)

theorem presentRoots_valid (heap : Heap Address Value) (state : State Address Value) :
    ValidRoots heap (presentRoots heap state) := fun _ member => (Finset.mem_filter.mp member).2

theorem trimmed_live_iff (heap : Heap Address Value) (state : State Address Value) (address : Address) :
    Live heap (presentRoots heap state) address ↔ Live heap state.registry address := by
  constructor
  · exact live_mono heap (Finset.filter_subset _ _)
  · intro live
    induction live with
    | @root address rooted =>
        obtain ⟨pair, member, same⟩ := Finset.mem_image.mp rooted.2
        apply Mettapedia.GSLT.Dynamics.StoreReachability.Reach.root
        refine ⟨rooted.1, Finset.mem_image.mpr ⟨pair, ?_, same⟩⟩
        exact Finset.mem_filter.mpr ⟨member, by simpa [same] using rooted.1⟩
    | step _ edge ih => exact .step ih edge

def retained (heap : Heap Address Value) (state : State Address Value) : Finset Address :=
  census heap (presentRoots heap state)

theorem retained_iff_live (heap : Heap Address Value) (state : State Address Value) (address : Address) :
    address ∈ retained heap state ↔ Live heap state.registry address := by
  rw [retained, mem_census_iff_live heap _ (presentRoots_valid heap state), trimmed_live_iff]

theorem retained_eq_footprint (heap : Heap Address Value) (state : State Address Value) :
    retained heap state = footprint heap state.registry := by
  ext address
  rw [retained_iff_live, mem_footprint]

def collectNow (heap : Heap Address Value) (state : State Address Value) : Heap Address Value :=
  let keep := retained heap state
  { lookup := fun address => if address ∈ keep then heap.lookup address else none
    allocated := keep
    allocated_iff address := by
      by_cases member : address ∈ keep
      · simp only [member, ↓reduceIte, true_iff]
        exact (heap.allocated_iff address).mp
          (live_allocated heap state.registry ((retained_iff_live heap state address).mp member))
      · simp [member]
    closed address cell found next reference := by
      split at found
      next member =>
        exact (retained_iff_live heap state next).mpr
          (live_step heap state.registry ((retained_iff_live heap state address).mp member) found reference)
      next => cases found }

theorem collectNow_lookup (heap : Heap Address Value) (state : State Address Value) :
    (collectNow heap state).lookup = (collect heap state.registry).lookup := by
  funext address
  by_cases member : address ∈ retained heap state
  · rw [lookup_collect_of_live heap state.registry ((retained_iff_live heap state address).mp member)]
    simp [collectNow, member]
  · rw [lookup_collect_of_not_live heap state.registry (fun live => member ((retained_iff_live heap state address).mpr live))]
    simp [collectNow, member]

theorem collectNow_eq_collect (heap : Heap Address Value) (state : State Address Value) :
    collectNow heap state = collect heap state.registry := by
  have same (left right : Heap Address Value) (lookup : left.lookup = right.lookup)
      (allocated : left.allocated = right.allocated) : left = right := by
    cases left
    cases right
    cases lookup
    cases allocated
    rfl
  exact same _ _ (collectNow_lookup heap state) (retained_eq_footprint heap state)

theorem collectNow_agrees (heap : Heap Address Value) (state : State Address Value) :
    AgreesAt heap (collectNow heap state) state := by
  intro address member path
  exact (walk_of_lookup_eq (collect heap state.registry) (collectNow heap state)
    (collectNow_lookup heap state) address path).trans (collect_agrees heap state address member path)

theorem collectNow_minimal (before after : Heap Address Value) (state : State Address Value)
    (agree : AgreesAt before after state) : (collectNow before state).allocated ⊆ after.allocated := by
  change retained before state ⊆ after.allocated
  rw [retained_eq_footprint]
  exact required_allocations before after state agree

def run (policy : Nat → Bool) (heap : Heap Address Value) : Nat → State Address Value → Heap Address Value × State Address Value
  | 0, state => (heap, state)
  | budget + 1, state =>
      let current := if policy budget then collectNow heap state else heap
      run policy current budget (step current state)

theorem run_eq_semantic (policy : Nat → Bool) (heap : Heap Address Value)
    (budget : Nat) (state : State Address Value) :
    run policy heap budget state = runHeap policy heap budget state := by
  induction budget generalizing heap state with
  | zero => rfl
  | succ budget ih => simp only [run, runHeap, collectNow_eq_collect, ih]

theorem run_state_exact (policy : Nat → Bool) (heap : Heap Address Value)
    (budget : Nat) (state : State Address Value) :
    (run policy heap budget state).2 = RegionReadCollection.run heap budget state := by
  rw [run_eq_semantic]
  exact (heap_run_preserves_future policy heap budget state).1

theorem run_preserves_future (policy : Nat → Bool) (heap : Heap Address Value)
    (budget : Nat) (state : State Address Value) :
    AgreesAt heap (run policy heap budget state).1 (run policy heap budget state).2 := by
  rw [run_eq_semantic]
  exact (heap_run_preserves_future policy heap budget state).2

theorem step_root_slots_nonincreasing (heap : Heap Address Value) (state : State Address Value) :
    (step heap state).roots.length ≤ state.roots.length := by
  cases pending : state.pending with
  | nil => simp [step, pending]
  | cons task rest =>
      cases task with
      | sequence first second =>
          simp [step, pending, State.roots, Task.roots, List.length_append]
      | read start path =>
          cases observed : walk heap start path <;>
            simp [step, pending, State.roots, Task.roots, observed, List.filterMap_append,
              List.length_append]

theorem source_root_slots_nonincreasing (heap : Heap Address Value) (budget : Nat) (state : State Address Value) :
    (RegionReadCollection.run heap budget state).roots.length ≤ state.roots.length := by
  induction budget generalizing state with
  | zero => exact Nat.le_refl _
  | succ budget ih =>
      exact (ih (step heap state)).trans (step_root_slots_nonincreasing heap state)

/-- The entry root-slot check covers every prefix, not just the final page.
This does not bound tracing work or temporary allocator storage. -/
theorem run_root_slots_nonincreasing (policy : Nat → Bool) (heap : Heap Address Value)
    (budget : Nat) (state : State Address Value) :
    (run policy heap budget state).2.roots.length ≤ state.roots.length := by
  rw [run_state_exact]
  exact source_root_slots_nonincreasing heap budget state

theorem resumed_page_exact (firstPolicy secondPolicy : Nat → Bool)
    (heap : Heap Address Value) (first second : Nat) (state : State Address Value) :
    let page := run firstPolicy heap first state
    (run secondPolicy page.1 second page.2).2 = RegionReadCollection.run heap (first + second) state := by
  simp only [run_eq_semantic]
  exact resumed_collected_heap_exact firstPolicy secondPolicy heap first second state

namespace Controls

open ResourceOwnership.Examples

theorem cycle_kept_garbage_removed :
    (collectNow cyclicHeap RegionReadInformation.Controls.reader).allocated = {1, 2} := by decide +kernel

theorem missing_root_does_not_invent_an_allocation :
    (collectNow RegionReadStability.Controls.absentHeap RegionReadStability.Controls.absentReader).allocated = ∅ := by decide +kernel

theorem executable_page_matches_source :
    (run (fun _ => true) cyclicHeap 1 RegionReadInformation.Controls.reader).2.answers =
      [some (2, cyclicCell 2)] := by decide +kernel

theorem returned_handle_survives_later_collection :
    let page := run (fun _ => true) cyclicHeap 1 RegionReadInformation.Controls.reader
    (collectNow page.1 page.2).allocated = {1, 2} := by decide +kernel

end Controls

end Mettapedia.Machines.RegionReadCensus
