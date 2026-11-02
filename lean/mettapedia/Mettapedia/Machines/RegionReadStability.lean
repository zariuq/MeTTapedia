import Mettapedia.Machines.RegionReadCollection

/-!
# Local rely conditions for live read regions

Complete cells in the reachable footprint must stay unchanged. Negative root
lookups are dependencies too: allocating a previously missing root changes its
answer even though it was absent from the live footprint. These local lookup
conditions imply preservation of all path observations, not the reverse.

Payload writes outside that dependency set satisfy the rely condition.
The interleaving theorem permits a different such write before every machine
operation. It is an explicit sequential-interleaving model, not a claim that
native validation and use are atomic, or that arbitrary concurrent collectors
and graph rewrites satisfy the condition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RegionReadStability

open ResourceOwnership RegionReadCollection

variable {Address Value : Type} [DecidableEq Address]

noncomputable def dependencies (heap : Heap Address Value) (state : State Address Value) : Finset Address :=
  footprint heap state.registry ∪ state.roots.toFinset

def Rely (before after : Heap Address Value) (state : State Address Value) : Prop :=
  ∀ address ∈ dependencies before state, after.lookup address = before.lookup address

theorem walk_eq_of_live_readings (before after : Heap Address Value) (roots : Roots Unit Address)
    (stable : ∀ address, Live before roots address → after.lookup address = before.lookup address)
    (start : Address) (live : Live before roots start) (path : List Address) :
    walk after start path = walk before start path := by
  induction path generalizing start with
  | nil => simp only [walk, stable start live]
  | cons child rest ih =>
      simp only [walk, stable start live]
      cases found : before.lookup start with
      | none => rfl
      | some cell =>
          simp only [Option.bind_some]
          split
          next reference => exact ih child (live_step before roots live found reference)
          next => rfl

theorem rely_implies_agrees (before after : Heap Address Value) (state : State Address Value)
    (rely : Rely before after state) : AgreesAt before after state := by
  intro address member path
  by_cases present : address ∈ before.allocated
  · apply walk_eq_of_live_readings before after state.registry
    · intro needed live
      exact rely needed (Finset.mem_union_left _ ((mem_footprint before state.registry needed).mpr live))
    · exact live_of_root before state.registry ((registry_mem state address).mpr member) present
  · have same := rely address (Finset.mem_union_right _ (List.mem_toFinset.mpr member))
    have missing := lookup_absent before address present
    cases path <;> simp [walk, same, missing]

theorem rely_preserves_page (before after : Heap Address Value) (state : State Address Value)
    (rely : Rely before after state) (budget : Nat) :
    run after budget state = run before budget state :=
  (run_agrees before after budget state (rely_implies_agrees before after state rely)).1

theorem interference_and_collection_compose (policy : Nat → Bool)
    (before after : Heap Address Value) (state : State Address Value)
    (rely : Rely before after state) (budget : Nat) :
    (runHeap policy after budget state).2 = run before budget state :=
  (heap_run_preserves_future policy after budget state).1.trans
    (rely_preserves_page before after state rely budget)

theorem outside_payload_write (heap : Heap Address Value) (state : State Address Value)
    (address : Address) (value : Value) (outside : address ∉ dependencies heap state) :
    Rely heap (heap.writePayload address value) state := by
  intro needed member
  apply Heap.writePayload_lookup_other
  intro same
  exact outside (same ▸ member)

abbrev Write (Address Value : Type) := Address × Value

def interleave (heap : Heap Address Value) (state : State Address Value) :
    List (Write Address Value) → State Address Value
  | [] => state
  | (address, value) :: rest =>
      let current := heap.writePayload address value
      interleave current (step current state) rest

/-- Every check is against the actual current heap and residual, not just the
initial root list. The environment writes themselves are never discarded. -/
def Admitted (heap : Heap Address Value) (state : State Address Value) :
    List (Write Address Value) → Prop
  | [] => True
  | (address, value) :: rest =>
      address ∉ dependencies heap state ∧
        Admitted (heap.writePayload address value) (step (heap.writePayload address value) state) rest

theorem admitted_interleaving_exact (heap : Heap Address Value) (state : State Address Value)
    (writes : List (Write Address Value)) (admitted : Admitted heap state writes) :
    interleave heap state writes = run heap writes.length state := by
  induction writes generalizing heap state with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨address, value⟩
      have stable := rely_implies_agrees heap (heap.writePayload address value) state
        (outside_payload_write heap state address value admitted.1)
      simp only [interleave, List.length_cons]
      rw [ih _ _ admitted.2]
      change run (heap.writePayload address value) (rest.length + 1) state = _
      exact (run_agrees heap _ _ state stable).1

namespace Controls

open ResourceOwnership.Examples

def reader : State (Fin 3) Nat := ⟨[.read 1 [2]], [], []⟩

theorem live_root_write_changes_the_page :
    (run (cyclicHeap.writePayload 2 99) 1 reader).answers ≠ (run cyclicHeap 1 reader).answers := by decide +kernel

def absentHeap : Heap (Fin 1) Nat where
  lookup _ := none
  allocated := ∅
  allocated_iff _ := by simp
  closed _ _ impossible := by cases impossible

def allocatedHeap : Heap (Fin 1) Nat where
  lookup _ := some ⟨7, ∅, 1⟩
  allocated := Finset.univ
  allocated_iff address := ⟨fun _ => ⟨_, rfl⟩, fun _ => Finset.mem_univ address⟩
  closed _ _ _ _ _ := Finset.mem_univ _

def absentReader : State (Fin 1) Nat := ⟨[.read 0 []], [], []⟩

theorem missing_root_is_still_a_dependency : (0 : Fin 1) ∈ dependencies absentHeap absentReader := by
  apply Finset.mem_union_right
  decide

theorem allocating_a_negative_lookup_changes_the_result :
    (run absentHeap 1 absentReader).answers = [none] ∧
      (run allocatedHeap 1 absentReader).answers = [some (0, ⟨7, ∅, 1⟩)] := by decide +kernel

theorem footprint_only_validation_misses_that_change :
    (∀ address ∈ footprint absentHeap absentReader.registry, allocatedHeap.lookup address = absentHeap.lookup address) ∧
      ¬ Rely absentHeap allocatedHeap absentReader := by
  constructor
  · intro address member
    have live := (mem_footprint absentHeap absentReader.registry address).mp member
    have allocated := live_allocated absentHeap absentReader.registry live
    exact False.elim (Finset.notMem_empty address allocated)
  · intro rely
    have wrong := rely 0 missing_root_is_still_a_dependency
    cases wrong

end Controls

end Mettapedia.Machines.RegionReadStability
