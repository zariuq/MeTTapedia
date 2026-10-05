import Mettapedia.GSLT.LanguageDef.NativeOpsCPostIndex

/-!
# Fallible dependency-array reservation

This logical allocator boundary separates preservation of initialized slots
from success, capacity growth and publication. It models the reserve helper's
branches and unsigned request, using the independent growth algorithm.
Physical address relocation, C field layout, aliases and realization of the
complete preparation syntax are still separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyCReserve

open OrderedDependencyCapacity
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex

universe u
variable {Value : Type u}

abbrev Allocator (Value : Type u) := List Value → Nat → Option (List Value)

/-- Ordinary reallocation preserves old initialized elements on success.
This law is an external-service obligation, not a C correctness conclusion.
New spare elements are opaque values and are not read by publication. -/
def AllocationLaw (allocate : Allocator Value) : Prop :=
  ∀ before required after, allocate before required = some after →
    after.length = required ∧ after.take before.length = before

def chosenCapacity (before : Array32 Value) (required : UInt32) : Nat :=
  grow required.toNat (if before.slots.length = 0 then 4 else before.slots.length)

def reserve (allocate : Allocator Value) (pointerBytes sizeMaximum : Nat)
    (before : Array32 Value) (required : UInt32) : Bool × Array32 Value :=
  if required.toNat ≤ before.slots.length then (true, before)
  else
    let capacity := chosenCapacity before required
    if capacity * pointerBytes > sizeMaximum then (false, before)
    else match allocate before.slots capacity with
      | none => (false, before)
      | some grown => (true, ⟨grown, before.count⟩)

theorem chosen_capacity_covers (before : Array32 Value) (required : UInt32) :
    required.toNat ≤ chosenCapacity before required := grow_covers_request _ _

theorem chosen_capacity_preserves_extent (before : Array32 Value) (required : UInt32) :
    before.slots.length ≤ chosenCapacity before required := by
  have bound := grow_preserves_capacity required.toNat
    (if before.slots.length = 0 then 4 else before.slots.length)
  by_cases empty : before.slots.length = 0 <;> simp [chosenCapacity, empty] at *
  exact bound

theorem chosen_capacity_bounded (before : Array32 Value) (required : UInt32)
    (sized : before.Sized) : chosenCapacity before required ≤ maximum := by
  apply grow_bounded
  · have bound := required.toNat_lt
    change required.toNat ≤ 4294967295
    omega
  · by_cases empty : before.slots.length = 0
    · simp [empty, maximum]
    · simpa [empty] using (show before.slots.length ≤ maximum from sized)

theorem sufficient_capacity_never_calls_allocator (allocate : Allocator Value)
    (pointerBytes sizeMaximum : Nat) (before : Array32 Value) (required : UInt32)
    (fits : required.toNat ≤ before.slots.length) :
    reserve allocate pointerBytes sizeMaximum before required = (true, before) := by
  simp [reserve, fits]

theorem reservation_failure_retains_array (allocate : Allocator Value)
    (pointerBytes sizeMaximum : Nat) (before : Array32 Value) (required : UInt32)
    (failed : (reserve allocate pointerBytes sizeMaximum before required).1 = false) :
    (reserve allocate pointerBytes sizeMaximum before required).2 = before := by
  by_cases fits : required.toNat ≤ before.slots.length
  · simp [reserve, fits] at failed
  · by_cases tooLarge : chosenCapacity before required * pointerBytes > sizeMaximum
    · simp [reserve, fits, tooLarge]
    · cases allocated : allocate before.slots (chosenCapacity before required) with
      | none => simp [reserve, fits, tooLarge, allocated]
      | some grown => simp [reserve, fits, tooLarge, allocated] at failed

theorem reservation_success_preserves_and_covers (allocate : Allocator Value)
    (law : AllocationLaw allocate) (pointerBytes sizeMaximum : Nat)
    (before : Array32 Value) (required : UInt32) (sized : before.Sized)
    (liveCount : before.count.toNat ≤ before.slots.length)
    (succeeded : (reserve allocate pointerBytes sizeMaximum before required).1 = true) :
    let after := (reserve allocate pointerBytes sizeMaximum before required).2
    after.count = before.count ∧ before.slots.length ≤ after.slots.length ∧
      required.toNat ≤ after.slots.length ∧ after.Sized ∧ after.active = before.active := by
  by_cases fits : required.toNat ≤ before.slots.length
  · simpa [reserve, fits] using (show before.count = before.count ∧
      before.slots.length ≤ before.slots.length ∧ required.toNat ≤ before.slots.length ∧
      before.Sized ∧ before.active = before.active from ⟨rfl, le_rfl, fits, sized, rfl⟩)
  · by_cases tooLarge : chosenCapacity before required * pointerBytes > sizeMaximum
    · simp [reserve, fits, tooLarge] at succeeded
    · cases allocated : allocate before.slots (chosenCapacity before required) with
      | none => simp [reserve, fits, tooLarge, allocated] at succeeded
      | some grown =>
          have payload := law before.slots (chosenCapacity before required) grown allocated
          have result : reserve allocate pointerBytes sizeMaximum before required =
              (true, ⟨grown, before.count⟩) := by simp [reserve, fits, tooLarge, allocated]
          rw [result]
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · rw [payload.1]
            exact chosen_capacity_preserves_extent before required
          · rw [payload.1]
            exact chosen_capacity_covers before required
          · change grown.length ≤ maximum
            rw [payload.1]
            exact chosen_capacity_bounded before required sized
          · change grown.take before.count.toNat = before.slots.take before.count.toNat
            calc
              grown.take before.count.toNat = (grown.take before.slots.length).take before.count.toNat := by
                rw [List.take_take, Nat.min_eq_left liveCount]
              _ = before.slots.take before.count.toNat := by rw [payload.2]

theorem successful_forward_reservation_admits_exact_batch
    (allocate : Allocator Value) (law : AllocationLaw allocate)
    (pointerBytes sizeMaximum : Nat) (before : Array32 Value) (added : UInt32)
    (sized : before.Sized) (liveCount : before.count.toNat ≤ before.slots.length)
    (fits : added ≤ 4294967295 - before.count)
    (succeeded : (reserve allocate pointerBytes sizeMaximum before (before.count + added)).1 = true) :
    before.count.toNat + added.toNat ≤
      (reserve allocate pointerBytes sizeMaximum before (before.count + added)).2.slots.length := by
  have extent := (reservation_success_preserves_and_covers allocate law pointerBytes sizeMaximum
    before (before.count + added) sized liveCount succeeded).2.2.1
  rwa [unsigned_addition_guard before.count added fits] at extent

/-- A concrete allocator specimen can move the complete payload and append
fresh spare slots. The abstract service law is proved for this implementation. -/
def paddingAllocator (filler : Value) (available : Bool) : Allocator Value :=
  fun before required =>
    if available && before.length ≤ required then
      some (before ++ List.replicate (required - before.length) filler)
    else none

theorem padding_allocator_law (filler : Value) (available : Bool) :
    AllocationLaw (paddingAllocator filler available) := by
  intro before required after allocated
  unfold paddingAllocator at allocated
  split at allocated
  · rename_i admitted
    have room : before.length ≤ required := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at admitted
      exact admitted.2
    cases Option.some.inj allocated
    constructor
    · simp only [List.length_append, List.length_replicate]
      omega
    · simp
  · contradiction

namespace Controls

def old : Array32 Nat := ⟨[10, 20], 2⟩

private theorem chosen_three : chosenCapacity old 3 = 4 := by
  change grow 3 2 = 4
  rw [grow]
  norm_num [maximum]
  rw [grow]
  norm_num

theorem spare_capacity_growth_preserves_active_values :
    let result := reserve (paddingAllocator 99 true) 8 1024 old 3
    result.1 = true ∧ result.2.slots = [10, 20, 99, 99] ∧ result.2.active = [10, 20] := by
  simp only [reserve, show (3 : UInt32).toNat = 3 from rfl, old, List.length_cons,
    List.length_nil, Nat.reduceAdd, show ¬ (3 ≤ 2) by omega, ↓reduceIte]
  simp only [show chosenCapacity (⟨[10, 20], 2⟩ : Array32 Nat) 3 = 4 from chosen_three]
  norm_num [paddingAllocator, Array32.active]
  decide

theorem allocation_failure_has_no_publication :
    reserve (paddingAllocator 99 false) 8 1024 old 3 = (false, old) := by
  simp only [reserve, show (3 : UInt32).toNat = 3 from rfl, old, List.length_cons,
    List.length_nil, Nat.reduceAdd, show ¬ (3 ≤ 2) by omega, ↓reduceIte]
  simp only [show chosenCapacity (⟨[10, 20], 2⟩ : Array32 Nat) 3 = 4 from chosen_three]
  norm_num [paddingAllocator]

theorem size_guard_refuses_before_allocation :
    reserve (paddingAllocator 99 true) 8 16 old 3 = (false, old) := by
  simp only [reserve, show (3 : UInt32).toNat = 3 from rfl, old, List.length_cons,
    List.length_nil, Nat.reduceAdd, show ¬ (3 ≤ 2) by omega, ↓reduceIte]
  simp only [show chosenCapacity (⟨[10, 20], 2⟩ : Array32 Nat) 3 = 4 from chosen_three]
  norm_num

theorem enough_capacity_ignores_allocator_failure :
    reserve (paddingAllocator 99 false) 8 0 old 2 = (true, old) := by
  apply sufficient_capacity_never_calls_allocator
  decide

/-- Reallocation can invalidate a captured physical address even when the
visible list is preserved. No address-equality law is supplied by this model. -/
theorem unconditional_count_increment_is_not_reservation :
    ({ old with count := old.count + 1 } : Array32 Nat).count ≠ old.count := by decide

end Controls

#print axioms chosen_capacity_covers
#print axioms chosen_capacity_preserves_extent
#print axioms chosen_capacity_bounded
#print axioms sufficient_capacity_never_calls_allocator
#print axioms reservation_failure_retains_array
#print axioms reservation_success_preserves_and_covers
#print axioms successful_forward_reservation_admits_exact_batch
#print axioms padding_allocator_law
#print axioms Controls.spare_capacity_growth_preserves_active_values
#print axioms Controls.allocation_failure_has_no_publication
#print axioms Controls.size_guard_refuses_before_allocation
#print axioms Controls.enough_capacity_ignores_allocator_failure
#print axioms Controls.unconditional_count_increment_is_not_reservation

end Mettapedia.Machines.OrderedDependencyCReserve
