import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Init.Data.UInt.Lemmas

/-!
# Finite-width capacity growth for dependency publication

The unsigned implementation doubles a positive capacity while it fits, then
uses the requested capacity directly near the unsigned boundary. This module
connects each UInt32 arithmetic step to an independent natural-number growth
algorithm, proves termination and allocation-size bounds, and exposes the
overflow in unconditional doubling. Heap allocation and pointer publication
are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyCapacity

def maximum : Nat := 4294967295

def grow (required next : Nat) : Nat :=
  if pending : next < required then
    if next > maximum / 2 then required
    else if positive : 0 < next then grow required (next * 2)
    else required
  else next
termination_by required - next
decreasing_by omega

theorem grow_covers_request (required next : Nat) : required ≤ grow required next := by
  unfold grow
  split
  · split
    · exact Nat.le_refl _
    · split
      · exact grow_covers_request required (next * 2)
      · exact Nat.le_refl _
  · omega
termination_by required - next
decreasing_by omega

theorem grow_preserves_capacity (required next : Nat) : next ≤ grow required next := by
  unfold grow
  split
  · split
    · omega
    · split
      · have later := grow_preserves_capacity required (next * 2)
        omega
      · omega
  · exact Nat.le_refl _
termination_by required - next
decreasing_by omega

theorem grow_bounded (required next : Nat)
    (requestBound : required ≤ maximum) (capacityBound : next ≤ maximum) :
    grow required next ≤ maximum := by
  unfold grow
  split
  · split
    · exact requestBound
    · split
      · apply grow_bounded required (next * 2) requestBound
        simp only [maximum] at *
        omega
      · exact requestBound
  · exact capacityBound
termination_by required - next
decreasing_by omega

theorem sufficient_capacity_is_unchanged (required next : Nat) (fits : required ≤ next) :
    grow required next = next := by
  rw [grow, dif_neg (by omega)]

def unsignedStep (required next : UInt32) : UInt32 :=
  if next > 2147483647 then required else next * 2

theorem unsignedStep_realizes_natural_step (required next : UInt32) :
    (unsignedStep required next).toNat =
      if next.toNat > maximum / 2 then required.toNat else next.toNat * 2 := by
  by_cases high : next > 2147483647
  · have bound : next.toNat > maximum / 2 := by
      simpa [UInt32.lt_iff_toNat_lt, maximum] using high
    simp [unsignedStep, high, bound]
  · have bound : ¬ next.toNat > maximum / 2 := by
      simpa [UInt32.lt_iff_toNat_lt, maximum] using high
    simp only [unsignedStep, high, ↓reduceIte, bound, UInt32.toNat_mul]
    have fits : next.toNat * 2 < 2 ^ 32 := by
      simp only [maximum] at bound
      omega
    simpa using Nat.mod_eq_of_lt fits

theorem unsignedStep_progress (required next : UInt32)
    (positive : 0 < next.toNat) (pending : next.toNat < required.toNat) :
    next.toNat < (unsignedStep required next).toNat := by
  rw [unsignedStep_realizes_natural_step]
  split <;> omega

theorem unsigned_addition_guard (existing added : UInt32)
    (fits : added ≤ 4294967295 - existing) :
    (existing + added).toNat = existing.toNat + added.toNat := by
  have bound := existing.toNat_lt
  have belowMaximum : existing ≤ (4294967295 : UInt32) := by
    rw [UInt32.le_iff_toNat_le]
    change existing.toNat ≤ 4294967295
    omega
  have admitted : added.toNat ≤ maximum - existing.toNat := by
    have naturalFits := UInt32.le_iff_toNat_le.mp fits
    rw [UInt32.toNat_sub_of_le _ _ belowMaximum] at naturalFits
    exact naturalFits
  rw [UInt32.toNat_add]
  apply Nat.mod_eq_of_lt
  simp only [maximum] at admitted
  omega

theorem allocation_size_does_not_overflow_u64 (capacity pointerBytes : Nat)
    (capacityBound : capacity ≤ maximum) (pointerBound : pointerBytes ≤ 4294967296) :
    capacity * pointerBytes < 2 ^ 64 := by
  have upper := Nat.mul_le_mul capacityBound pointerBound
  norm_num [maximum] at upper ⊢
  omega

theorem addressable_allocation_uses_exact_u64_product
    (capacity pointerBytes : UInt64)
    (capacityBound : capacity.toNat ≤ maximum)
    (pointerBound : pointerBytes.toNat ≤ 4294967296) :
    (capacity * pointerBytes).toNat = capacity.toNat * pointerBytes.toNat := by
  rw [UInt64.toNat_mul]
  exact Nat.mod_eq_of_lt
    (allocation_size_does_not_overflow_u64 _ _ capacityBound pointerBound)

namespace Controls

example : grow 5 4 = 8 := by
  rw [grow]
  norm_num [maximum]
  rw [grow]
  norm_num
example : grow 2147483649 2147483648 = 2147483649 := by
  rw [grow]
  norm_num [maximum]
example : grow maximum 2147483648 = maximum := by
  rw [grow]
  norm_num [maximum]
example : (unsignedStep 4294967295 2147483648).toNat = maximum := by decide

/-- Dropping the boundary guard turns a required growth into zero. -/
example : ((2147483648 : UInt32) * 2).toNat = 0 := by decide
example : ¬ (2147483649 ≤ ((2147483648 : UInt32) * 2).toNat) := by decide

end Controls
end Mettapedia.Machines.OrderedDependencyCapacity
