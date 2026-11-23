import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Geometric tail bounds for finite weighted sums in the extended nonnegative reals. -/

set_option autoImplicit false

open scoped ENNReal

namespace Mettapedia.Analysis

theorem tsum_scaled_geometric_tail (scale ratio : ENNReal) (cutoff : Nat) :
    (∑' m : ℕ, if cutoff ≤ m then scale * ratio ^ m else 0) =
      scale * ratio ^ cutoff * (1 - ratio)⁻¹ := by
  have onTail :
      (∑' m : ↥((Finset.range cutoff : Set ℕ)ᶜ), scale * ratio ^ (m : ℕ)) =
        ∑' m : ℕ, if cutoff ≤ m then scale * ratio ^ m else 0 := by
    rw [tsum_subtype (f := fun m : ℕ => scale * ratio ^ m)]
    apply tsum_congr
    intro m
    simp only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt]
  have shifted :
      (∑' m : ↥((Finset.range cutoff : Set ℕ)ᶜ), scale * ratio ^ (m : ℕ)) =
        ∑' m : ℕ, scale * ratio ^ (m + cutoff) := by
    exact ((notMemRangeEquiv cutoff).symm.tsum_eq
      (f := fun m : {n // n ∉ Finset.range cutoff} => scale * ratio ^ (m : ℕ))).symm
  rw [← onTail, shifted]
  calc
    _ = ∑' m : ℕ, (scale * ratio ^ cutoff) * ratio ^ m := by
      apply tsum_congr
      intro m
      rw [pow_add]
      ac_rfl
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- Discounting an exponential count bound composes the growth and discount
in each summand. The remaining geometric tail depends only on the cutoff. -/
theorem sum_discounted_geometric_tail_le (support : Finset Nat)
    (scale growth discount : ENNReal) (cutoff : Nat) :
    (∑ m ∈ support, (if cutoff ≤ m then scale * growth ^ m else 0) * (discount ^ m)⁻¹) ≤
      scale * (growth * discount⁻¹) ^ cutoff * (1 - growth * discount⁻¹)⁻¹ := by
  calc
    _ = ∑ m ∈ support, if cutoff ≤ m then scale * (growth * discount⁻¹) ^ m else 0 := by
      apply Finset.sum_congr rfl
      intro m _
      by_cases active : cutoff ≤ m
      · simp only [if_pos active, ENNReal.inv_pow, mul_pow, mul_assoc]
      · simp [active]
    _ ≤ ∑' m : ℕ, if cutoff ≤ m then scale * (growth * discount⁻¹) ^ m else 0 :=
      ENNReal.sum_le_tsum support
    _ = _ := tsum_scaled_geometric_tail _ _ _

end Mettapedia.Analysis
