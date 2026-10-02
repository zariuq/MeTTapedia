import Mettapedia.Algorithms.CertifiedLogarithm

/-! # Certified rational enclosures of finite logarithmic objectives -/

namespace Mettapedia.Algorithms.CertifiedLogScore

open Finset
open CertifiedLogarithm

variable {I : Type*} [Fintype I]

def approximation (weight argument : I → ℚ) (terms : ℕ) : ℚ :=
  ∑ i, weight i * CertifiedLogarithm.approximation (argument i) terms

def radius (weight argument : I → ℚ) (terms : ℕ) : ℚ :=
  ∑ i, |weight i| * CertifiedLogarithm.radius (argument i) terms

/-- Arbitrary signed rational weights retain a rigorous logarithmic score enclosure. -/
theorem enclosure (weight argument : I → ℚ) (positive : ∀ i, 0 < argument i) (terms : ℕ) :
    |(∑ i, (weight i : ℝ) * Real.log (argument i : ℝ)) -
      (approximation weight argument terms : ℝ)| ≤ (radius weight argument terms : ℝ) := by
  simp only [approximation, radius, Rat.cast_sum, Rat.cast_mul, Rat.cast_abs]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(weight i : ℝ) * Real.log (argument i : ℝ) -
        (weight i : ℝ) * CertifiedLogarithm.approximation (argument i) terms| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (CertifiedLogarithm.enclosure (argument i) (positive i) terms) (abs_nonneg _)

theorem radius_nonneg (weight argument : I → ℚ) (positive : ∀ i, 0 < argument i)
    (terms : ℕ) : 0 ≤ radius weight argument terms :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _)
    (CertifiedLogarithm.radius_nonneg (argument i) (positive i) terms))

/-- A finite weighted score inherits convergence of the certified error radii. -/
theorem radius_tendsto_zero (weight argument : I → ℚ) (positive : ∀ i, 0 < argument i) :
    Filter.Tendsto (fun n : ℕ => (radius weight argument n : ℝ))
      Filter.atTop (nhds 0) := by
  have limits := tendsto_finsetSum Finset.univ (fun i _ =>
    (CertifiedLogarithm.radius_tendsto_zero (argument i) (positive i)).const_mul
      |(weight i : ℝ)|)
  simpa [radius] using limits

theorem radius_eventually_small (weight argument : I → ℚ)
    (positive : ∀ i, 0 < argument i) (tolerance : ℝ) (h : 0 < tolerance) :
    ∀ᶠ n : ℕ in Filter.atTop, (radius weight argument n : ℝ) < tolerance :=
  (radius_tendsto_zero weight argument positive).eventually_lt_const h

end Mettapedia.Algorithms.CertifiedLogScore
