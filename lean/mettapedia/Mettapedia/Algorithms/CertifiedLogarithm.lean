import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Rational enclosures for natural logarithms

The algorithm uses rational arithmetic only. Its error certificate is Mathlib's
odd-power expansion of `log ((1+x)/(1-x))`, after the change of variable
`x = (r-1)/(r+1)`. A positive rational input produces an enclosing interval for
the real logarithm. No numerical oracle is trusted.
-/

namespace Mettapedia.Algorithms.CertifiedLogarithm

open Finset

/-- Argument reduction for the odd-power logarithm series. -/
def parameter (r : ℚ) : ℚ := (r - 1) / (r + 1)

/-- A computable rational approximation to the natural logarithm. -/
def approximation (r : ℚ) (terms : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range terms, (parameter r) ^ (2 * i + 1) / (2 * i + 1 : ℕ)

/-- The computable rational radius guaranteed by the series remainder. -/
def radius (r : ℚ) (terms : ℕ) : ℚ :=
  2 * |parameter r| ^ (2 * terms + 1) / (1 - parameter r ^ 2)

theorem parameter_abs_lt_one (r : ℚ) (positive : 0 < r) : |(parameter r : ℝ)| < 1 := by
  have hr : 0 < (r : ℝ) := by exact_mod_cast positive
  have hd : 0 < (r : ℝ) + 1 := by linarith
  change |(((r - 1) / (r + 1) : ℚ) : ℝ)| < 1
  push_cast
  apply abs_lt.mpr
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith

theorem parameter_inverse (r : ℚ) (positive : 0 < r) :
    (1 + (parameter r : ℝ)) / (1 - (parameter r : ℝ)) = r := by
  have hr : 0 < (r : ℝ) := by exact_mod_cast positive
  have hd : (r : ℝ) + 1 ≠ 0 := by linarith
  have hx := (abs_lt.mp (parameter_abs_lt_one r positive)).2
  have hm : 1 - (parameter r : ℝ) ≠ 0 := by linarith
  apply (div_eq_iff hm).mpr
  unfold parameter
  push_cast
  field_simp
  ring

/-- Every positive rational logarithm is enclosed by the rational approximation and radius. -/
theorem enclosure (r : ℚ) (positive : 0 < r) (terms : ℕ) :
    |Real.log (r : ℝ) - (approximation r terms : ℝ)| ≤ (radius r terms : ℝ) := by
  have series := Real.sum_range_sub_log_div_le (parameter_abs_lt_one r positive) terms
  rw [parameter_inverse r positive] at series
  have ha : (approximation r terms : ℝ) =
      2 * ∑ i ∈ Finset.range terms,
        (parameter r : ℝ) ^ (2 * i + 1) / (2 * i + 1 : ℕ) := by
    unfold approximation
    push_cast
    rfl
  have hb : (radius r terms : ℝ) =
      2 * (|(parameter r : ℝ)| ^ (2 * terms + 1) / (1 - (parameter r : ℝ) ^ 2)) := by
    unfold radius
    push_cast
    ring
  rw [ha, hb]
  calc
    _ = 2 * |1 / 2 * Real.log (r : ℝ) - ∑ i ∈ Finset.range terms,
          (parameter r : ℝ) ^ (2 * i + 1) / (2 * i + 1 : ℕ)| := by
      rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← abs_mul]
      congr 1
      ring
    _ ≤ _ := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
        mul_le_mul_of_nonneg_left series (by norm_num : (0 : ℝ) ≤ 2)

theorem lower_bound (r : ℚ) (positive : 0 < r) (terms : ℕ) :
    ((approximation r terms - radius r terms : ℚ) : ℝ) ≤ Real.log (r : ℝ) := by
  have h := (abs_le.mp (enclosure r positive terms)).1
  push_cast
  linarith

theorem upper_bound (r : ℚ) (positive : 0 < r) (terms : ℕ) :
    Real.log (r : ℝ) ≤ ((approximation r terms + radius r terms : ℚ) : ℝ) := by
  have h := (abs_le.mp (enclosure r positive terms)).2
  push_cast
  linarith

theorem radius_nonneg (r : ℚ) (positive : 0 < r) (terms : ℕ) :
    0 ≤ radius r terms := by
  have bound := enclosure r positive terms
  have real_nonneg : 0 ≤ (radius r terms : ℝ) := (abs_nonneg _).trans bound
  exact_mod_cast real_nonneg

/-- Increasing the series budget eventually gives every positive error tolerance. -/
theorem radius_tendsto_zero (r : ℚ) (positive : 0 < r) :
    Filter.Tendsto (fun n : ℕ => (radius r n : ℝ)) Filter.atTop (nhds 0) := by
  have hx := parameter_abs_lt_one r positive
  have hs : (parameter r : ℝ) ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).mpr hx
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (parameter r : ℝ)) hs
  have hc := hp.mul_const (2 * |(parameter r : ℝ)| / (1 - (parameter r : ℝ) ^ 2))
  convert hc using 1
  · funext n
    unfold radius
    push_cast
    rw [pow_add, pow_mul, sq_abs, pow_one]
    ring
  · simp

theorem radius_eventually_small (r : ℚ) (positive : 0 < r) (tolerance : ℝ)
    (h : 0 < tolerance) :
    ∀ᶠ n : ℕ in Filter.atTop, (radius r n : ℝ) < tolerance :=
  (radius_tendsto_zero r positive).eventually_lt_const h

theorem approximation_tendsto (r : ℚ) (positive : 0 < r) :
    Filter.Tendsto (fun n : ℕ => (approximation r n : ℝ))
      Filter.atTop (nhds (Real.log (r : ℝ))) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positiveTolerance
  filter_upwards [radius_eventually_small r positive tolerance positiveTolerance] with n small
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (enclosure r positive n) small

end Mettapedia.Algorithms.CertifiedLogarithm
