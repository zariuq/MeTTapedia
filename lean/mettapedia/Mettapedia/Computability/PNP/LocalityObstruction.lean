import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# P vs NP crux: logarithmic-radius locality is not polylog-size by itself

This file isolates a concrete obstruction in the Goertzel P≠NP proof strategy.

If a "local decoder" must inspect a bounded-degree neighborhood of radius `Θ(log m)`,
then the number of nodes visible in that neighborhood is already polynomial in `m`,
not polylogarithmic in `m`. So the paper's switching/locality step cannot conclude
`poly(log m)` decoder size from log-radius locality alone; it needs an extra compression
argument.

We record the obstruction in two forms:

* exact natural-number lower bounds for bounded-degree neighborhoods, and
* an asymptotic statement showing every fixed polylogarithm is little-o of the
  resulting log-radius neighborhood growth.
-/

namespace Mettapedia.Computability.PNP

open Filter Asymptotics

noncomputable section

/-- A real-valued model of neighborhood growth for degree `d` and radius `c * log x`. -/
def logRadiusNeighborhood (d c : ℝ) : ℝ → ℝ :=
  fun x => d ^ (c * Real.log x)

/-- A fixed polylogarithmic benchmark. -/
def polylog (k : ℕ) : ℝ → ℝ :=
  fun x => Real.log x ^ k

/-- A degree-`d` neighborhood at radius `log₂ m + 1` already contains at least `m` nodes. -/
theorem inputSize_le_neighborhoodSize_at_binaryLogRadius {d m : ℕ} (hd : 2 ≤ d) :
    m ≤ d ^ (Nat.log 2 m + 1) := by
  have hm : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two m
  exact le_trans hm.le (Nat.pow_le_pow_left hd _)

/-- For powers of two, the radius `log₂ m` already forces polynomial-size neighborhoods. -/
theorem powerOfTwo_le_neighborhoodSize_at_exactBinaryLogRadius {d n : ℕ} (hd : 2 ≤ d) :
    2 ^ n ≤ d ^ (Nat.log 2 (2 ^ n)) := by
  rw [Nat.log_pow Nat.one_lt_two]
  exact Nat.pow_le_pow_left hd n

/-- Concrete sanity check: at `m = 2^20`, quartic polylog is already too small. -/
theorem quarticPolylogFailsAtPowerTwo20 {d : ℕ} (hd : 2 ≤ d) :
    (Nat.log 2 (2 ^ 20)) ^ 4 < d ^ (Nat.log 2 (2 ^ 20)) := by
  rw [Nat.log_pow Nat.one_lt_two]
  have hgap : (20 : ℕ) ^ 4 < 2 ^ 20 := by native_decide
  exact lt_of_lt_of_le hgap (Nat.pow_le_pow_left hd 20)

private theorem logRadiusNeighborhood_eventuallyEq_rpow {d c : ℝ}
    (hd : 1 < d) :
    logRadiusNeighborhood d c =ᶠ[atTop] fun x => x ^ (c * Real.log d) := by
  have hdpos : 0 < d := lt_trans zero_lt_one hd
  have hdnonneg : 0 ≤ d := hdpos.le
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hxd : d ^ Real.log x = x ^ Real.log d := by
    apply Real.log_injOn_pos (Real.rpow_pos_of_pos hdpos _) (Real.rpow_pos_of_pos hx _)
    rw [Real.log_rpow hdpos, Real.log_rpow hx, mul_comm]
  calc
    logRadiusNeighborhood d c x = d ^ (c * Real.log x) := rfl
    _ = d ^ (Real.log x * c) := by rw [mul_comm]
    _ = (d ^ Real.log x) ^ c := by rw [Real.rpow_mul hdnonneg]
    _ = (x ^ Real.log d) ^ c := by rw [hxd]
    _ = x ^ (Real.log d * c) := by rw [← Real.rpow_mul hx.le]
    _ = x ^ (c * Real.log d) := by rw [mul_comm]

/-- Any fixed polylogarithm is asymptotically negligible compared to log-radius neighborhood
growth for degree `d > 1` and positive radius constant `c`. -/
  theorem polylog_isLittleO_logRadiusNeighborhood (k : ℕ) {d c : ℝ}
    (hd : 1 < d) (hc : 0 < c) :
    polylog k =o[atTop] logRadiusNeighborhood d c := by
  have hmain : polylog k =o[atTop] fun x => x ^ (c * Real.log d) := by
    simpa [polylog, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) (mul_pos hc (Real.log_pos hd)))
  exact hmain.congr' Filter.EventuallyEq.rfl (logRadiusNeighborhood_eventuallyEq_rpow hd).symm

private theorem polylog_frequently_ne_zero (k : ℕ) :
    ∃ᶠ x in atTop, polylog k x ≠ 0 := by
  by_cases hk : k = 0
  · subst hk
    exact (Filter.Eventually.of_forall fun x => by simp [polylog]).frequently
  · have heventually : ∀ᶠ x in atTop, polylog k x ≠ 0 := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog : Real.log x ≠ 0 := by
        exact ne_of_gt (Real.log_pos hx)
      simpa [polylog] using pow_ne_zero k hlog
    exact heventually.frequently

/-- Therefore log-radius neighborhood growth is not `O(polylog)` for any fixed exponent. -/
theorem logRadiusNeighborhood_not_isBigO_polylog (k : ℕ) {d c : ℝ}
    (hd : 1 < d) (hc : 0 < c) :
    ¬ logRadiusNeighborhood d c =O[atTop] polylog k :=
  (polylog_isLittleO_logRadiusNeighborhood k hd hc).not_isBigO (polylog_frequently_ne_zero k)

end

end Mettapedia.Computability.PNP
