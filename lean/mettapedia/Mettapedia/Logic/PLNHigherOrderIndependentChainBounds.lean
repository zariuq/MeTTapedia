import Mettapedia.Logic.PLNHigherOrderChainBounds
import Mathlib.Data.Real.Basic

/-!
# Higher-Order Independent Chain Bounds

This module adds stronger chain bounds under an explicit quadratic/RSS-style
certificate.  The conservative additive and bottleneck laws remain canonical;
these theorems describe what becomes available under stronger assumptions.
-/

namespace Mettapedia.Logic

open scoped BigOperators

theorem chainSquaredError_le_rss_of_quadraticCertificate
    {n : ℕ}
    (errors : Fin n → ℝ)
    {ε : ℝ}
    (hquad : (∑ i, errors i) ^ 2 ≤ ∑ i, (errors i) ^ 2)
    (hbound : ∀ i, (errors i) ^ 2 ≤ ε ^ 2) :
    (∑ i, errors i) ^ 2 ≤ n * ε ^ 2 := by
  calc
    (∑ i, errors i) ^ 2 ≤ ∑ i, (errors i) ^ 2 := hquad
    _ ≤ ∑ i, ε ^ 2 := by
          exact Finset.sum_le_sum fun i _ => hbound i
    _ = n * ε ^ 2 := by simp

theorem chainError_le_rss_of_quadraticCertificate
    {n : ℕ}
    (errors : Fin n → ℝ)
    {ε : ℝ}
    (hquad : (∑ i, errors i) ^ 2 ≤ ∑ i, (errors i) ^ 2)
    (hbound : ∀ i, (errors i) ^ 2 ≤ ε ^ 2) :
    |∑ i, errors i| ≤ Real.sqrt (n * ε ^ 2) := by
  have hsq' :
      (∑ i, errors i) ^ 2 ≤ n * ε ^ 2 := by
    exact chainSquaredError_le_rss_of_quadraticCertificate errors hquad hbound
  have hroot :
      Real.sqrt ((∑ i, errors i) ^ 2) ≤ Real.sqrt (n * ε ^ 2) := by
    exact Real.sqrt_le_sqrt hsq'
  simpa [Real.sqrt_sq_eq_abs] using hroot

theorem rssBound_le_additiveBound
    {n : ℕ}
    {ε : ℝ}
    (hε : 0 ≤ ε) :
    Real.sqrt (n * ε ^ 2) ≤ n * ε := by
  have hsqrt_n_le_n : Real.sqrt (n : ℝ) ≤ n := by
    by_cases h0 : n = 0
    · subst h0
      norm_num
    · have hpos_nat : 0 < n := Nat.pos_iff_ne_zero.mpr h0
      have hone_le : (1 : ℝ) ≤ n := by exact_mod_cast hpos_nat
      have hsq : (n : ℝ) ≤ n ^ 2 := by nlinarith
      exact (Real.sqrt_le_iff).2 ⟨by positivity, by simpa [sq] using hsq⟩
  calc
    Real.sqrt (n * ε ^ 2) = Real.sqrt (n : ℝ) * ε := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg hε]
    _ ≤ n * ε := by
      gcongr

end Mettapedia.Logic
