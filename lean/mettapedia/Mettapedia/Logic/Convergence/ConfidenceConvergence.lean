import Mettapedia.Logic.PLNEvidence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# PLN Confidence Convergence

This file proves that PLN confidence converges to 1 as the number of observations grows.

## Key Results

- `confidenceFromN`: PLN confidence formula c = n/(n+κ)
- `confidence_tendsto_one`: As n → ∞, confidence → 1
- `confidence_rate`: 1 - confidence = κ/(n+κ) = O(1/n)

## The Confidence Formula

PLN confidence measures how much evidence we have relative to a prior:
- c = (n⁺ + n⁻) / (n⁺ + n⁻ + κ)

where:
- n⁺ = positive evidence count
- n⁻ = negative evidence count
- κ = prior parameter (context size)

As total observations n = n⁺ + n⁻ → ∞, confidence → 1.

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009)
- EvidenceBeta.lean for related convergence bounds
-/

namespace Mettapedia.Logic.Convergence

open Mettapedia.Logic.PLNEvidence
open Filter
open Topology

/-! ## Confidence Formula -/

/-- PLN confidence from n observations with prior parameter κ.

    c = n / (n + κ)

    This measures how much evidence we have: 0 when n=0, approaches 1 as n → ∞.
-/
noncomputable def confidenceFromN (κ : ℝ) (n : ℕ) : ℝ := n / (n + κ)

/-- Confidence is non-negative when κ ≥ 0 -/
theorem confidenceFromN_nonneg (κ : ℝ) (hκ : 0 ≤ κ) (n : ℕ) : 0 ≤ confidenceFromN κ n := by
  unfold confidenceFromN
  apply div_nonneg
  · exact Nat.cast_nonneg n
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- Confidence is at most 1 when κ > 0 -/
theorem confidenceFromN_le_one (κ : ℝ) (hκ : 0 < κ) (n : ℕ) : confidenceFromN κ n ≤ 1 := by
  unfold confidenceFromN
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden_pos : 0 < (n : ℝ) + κ := by linarith
  rw [div_le_one hden_pos]
  linarith

/-- Confidence at n=0 is 0 -/
theorem confidenceFromN_zero (κ : ℝ) (_hκ : 0 < κ) : confidenceFromN κ 0 = 0 := by
  unfold confidenceFromN
  simp only [Nat.cast_zero, zero_div]

/-- Confidence is monotonically increasing in n -/
theorem confidenceFromN_mono (κ : ℝ) (hκ : 0 < κ) : Monotone (confidenceFromN κ) := by
  intro m n hmn
  unfold confidenceFromN
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have hdenm_pos : 0 < (m : ℝ) + κ := by linarith
  have hdenn_pos : 0 < (n : ℝ) + κ := by linarith
  -- m/(m+κ) ≤ n/(n+κ) iff m(n+κ) ≤ n(m+κ)
  rw [div_le_div_iff₀ hdenm_pos hdenn_pos]
  -- Need: m * (n + κ) ≤ n * (m + κ)
  -- i.e., m*n + m*κ ≤ n*m + n*κ
  -- i.e., m*κ ≤ n*κ (since m*n = n*m)
  nlinarith

/-! ## Rate of Convergence -/

/-- The gap to full confidence: 1 - c = κ/(n+κ) -/
theorem confidence_gap (κ : ℝ) (hκ : 0 < κ) (n : ℕ) :
    1 - confidenceFromN κ n = κ / ((n : ℝ) + κ) := by
  unfold confidenceFromN
  have hden_pos : 0 < (n : ℝ) + κ := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  field_simp [hden_pos.ne']
  ring

/-- The gap is O(1/n): κ/(n+κ) ≤ κ/n for n > 0 -/
theorem confidence_gap_bound (κ : ℝ) (hκ : 0 < κ) (n : ℕ) (hn : 0 < n) :
    κ / ((n : ℝ) + κ) ≤ κ / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hden_pos : 0 < (n : ℝ) + κ := by linarith
  apply div_le_div_of_nonneg_left (le_of_lt hκ) hn'
  linarith

/-! ## Convergence to 1 -/

/-- Confidence gap tends to 0 -/
theorem confidence_gap_tendsto_zero (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun n => 1 - confidenceFromN κ n) atTop (𝓝 0) := by
  simp_rw [confidence_gap κ hκ]
  -- Need to show κ/(n+κ) → 0 as n → ∞
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + κ) atTop atTop := by
    apply Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
  have h2 : Tendsto (fun x : ℝ => κ / x) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = κ * 0 by ring]
    apply Tendsto.const_mul
    exact tendsto_inv_atTop_zero
  exact h2.comp h1

/-- Confidence converges to 1 as n → ∞ -/
theorem confidence_tendsto_one (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (confidenceFromN κ) atTop (𝓝 1) := by
  have h := confidence_gap_tendsto_zero κ hκ
  -- 1 - c → 0 implies c → 1
  have h' : Tendsto (fun n => 1 - (1 - confidenceFromN κ n)) atTop (𝓝 (1 - 0)) := by
    exact Tendsto.sub tendsto_const_nhds h
  simp only [sub_sub_cancel, sub_zero] at h'
  exact h'

/-! ## Explicit Bounds -/

/-- For n ≥ N, confidence is at least 1 - κ/N -/
theorem confidence_lower_bound (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N) (n : ℕ) (hn : N ≤ n) :
    1 - κ / N ≤ confidenceFromN κ n := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hden_pos : 0 < (n : ℝ) + κ := by linarith
  -- 1 - κ/N ≤ confidenceFromN κ n
  -- Equivalent: 1 - confidenceFromN κ n ≤ κ/N
  -- Using confidence_gap: κ/(n+κ) ≤ κ/N
  have h_gap := confidence_gap κ hκ n
  -- Rewrite using gap
  have h_conf : confidenceFromN κ n = 1 - κ / ((n : ℝ) + κ) := by linarith
  rw [h_conf]
  -- Goal: 1 - κ/N ≤ 1 - κ/(n+κ)
  -- i.e., κ/(n+κ) ≤ κ/N
  have h_ineq : κ / ((n : ℝ) + κ) ≤ κ / N := by
    apply div_le_div_of_nonneg_left (le_of_lt hκ) hN'
    linarith
  linarith

/-- To achieve confidence ≥ 1 - ε, we need n ≥ ⌈κ/ε⌉ observations -/
theorem confidence_threshold (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∃ N : ℕ, ∀ n ≥ N, 1 - ε ≤ confidenceFromN κ n := by
  use Nat.ceil (κ / ε)
  intro n hn
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hceil : κ / ε ≤ n := by
    calc κ / ε ≤ Nat.ceil (κ / ε) := Nat.le_ceil _
      _ ≤ n := Nat.cast_le.mpr hn
  have hden_pos : 0 < (n : ℝ) + κ := by linarith
  -- Need: 1 - ε ≤ confidenceFromN κ n
  -- Using confidence_gap: 1 - confidenceFromN = κ/(n+κ)
  -- So confidenceFromN = 1 - κ/(n+κ)
  -- Need: 1 - ε ≤ 1 - κ/(n+κ)
  -- i.e., κ/(n+κ) ≤ ε
  have h_gap := confidence_gap κ hκ n
  have h_conf : confidenceFromN κ n = 1 - κ / ((n : ℝ) + κ) := by linarith
  rw [h_conf]
  -- Goal: 1 - ε ≤ 1 - κ/(n+κ)
  -- i.e., κ/(n+κ) ≤ ε
  have h_ineq : κ / ((n : ℝ) + κ) ≤ ε := by
    rw [div_le_iff₀ hden_pos]
    -- Need: κ ≤ ε * (n + κ)
    have h : κ ≤ ε * n := by
      calc κ = ε * (κ / ε) := by field_simp
        _ ≤ ε * n := by nlinarith
    -- ε * (n + κ) = ε * n + ε * κ ≥ ε * n ≥ κ
    have hεκ : 0 < ε * κ := mul_pos hε hκ
    nlinarith
  linarith

/-! ## Summary

This file establishes:

1. **confidenceFromN**: PLN confidence formula c = n/(n+κ)

2. **Basic properties**:
   - Non-negative for κ ≥ 0
   - At most 1 for κ > 0
   - Monotonically increasing in n

3. **Convergence**:
   - `confidence_gap`: 1 - c = κ/(n+κ)
   - `confidence_gap_tendsto_zero`: Gap → 0 as n → ∞
   - `confidence_tendsto_one`: c → 1 as n → ∞

4. **Explicit bounds**:
   - `confidence_lower_bound`: For n ≥ N, c ≥ 1 - κ/N
   - `confidence_threshold`: To get c ≥ 1-ε, need n ≥ ⌈κ/ε⌉

The key insight is that confidence increases monotonically toward 1,
with the gap shrinking as O(1/n).
-/

end Mettapedia.Logic.Convergence
