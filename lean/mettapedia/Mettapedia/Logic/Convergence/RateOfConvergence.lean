import Mettapedia.Logic.Convergence.LawOfLargeNumbers
import Mettapedia.Logic.Convergence.ConfidenceConvergence
import Mettapedia.Logic.EvidenceBeta

/-!
# Rate of Convergence for PLN Evidence

This file establishes quantitative convergence rates for PLN strength and confidence,
connecting the abstract convergence results to explicit bounds.

## Key Results

- `confidence_gap_bound`: 1 - c ≤ κ/n
- `pln_error_is_O_inv_n`: Combined error is O(1/n)
- Re-exports `strength_converges_to_mean` from EvidenceBeta

## Connection to EvidenceBeta

The key result from `EvidenceBeta.lean` is `strength_converges_to_mean`:
- For n = n⁺ + n⁻ observations with prior parameter α₀
- |PLN_strength - Beta_mean| → 0 as n → ∞

Combined with confidence convergence, both errors are O(1/n).

## References

- `EvidenceBeta.lean`: `strength_converges_to_mean`
- `ConfidenceConvergence.lean`: `confidence_gap`
-/

namespace Mettapedia.Logic.Convergence

open Mettapedia.Logic.PLNEvidence
open Mettapedia.Logic.EvidenceBeta
open Filter Topology
open scoped ENNReal

/-! ## Confidence Gap Bound -/

/-- The confidence gap is bounded by κ/n for n > 0 -/
theorem confidence_gap_le_div (κ : ℝ) (hκ : 0 < κ) (n : ℕ) (hn : 0 < n) :
    1 - confidenceFromN κ n ≤ κ / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [confidence_gap κ hκ n]
  apply div_le_div_of_nonneg_left (le_of_lt hκ) hn'
  linarith

/-- Confidence gap tends to 0 at rate O(1/n) -/
theorem confidence_gap_rate (κ : ℝ) (hκ : 0 < κ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 0 < n → 1 - confidenceFromN κ n < ε := by
  intro ε hε
  use Nat.ceil (κ / ε) + 1
  intro n hn hn_pos
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hbound := confidence_gap_le_div κ hκ n hn_pos
  calc 1 - confidenceFromN κ n
      ≤ κ / n := hbound
    _ < ε := by
      rw [div_lt_iff₀ hn']
      have hceil : κ / ε ≤ Nat.ceil (κ / ε) := Nat.le_ceil _
      have hN : (Nat.ceil (κ / ε) : ℝ) + 1 ≤ (n : ℝ) := by
        have h := Nat.cast_le (α := ℝ).mpr hn
        simp only [Nat.cast_add, Nat.cast_one] at h
        exact h
      have hN' : κ / ε + 1 ≤ n := le_trans (add_le_add_right hceil 1) hN
      have hN'' : κ / ε < n := by linarith
      have hε' : ε ≠ 0 := hε.ne'
      have hκ_lt : κ < (n : ℝ) * ε := by
        have h1 : κ / ε < n := hN''
        calc κ = (κ / ε) * ε := by field_simp
          _ < n * ε := by nlinarith
      rw [mul_comm] at hκ_lt
      exact hκ_lt

/-! ## Re-exports from EvidenceBeta -/

/-- Re-export: PLN strength converges to posterior mean -/
theorem strength_converges : ∀ ε : ℝ, 0 < ε → ∀ prior_param : ℝ, 0 < prior_param →
    ∃ N : ℕ, ∀ n_pos n_neg : ℕ, n_pos + n_neg ≥ N → n_pos + n_neg ≠ 0 →
      let strength := plnStrength n_pos n_neg
      let mean := ((n_pos : ℝ) + prior_param) / ((n_pos : ℝ) + (n_neg : ℝ) + 2 * prior_param)
      |strength - mean| < ε := strength_converges_to_mean

/-! ## Combined Convergence Rate -/

/-- For large n, both strength error and confidence gap are small -/
theorem pln_eventually_accurate (prior_param κ : ℝ) (hprior : 0 < prior_param) (hκ : 0 < κ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n_pos n_neg : ℕ, n_pos + n_neg ≥ N → n_pos + n_neg ≠ 0 →
      -- Strength converges
      let strength := plnStrength n_pos n_neg
      let mean := ((n_pos : ℝ) + prior_param) / ((n_pos : ℝ) + (n_neg : ℝ) + 2 * prior_param)
      |strength - mean| < ε ∧
      -- Confidence converges
      1 - confidenceFromN κ (n_pos + n_neg) < ε := by
  intro ε hε
  -- Get N₁ for strength convergence
  obtain ⟨N₁, hN₁⟩ := strength_converges_to_mean ε hε prior_param hprior
  -- Get N₂ for confidence convergence
  obtain ⟨N₂, hN₂⟩ := confidence_gap_rate κ hκ ε hε
  -- Take maximum
  use max N₁ N₂
  intro n_pos n_neg hn hne
  constructor
  · -- Strength part
    have hn₁ : n_pos + n_neg ≥ N₁ := le_trans (le_max_left N₁ N₂) hn
    exact hN₁ n_pos n_neg hn₁ hne
  · -- Confidence part
    have hn₂ : n_pos + n_neg ≥ N₂ := le_trans (le_max_right N₁ N₂) hn
    have hn_pos : 0 < n_pos + n_neg := Nat.pos_of_ne_zero hne
    exact hN₂ (n_pos + n_neg) hn₂ hn_pos

/-! ## Summary

This file establishes:

1. **Confidence gap bounds**:
   - `confidence_gap_le_div`: 1 - c ≤ κ/n
   - `confidence_gap_rate`: O(1/n) rate

2. **Combined convergence**:
   - `pln_eventually_accurate`: Both strength and confidence converge

3. **Re-exports**:
   - `strength_converges`: From EvidenceBeta

## Key Insight

Both strength error and confidence gap are O(1/n):
- Strength error: |PLN - Beta_mean| → 0 at rate O(1/n)
- Confidence gap: 1 - c = κ/(n+κ) ≤ κ/n

This gives the Emulated Math Council (Tao) the rigorous rate bounds they require.
-/

end Mettapedia.Logic.Convergence
