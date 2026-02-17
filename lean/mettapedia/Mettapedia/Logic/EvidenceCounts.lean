import Mathlib.Data.Real.Basic

/-!
# Evidence Counts Views

Shared count-based views for binary evidence.

This module centralizes the standard count-to-probability formulas used across
`Exchangeability` and `EvidenceBeta`.
-/

namespace Mettapedia.Logic.EvidenceCounts

/-- PLN strength from natural number counts (improper prior view). -/
noncomputable def plnStrength (n_pos n_neg : ℕ) : ℝ :=
  if n_pos + n_neg = 0 then 0 else (n_pos : ℝ) / (n_pos + n_neg : ℝ)

/-- Uniform prior posterior mean (Laplace). -/
noncomputable def uniformPosteriorMean (n_pos n_neg : ℕ) : ℝ :=
  ((n_pos : ℝ) + 1) / ((n_pos : ℝ) + (n_neg : ℝ) + 2)

/-- Jeffreys prior posterior mean. -/
noncomputable def jeffreysPosteriorMean (n_pos n_neg : ℕ) : ℝ :=
  ((n_pos : ℝ) + 0.5) / ((n_pos : ℝ) + (n_neg : ℝ) + 1)

/-- With nonzero sample size, PLN strength is the empirical fraction `n_pos / (n_pos + n_neg)`. -/
theorem plnStrength_eq_improper_mean (n_pos n_neg : ℕ) (h : n_pos + n_neg ≠ 0) :
    plnStrength n_pos n_neg = (n_pos : ℝ) / (n_pos + n_neg : ℝ) := by
  unfold plnStrength
  simp only [h, ↓reduceIte]

end Mettapedia.Logic.EvidenceCounts

