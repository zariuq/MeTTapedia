import Mettapedia.Logic.PLNHigherOrderVarianceUpdate

/-!
# Higher-Order Posterior Update

This module adds a theorem-facing Bayesian update rule for regime weights.
The point is not to formalize a particular estimator, but to formalize the
state transition that reveal actions are supposed to induce.
-/

namespace Mettapedia.Logic

open scoped BigOperators

variable {R : Type*} [Fintype R] [DecidableEq R]

noncomputable def bayesianUpdateWeights
    (posterior : CertifiedRegimePosterior R)
    (likelihood : R → ℝ)
    (_hlik_nonneg : ∀ r, 0 ≤ likelihood r)
    (_hnorm : 0 < ∑ r, posterior.weights r * likelihood r) :
    R → ℝ :=
  fun r => posterior.weights r * likelihood r /
    (∑ r', posterior.weights r' * likelihood r')

noncomputable def bayesianUpdatePosterior
    (posterior : CertifiedRegimePosterior R)
    (likelihood : R → ℝ)
    (hlik_nonneg : ∀ r, 0 ≤ likelihood r)
    (hnorm : 0 < ∑ r, posterior.weights r * likelihood r) :
    CertifiedRegimePosterior R where
  weights := bayesianUpdateWeights posterior likelihood hlik_nonneg hnorm
  valid := by
    constructor
    · intro r
      unfold bayesianUpdateWeights
      apply div_nonneg
      · exact mul_nonneg
          (CertifiedRegimePosterior.weights_nonneg posterior r)
          (hlik_nonneg r)
      · linarith
    · have hden_ne : (∑ r, posterior.weights r * likelihood r) ≠ 0 := by
        linarith
      let Z : ℝ := ∑ r, posterior.weights r * likelihood r
      have hsum :
          ∑ r, posterior.weights r * likelihood r / Z =
            (∑ r, posterior.weights r * likelihood r) / Z := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul]
      calc
        ∑ r, bayesianUpdateWeights posterior likelihood hlik_nonneg hnorm r
            = Z / Z := by
                  simp [bayesianUpdateWeights, Z, hsum]
        _ = 1 := by
              field_simp [Z, hden_ne]
  uncertaintyRadius := posterior.uncertaintyRadius
  uncertaintyRadius_nonneg := posterior.uncertaintyRadius_nonneg

theorem bayesianUpdate_valid
    (posterior : CertifiedRegimePosterior R)
    (likelihood : R → ℝ)
    (hlik_nonneg : ∀ r, 0 ≤ likelihood r)
    (hnorm : 0 < ∑ r, posterior.weights r * likelihood r) :
    PLNRegimeMixtureTheorems.ValidRegimeWeights
      (bayesianUpdateWeights posterior likelihood hlik_nonneg hnorm) := by
  exact (bayesianUpdatePosterior posterior likelihood hlik_nonneg hnorm).valid

theorem bayesianUpdate_concentrates_of_equal_prior_and_likelihood_gap
    (posterior : CertifiedRegimePosterior R)
    (likelihood : R → ℝ)
    (hlik_nonneg : ∀ r, 0 ≤ likelihood r)
    (hnorm : 0 < ∑ r, posterior.weights r * likelihood r)
    {r₀ r₁ : R}
    (hprior : posterior.weights r₁ = posterior.weights r₀)
    (hlik : likelihood r₁ ≤ likelihood r₀) :
    bayesianUpdateWeights posterior likelihood hlik_nonneg hnorm r₁ ≤
      bayesianUpdateWeights posterior likelihood hlik_nonneg hnorm r₀ := by
  have hden_pos : 0 < ∑ r, posterior.weights r * likelihood r := hnorm
  have hnum :
      posterior.weights r₁ * likelihood r₁ ≤
        posterior.weights r₀ * likelihood r₀ := by
    rw [hprior]
    exact mul_le_mul_of_nonneg_left hlik
      (CertifiedRegimePosterior.weights_nonneg posterior r₀)
  unfold bayesianUpdateWeights
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)

theorem expectedPosteriorVariance_le_priorVariance
    (step : EnrichedChainStep R) :
    expectedPostRevealVariance step ≤ totalVariance step := by
  exact expectedPostRevealVariance_le_totalVariance step

theorem expectedPosteriorVariance_drop_eq_betweenVariance
    (step : EnrichedChainStep R) :
    totalVariance step - expectedPostRevealVariance step =
      betweenVariance step := by
  exact revealVarianceReduction_eq_betweenVariance step

end Mettapedia.Logic
