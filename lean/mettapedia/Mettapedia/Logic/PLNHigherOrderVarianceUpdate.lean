import Mettapedia.Logic.PLNHigherOrderCertifiedEstimates
import Mathlib.Data.Real.Basic

/-!
# Higher-Order Variance Update

This module enriches the current higher-order regime-mixture story with
within-regime uncertainty.  The central payoff is a clean law-of-total-variance
reading of reveal:

- between-regime variance is the part reveal can remove,
- expected within-regime variance is the irreducible post-reveal remainder.
-/

namespace Mettapedia.Logic

open scoped BigOperators
open Mettapedia.Logic.PLNRegimeMixtureTheorems

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- Higher-order step enriched with within-regime uncertainty. -/
structure EnrichedChainStep (R : Type*) [Fintype R] [DecidableEq R] where
  posterior : CertifiedRegimePosterior R
  branchValues : R → ℝ
  withinVariance : R → ℝ
  withinVariance_nonneg : ∀ r, 0 ≤ withinVariance r

/-- The between-regime component is exactly the existing regime-mixture variance. -/
def betweenVariance (step : EnrichedChainStep R) : ℝ :=
  mixtureVariance step.posterior.weights step.branchValues

/-- Expected irreducible uncertainty after revealing the true regime. -/
def expectedWithinVariance (step : EnrichedChainStep R) : ℝ :=
  ∑ r, step.posterior.weights r * step.withinVariance r

/-- Total unresolved uncertainty before reveal. -/
def totalVariance (step : EnrichedChainStep R) : ℝ :=
  betweenVariance step + expectedWithinVariance step

/-- Reveal removes the between-regime part and leaves only within-regime
uncertainty in expectation. -/
def expectedPostRevealVariance (step : EnrichedChainStep R) : ℝ :=
  expectedWithinVariance step

def revealVarianceReduction (step : EnrichedChainStep R) : ℝ :=
  totalVariance step - expectedPostRevealVariance step

def revealBetweenGain (step : EnrichedChainStep R) (cost : ℝ) : ℝ :=
  revealVarianceReduction step - cost

theorem betweenVariance_nonneg (step : EnrichedChainStep R) :
    0 ≤ betweenVariance step := by
  unfold betweenVariance mixtureVariance expectedSquaredLoss
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg
      (CertifiedRegimePosterior.weights_nonneg step.posterior r)
      (sq_nonneg _)

theorem expectedWithinVariance_nonneg (step : EnrichedChainStep R) :
    0 ≤ expectedWithinVariance step := by
  unfold expectedWithinVariance
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg
      (CertifiedRegimePosterior.weights_nonneg step.posterior r)
      (step.withinVariance_nonneg r)

theorem totalVariance_nonneg (step : EnrichedChainStep R) :
    0 ≤ totalVariance step := by
  unfold totalVariance
  exact add_nonneg (betweenVariance_nonneg step) (expectedWithinVariance_nonneg step)

theorem lawOfTotalVariance (step : EnrichedChainStep R) :
    totalVariance step =
      betweenVariance step + expectedWithinVariance step := by
  rfl

theorem expectedPostRevealVariance_eq_expectedWithinVariance
    (step : EnrichedChainStep R) :
    expectedPostRevealVariance step = expectedWithinVariance step := by
  rfl

theorem revealVarianceReduction_eq_betweenVariance
    (step : EnrichedChainStep R) :
    revealVarianceReduction step = betweenVariance step := by
  unfold revealVarianceReduction totalVariance expectedPostRevealVariance
    expectedWithinVariance
  ring

theorem expectedPostRevealVariance_le_totalVariance
    (step : EnrichedChainStep R) :
    expectedPostRevealVariance step ≤ totalVariance step := by
  unfold expectedPostRevealVariance totalVariance
  exact le_add_of_nonneg_left (betweenVariance_nonneg step)

theorem revealBetweenGain_eq_betweenVariance_sub_cost
    (step : EnrichedChainStep R) (cost : ℝ) :
    revealBetweenGain step cost = betweenVariance step - cost := by
  unfold revealBetweenGain
  rw [revealVarianceReduction_eq_betweenVariance]

theorem revealGain_positive_if_cost_lt_betweenVariance
    (step : EnrichedChainStep R) {cost : ℝ}
    (hcost : cost < betweenVariance step) :
    0 < revealBetweenGain step cost := by
  rw [revealBetweenGain_eq_betweenVariance_sub_cost]
  linarith

theorem revealPreferred_if_cost_lt_betweenVariance
    (step : EnrichedChainStep R) {cost : ℝ}
    (hcost : cost < betweenVariance step) :
    cost < revealVarianceReduction step := by
  rw [revealVarianceReduction_eq_betweenVariance]
  exact hcost

end Mettapedia.Logic
