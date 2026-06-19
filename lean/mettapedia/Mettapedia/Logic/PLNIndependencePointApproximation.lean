import Mettapedia.Logic.PLNDeductionITVBridge

/-!
# Independence-Point Approximation Canaries

This file records the small theorem surface behind a common implementation
temptation: represent second-order truth values by moments, histograms, samples,
or mixtures of Betas, then push the marginal representations through a rule.

The honest reading is narrower.  A marginal-only calculation targets the
product-coupling, or independence-point, answer.  That point can be useful and
fast, but it is only one member of the no-independence credal interval unless a
coupling/independence assumption has actually been discharged.
-/

namespace Mettapedia.Logic.PLNIndependencePoint

open Mettapedia.Logic.PLNDeduction

/-- Mean of the product `X * Y` under the product coupling of two two-point
marginals. -/
noncomputable def twoPointProductPushforwardMean
    (x₀ x₁ y₀ y₁ wx wy : ℝ) : ℝ :=
  wx * wy * (x₀ * y₀) +
    wx * (1 - wy) * (x₀ * y₁) +
    (1 - wx) * wy * (x₁ * y₀) +
    (1 - wx) * (1 - wy) * (x₁ * y₁)

noncomputable def twoPointMarginalMean (x₀ x₁ w : ℝ) : ℝ :=
  w * x₀ + (1 - w) * x₁

/-- Under the product coupling, pushing a product rule through the full
two-by-two table is exactly the product of marginal means.  This is the useful
fast heuristic, but also the place where the independence assumption enters. -/
theorem twoPointProductPushforwardMean_eq_productOfMarginalMeans
    (x₀ x₁ y₀ y₁ wx wy : ℝ) :
    twoPointProductPushforwardMean x₀ x₁ y₀ y₁ wx wy =
      twoPointMarginalMean x₀ x₁ wx * twoPointMarginalMean y₀ y₁ wy := by
  unfold twoPointProductPushforwardMean twoPointMarginalMean
  ring

/-- A one-parameter family of couplings for two equiprobable two-point
marginals.  The product coupling is `t = 1/4`; the Fréchet endpoints are
`t = 0` and `t = 1/2`. -/
noncomputable def twoPointHalfHalfCouplingProductMean
    (x₀ x₁ y₀ y₁ t : ℝ) : ℝ :=
  t * (x₀ * y₀) +
    ((1 / 2 : ℝ) - t) * (x₀ * y₁) +
    ((1 / 2 : ℝ) - t) * (x₁ * y₀) +
    t * (x₁ * y₁)

/-- The executable Fréchet-gap witness used by the CeTTa experiment:
the independence-point `0.30` sits strictly inside `[0.21, 0.39]`. -/
theorem twoPointProductCoupling_strictly_inside_frechet_gap_canary :
    twoPointHalfHalfCouplingProductMean
        (1 / 5 : ℝ) (4 / 5 : ℝ) (3 / 10 : ℝ) (9 / 10 : ℝ) 0 =
        (21 / 100 : ℝ) ∧
      twoPointProductPushforwardMean
        (1 / 5 : ℝ) (4 / 5 : ℝ) (3 / 10 : ℝ) (9 / 10 : ℝ)
        (1 / 2 : ℝ) (1 / 2 : ℝ) =
        (3 / 10 : ℝ) ∧
      twoPointHalfHalfCouplingProductMean
        (1 / 5 : ℝ) (4 / 5 : ℝ) (3 / 10 : ℝ) (9 / 10 : ℝ)
        (1 / 2 : ℝ) =
        (39 / 100 : ℝ) ∧
      (21 / 100 : ℝ) < (3 / 10 : ℝ) ∧
      (3 / 10 : ℝ) < (39 / 100 : ℝ) ∧
      (39 / 100 : ℝ) - (21 / 100 : ℝ) = (9 / 50 : ℝ) := by
  norm_num [twoPointHalfHalfCouplingProductMean,
    twoPointProductPushforwardMean]

/-- A direct deduction-level canary: the traditional independence-point
formula is inside the no-independence interval, but the interval is fully open.
This is why a marginal-only approximation must report width, not only a point. -/
theorem simpleDeductionStrength_independencePoint_inside_openInterval_canary :
    deductionCredalStrengthLower
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) =
        (0 : ℝ) ∧
      simpleDeductionStrengthFormula
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) =
        (1 / 2 : ℝ) ∧
      deductionCredalStrengthUpper
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) =
        (1 : ℝ) ∧
      deductionCredalStrengthLower
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) <
        simpleDeductionStrengthFormula
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) ∧
      simpleDeductionStrengthFormula
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) <
        deductionCredalStrengthUpper
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) := by
  norm_num [deductionCredalStrengthLower, deductionCredalStrengthUpper,
    deductionCredalJointLower, deductionCredalJointUpper,
    deductionBBranchLower, deductionBBranchUpper, deductionNotBBranchLower,
    deductionNotBBranchUpper, deductionJointAB, deductionJointBC,
    simpleDeductionStrengthFormula, conditionalProbabilityConsistency,
    smallestIntersectionProbability, largestIntersectionProbability]

/-- The single-Beta effective concentration matching a law's first two moments.
This is a display/readout for a whole second-order law, not the average of
component concentrations in an arbitrary mixture encoding. -/
noncomputable def effectiveConcentration (mean variance : ℝ) : ℝ :=
  mean * (1 - mean) / variance - 1

noncomputable def weightedAverageComponentCount
    (w₁ c₁ w₂ c₂ : ℝ) : ℝ :=
  w₁ * c₁ + w₂ * c₂

/-- A flat high-variance law has low effective concentration even if someone
chooses to encode it as a mixture of sharp components. -/
theorem flatLaw_effectiveConcentration_not_weightedComponentCount_canary :
    effectiveConcentration (1 / 2 : ℝ) (1 / 4 : ℝ) = (0 : ℝ) ∧
      weightedAverageComponentCount
        (1 / 2 : ℝ) (1000 : ℝ) (1 / 2 : ℝ) (1000 : ℝ) =
        (1000 : ℝ) ∧
      effectiveConcentration (1 / 2 : ℝ) (1 / 4 : ℝ) <
        weightedAverageComponentCount
          (1 / 2 : ℝ) (1000 : ℝ) (1 / 2 : ℝ) (1000 : ℝ) := by
  norm_num [effectiveConcentration, weightedAverageComponentCount]

end Mettapedia.Logic.PLNIndependencePoint
