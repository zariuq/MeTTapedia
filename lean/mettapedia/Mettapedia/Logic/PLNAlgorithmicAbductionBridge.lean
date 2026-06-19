import Mettapedia.Logic.PLNInductionAbductionITVBridge
import Mettapedia.Logic.IntensionalInheritanceSolomonoffBridge

/-!
# Algorithmic-Prior Abduction Ranking

`Truth_Abduction` supplies an inverse-deduction point estimate.  Explanation
selection also needs a prior over hypotheses.  This file gives the narrow
bridge used by WM-PLN:

* the prior-weighted interval is just the existing abduction interval scaled by
  a supplied hypothesis prior;
* when that prior is supplied by the universal-mixture/Solomonoff bridge, this
  is an algorithmic-prior explanation score;
* finite description-length weights give small executable canaries.

The file does not claim that a point score is tight.  Robust ranking is by
separated prior-weighted intervals.
-/

namespace Mettapedia.Logic.PLN

open Mettapedia.Logic.PLNIndefiniteTruth
open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.IntensionalInheritance

/-- A simple finite description-length prior used for executable canaries:
`2^{-k}`.  The full universal-mixture prior is provided separately by
`priorFromConditional`. -/
noncomputable def descriptionLengthPrior (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ k

noncomputable def priorWeightedPoint (prior point : ℝ) : ℝ :=
  prior * point

noncomputable def priorWeightedLower (prior : ℝ) (itv : ITV) : ℝ :=
  prior * itv.lower

noncomputable def priorWeightedUpper (prior : ℝ) (itv : ITV) : ℝ :=
  prior * itv.upper

/-- Robust explanation ranking after applying hypothesis priors. -/
def priorWeightedIntervalStrictlyRanks
    (betterPrior worsePrior : ℝ) (better worse : ITV) : Prop :=
  priorWeightedUpper worsePrior worse < priorWeightedLower betterPrior better

/-- Prior-weighted intervals overlap when the weighted credal evidence still
does not justify a strict explanation ranking. -/
def priorWeightedIntervalsOverlap
    (xPrior yPrior : ℝ) (x y : ITV) : Prop :=
  priorWeightedLower xPrior x ≤ priorWeightedUpper yPrior y ∧
    priorWeightedLower yPrior y ≤ priorWeightedUpper xPrior x

/-- Universal-mixture prior-weighted lower endpoint.  This is the hook from
algorithmic/intensional explanation priors into the already-built abduction
interval surface. -/
noncomputable def universalMixtureAbductionLower
    (ξ : Mettapedia.Logic.IntensionalInheritance.Semimeasure)
    (ctx hypothesis : Mettapedia.Logic.IntensionalInheritance.BinString)
    (itv : ITV) : ℝ :=
  priorWeightedLower (priorFromConditional ξ ctx hypothesis) itv

/-- Universal-mixture prior-weighted upper endpoint. -/
noncomputable def universalMixtureAbductionUpper
    (ξ : Mettapedia.Logic.IntensionalInheritance.Semimeasure)
    (ctx hypothesis : Mettapedia.Logic.IntensionalInheritance.BinString)
    (itv : ITV) : ℝ :=
  priorWeightedUpper (priorFromConditional ξ ctx hypothesis) itv

/-- Positive canary: an algorithmic prior can reverse point-only abduction and
also justify a robust interval ranking when the prior-weighted intervals are
separated.

Here the simpler candidate has raw point `3/4` and interval `[1/2,1]`; the
more complex candidate has stronger raw point `5/6` and interval `[2/3,1]`.
With description-length priors `2^{-1}` and `2^{-4}`, the simpler explanation
strictly wins after prior weighting. -/
theorem algorithmicPriorAbduction_strict_interval_rank_canary :
    descriptionLengthPrior 1 = (1 / 2 : ℝ) ∧
      descriptionLengthPrior 4 = (1 / 16 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (3 / 4 : ℝ) ∧
      plnAbductionStrength
          (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (5 / 6 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) <
        plnAbductionStrength
          (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) =
        (3 / 8 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 4)
          (plnAbductionStrength
            (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) =
        (5 / 96 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 4)
          (plnAbductionStrength
            (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) <
        priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) ∧
      priorWeightedLower (descriptionLengthPrior 1)
          abductionSearchBetterPointITV =
        (1 / 4 : ℝ) ∧
      priorWeightedUpper (descriptionLengthPrior 1)
          abductionSearchBetterPointITV =
        (1 / 2 : ℝ) ∧
      priorWeightedLower (descriptionLengthPrior 4)
          abductionSearchStrongITV =
        (1 / 24 : ℝ) ∧
      priorWeightedUpper (descriptionLengthPrior 4)
          abductionSearchStrongITV =
        (1 / 16 : ℝ) ∧
      priorWeightedIntervalStrictlyRanks
        (descriptionLengthPrior 1) (descriptionLengthPrior 4)
        abductionSearchBetterPointITV abductionSearchStrongITV := by
  norm_num [descriptionLengthPrior, priorWeightedPoint, priorWeightedLower,
    priorWeightedUpper, priorWeightedIntervalStrictlyRanks,
    abductionSearchBetterPointITV, abductionSearchStrongITV,
    plnAbductionCredalStrengthITV, deductionCredalStrengthITV,
    deductionCredalStrengthLower, deductionCredalStrengthUpper,
    deductionCredalJointLower, deductionCredalJointUpper,
    deductionBBranchLower, deductionBBranchUpper,
    deductionNotBBranchLower, deductionNotBBranchUpper,
    deductionJointAB, deductionJointBC, bayesInversion, plnAbductionStrength,
    plnDeductionStrength]

/-- Negative canary: a description-length prior may flip point scores while
the prior-weighted intervals still overlap.  In that case the system should
record ambiguity, not a robust best explanation. -/
theorem algorithmicPriorAbduction_point_flip_not_interval_rank_canary :
    plnAbductionStrength
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) =
      (1 / 2 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (3 / 4 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) <
        plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)) =
        (1 / 4 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 2)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) =
        (3 / 16 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 2)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) <
        priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
      priorWeightedIntervalsOverlap
        (descriptionLengthPrior 1) (descriptionLengthPrior 2)
        abductionSearchOpenITV abductionSearchBetterPointITV ∧
      ¬ priorWeightedIntervalStrictlyRanks
        (descriptionLengthPrior 1) (descriptionLengthPrior 2)
        abductionSearchOpenITV abductionSearchBetterPointITV ∧
      ¬ priorWeightedIntervalStrictlyRanks
        (descriptionLengthPrior 2) (descriptionLengthPrior 1)
        abductionSearchBetterPointITV abductionSearchOpenITV := by
  norm_num [descriptionLengthPrior, priorWeightedPoint, priorWeightedLower,
    priorWeightedUpper, priorWeightedIntervalsOverlap,
    priorWeightedIntervalStrictlyRanks, abductionSearchOpenITV,
    abductionSearchBetterPointITV, plnAbductionCredalStrengthITV,
    deductionCredalStrengthITV, deductionCredalStrengthLower,
    deductionCredalStrengthUpper, deductionCredalJointLower,
    deductionCredalJointUpper, deductionBBranchLower, deductionBBranchUpper,
    deductionNotBBranchLower, deductionNotBBranchUpper, deductionJointAB,
    deductionJointBC, bayesInversion, plnAbductionStrength,
    plnDeductionStrength]

end Mettapedia.Logic.PLN
