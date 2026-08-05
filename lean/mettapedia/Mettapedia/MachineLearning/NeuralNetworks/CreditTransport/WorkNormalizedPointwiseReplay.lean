import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PointwiseCoordinateReplay

/-!
# Work-normalized pointwise replay

A sampling law can have the better expected one-step objective and still be
worse per unit measured work.  This file adds the exact finite comparison
needed to keep those claims separate.

The quantity below is observed expected benefit divided by declared positive
work.  It is a one-state replay statistic, not a guarantee that repeated
nonlinear updates accumulate the same benefit.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace WorkNormalizedPointwiseReplay

open ImportanceSampledCoordinateDescent
open PointwiseCoordinateReplay

noncomputable section

universe u

variable {Coordinate : Type u}
  [Fintype Coordinate] [Nonempty Coordinate]

/-- Exact expected objective benefit per unit of declared work. -/
def expectedBenefitPerWork
    (weight benefit : Coordinate → ℝ) (work : ℝ) : ℝ :=
  weightedAverage weight benefit / work

omit [Nonempty Coordinate] in
/-- Compare two pointwise replay laws without a floating-ratio shortcut. -/
theorem expectedBenefitPerWork_lt_iff_cross
    (leftWeight rightWeight benefit : Coordinate → ℝ)
    {leftWork rightWork : ℝ}
    (positiveLeftWork : 0 < leftWork)
    (positiveRightWork : 0 < rightWork) :
    expectedBenefitPerWork leftWeight benefit leftWork <
        expectedBenefitPerWork rightWeight benefit rightWork ↔
      weightedAverage leftWeight benefit * rightWork <
        weightedAverage rightWeight benefit * leftWork := by
  exact div_lt_div_iff₀ positiveLeftWork positiveRightWork

omit [Nonempty Coordinate] in
/-- At equal positive work, ordering by work-normalized benefit is exactly
ordering by expected benefit. -/
theorem expectedBenefitPerWork_lt_iff_of_equalWork
    (leftWeight rightWeight benefit : Coordinate → ℝ)
    {work : ℝ} (positiveWork : 0 < work) :
    expectedBenefitPerWork leftWeight benefit work <
        expectedBenefitPerWork rightWeight benefit work ↔
      weightedAverage leftWeight benefit <
        weightedAverage rightWeight benefit := by
  exact div_lt_div_iff_of_pos_right positiveWork

/-! ## Exact reversal fixture -/

def highBenefitWeight : Bool → ℝ
  | false => 3
  | true => 1

def lowCostWeight : Bool → ℝ
  | false => 1
  | true => 3

/-- From a pre-step objective of `4`, the two proposals have benefits `4`
and `2`. -/
def positiveBenefit : Bool → ℝ
  | false => 4
  | true => 2

theorem highBenefitWeight_pos :
    ∀ coordinate, 0 < highBenefitWeight coordinate := by
  intro coordinate
  cases coordinate <;> norm_num [highBenefitWeight]

theorem lowCostWeight_pos :
    ∀ coordinate, 0 < lowCostWeight coordinate := by
  intro coordinate
  cases coordinate <;> norm_num [lowCostWeight]

/-- The high-benefit law is strictly better per draw. -/
theorem highBenefit_has_greater_expectedBenefit :
    weightedAverage lowCostWeight positiveBenefit <
      weightedAverage highBenefitWeight positiveBenefit := by
  norm_num [
    weightedAverage, totalWeight, lowCostWeight,
    highBenefitWeight, positiveBenefit]

/-- If the high-benefit law costs twice as much, the lower-benefit law is
strictly better per measured work. -/
theorem higherBenefit_can_have_lowerBenefitPerWork :
    expectedBenefitPerWork highBenefitWeight positiveBenefit 2 <
      expectedBenefitPerWork lowCostWeight positiveBenefit 1 := by
  norm_num [
    expectedBenefitPerWork, weightedAverage, totalWeight,
    lowCostWeight, highBenefitWeight, positiveBenefit]

/-- Zero work is not a valid experimental denominator: field division maps
it to zero rather than to an infinite benefit rate. -/
theorem zeroWork_collapsesBenefitRate :
    expectedBenefitPerWork highBenefitWeight positiveBenefit 0 = 0 := by
  simp [expectedBenefitPerWork]

#print axioms expectedBenefitPerWork_lt_iff_cross
#print axioms expectedBenefitPerWork_lt_iff_of_equalWork
#print axioms highBenefit_has_greater_expectedBenefit
#print axioms higherBenefit_can_have_lowerBenefitPerWork
#print axioms zeroWork_collapsesBenefitRate

end

end WorkNormalizedPointwiseReplay

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
