import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32PointwiseCoordinateReplay
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedPointwiseReplay

/-!
# Exact binary32 work-normalized pointwise replay

Pointwise replay distinguishes the expected objective after one sampled
proposal from any claim about future iterates.  This module makes a second
distinction explicit: a proposal law can be better per draw while being worse
per declared unit of work.

The checker retains the objective, sampling-weight, and work measurements as
finite binary32 words.  Its soundness theorem concerns exactly those decoded
values.  It does not identify a work counter with wall time or extrapolate one
checkpoint observation to later states.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32WorkNormalizedPointwiseReplay

open Float32CheckpointMatrix
open Float32PointwiseCoordinateReplay
open ImportanceSampledCoordinateDescent
open PointwiseCoordinateReplay
open WorkNormalizedPointwiseReplay

noncomputable section

universe u

variable {Coordinate : Type u}
  [Fintype Coordinate] [Nonempty Coordinate]

/-- Two sampling laws over one shared proposal table, together with the
positive work attributed to one draw from each law. -/
structure Float32WorkComparison (Coordinate : Type u) where
  sampling : Float32SamplingComparison Coordinate
  leftWork : FiniteFloat32Word
  rightWork : FiniteFloat32Word

def Float32WorkComparison.leftWorkRat
    (comparison : Float32WorkComparison Coordinate) : ℚ :=
  comparison.leftWork.toRat

def Float32WorkComparison.rightWorkRat
    (comparison : Float32WorkComparison Coordinate) : ℚ :=
  comparison.rightWork.toRat

def Float32WorkComparison.leftWorkReal
    (comparison : Float32WorkComparison Coordinate) : ℝ :=
  comparison.leftWork.toReal

def Float32WorkComparison.rightWorkReal
    (comparison : Float32WorkComparison Coordinate) : ℝ :=
  comparison.rightWork.toReal

/-- Both work measurements must be strictly positive. -/
def Float32WorkComparison.positiveWorkCheck
    (comparison : Float32WorkComparison Coordinate) : Bool :=
  decide (
    0 < comparison.leftWorkRat ∧
      0 < comparison.rightWorkRat)

/-- Accept exactly when both sampling laws and both work measurements are
positive and the left law has greater exact expected benefit per work. -/
def Float32WorkComparison.check
    (comparison : Float32WorkComparison Coordinate) : Bool :=
  comparison.sampling.leftTable.positiveWeightCheck &&
    (comparison.sampling.rightTable.positiveWeightCheck &&
      (comparison.positiveWorkCheck &&
        decide (
          comparison.sampling.rightTable.expectedBenefitRat /
                comparison.rightWorkRat <
            comparison.sampling.leftTable.expectedBenefitRat /
                comparison.leftWorkRat)))

omit [Fintype Coordinate] [Nonempty Coordinate] in
theorem Float32WorkComparison.cast_leftWorkRat
    (comparison : Float32WorkComparison Coordinate) :
    (comparison.leftWorkRat : ℝ) = comparison.leftWorkReal := by
  rfl

omit [Fintype Coordinate] [Nonempty Coordinate] in
theorem Float32WorkComparison.cast_rightWorkRat
    (comparison : Float32WorkComparison Coordinate) :
    (comparison.rightWorkRat : ℝ) = comparison.rightWorkReal := by
  rfl

/- A successful word-level check proves the same strict work-normalized
ordering for the exact real values denoted by those words. -/
omit [Nonempty Coordinate] in
theorem Float32WorkComparison.check_sound
    (comparison : Float32WorkComparison Coordinate)
    (accepted : comparison.check = true) :
    expectedBenefitPerWork
        comparison.sampling.rightTable.weightReal
        (replayBenefit comparison.sampling.rightTable.beforeReal
          comparison.sampling.rightTable.afterReal)
        comparison.rightWorkReal <
      expectedBenefitPerWork
        comparison.sampling.leftTable.weightReal
        (replayBenefit comparison.sampling.leftTable.beforeReal
          comparison.sampling.leftTable.afterReal)
        comparison.leftWorkReal := by
  have outer := Bool.and_eq_true_iff.mp accepted
  have middle := Bool.and_eq_true_iff.mp outer.2
  have inner := Bool.and_eq_true_iff.mp middle.2
  have benefitRateRat :
      comparison.sampling.rightTable.expectedBenefitRat /
            comparison.rightWorkRat <
        comparison.sampling.leftTable.expectedBenefitRat /
            comparison.leftWorkRat :=
    of_decide_eq_true inner.2
  have benefitRateReal :
      (comparison.sampling.rightTable.expectedBenefitRat : ℝ) /
            (comparison.rightWorkRat : ℝ) <
        (comparison.sampling.leftTable.expectedBenefitRat : ℝ) /
            (comparison.leftWorkRat : ℝ) := by
    exact_mod_cast benefitRateRat
  simpa [
    expectedBenefitPerWork,
    comparison.sampling.rightTable.cast_expectedBenefitRat,
    comparison.sampling.leftTable.cast_expectedBenefitRat,
    comparison.cast_rightWorkRat,
    comparison.cast_leftWorkRat] using benefitRateReal

/-! ## Exact reversal and rejection fixtures -/

def positiveTwoWord : FiniteFloat32Word where
  word := 1073741824
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveFourWord : FiniteFloat32Word where
  word := 1082130432
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

/-- Both proposals help from objective `4`: one reaches `0`, the other `2`.
The left law favors the smaller benefit but is assigned half the work. -/
def lowCostVersusHighRawBenefit :
    Float32SamplingComparison Bool where
  before := positiveFourWord
  after
    | false => zeroWord
    | true => positiveTwoWord
  leftWeight
    | false => positiveOne
    | true => positiveThree
  rightWeight
    | false => positiveThree
    | true => positiveOne

def lowCostWinsPerWork : Float32WorkComparison Bool where
  sampling := lowCostVersusHighRawBenefit
  leftWork := positiveOne
  rightWork := positiveTwoWord

/-- The right law has the better expected objective before accounting for
work. -/
theorem highRawBenefit_is_betterPerDraw :
    weightedAverage
        lowCostVersusHighRawBenefit.rightTable.weightReal
        lowCostVersusHighRawBenefit.rightTable.afterReal <
      weightedAverage
        lowCostVersusHighRawBenefit.leftTable.weightReal
        lowCostVersusHighRawBenefit.leftTable.afterReal := by
  norm_num [
    weightedAverage, totalWeight,
    Float32SamplingComparison.leftTable,
    Float32SamplingComparison.rightTable,
    Float32ReplayTable.weightReal,
    Float32ReplayTable.afterReal,
    lowCostVersusHighRawBenefit,
    positiveFourWord, positiveTwoWord,
    positiveThree, positiveOne, zeroWord,
    FiniteFloat32Word.toReal, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

/-- The exact checker accepts the opposite ordering after the declared
two-to-one work difference is included. -/
theorem lowCostWinsPerWork_is_accepted :
    lowCostWinsPerWork.check = true := by
  norm_num [
    Float32WorkComparison.check,
    Float32WorkComparison.positiveWorkCheck,
    Float32WorkComparison.leftWorkRat,
    Float32WorkComparison.rightWorkRat,
    Float32SamplingComparison.leftTable,
    Float32SamplingComparison.rightTable,
    Float32ReplayTable.positiveWeightCheck,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    lowCostWinsPerWork, lowCostVersusHighRawBenefit,
    positiveFourWord, positiveTwoWord,
    positiveThree, positiveOne, zeroWord,
    FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

theorem lowCostWinsPerWork_is_better :
    expectedBenefitPerWork
        lowCostWinsPerWork.sampling.rightTable.weightReal
        (replayBenefit
          lowCostWinsPerWork.sampling.rightTable.beforeReal
          lowCostWinsPerWork.sampling.rightTable.afterReal)
        lowCostWinsPerWork.rightWorkReal <
      expectedBenefitPerWork
        lowCostWinsPerWork.sampling.leftTable.weightReal
        (replayBenefit
          lowCostWinsPerWork.sampling.leftTable.beforeReal
          lowCostWinsPerWork.sampling.leftTable.afterReal)
        lowCostWinsPerWork.leftWorkReal :=
  lowCostWinsPerWork.check_sound lowCostWinsPerWork_is_accepted

def zeroWorkComparison : Float32WorkComparison Bool where
  sampling := lowCostVersusHighRawBenefit
  leftWork := zeroWord
  rightWork := positiveOne

/-- Zero work is rejected rather than entering field division as a
misleading zero rate. -/
theorem zeroWorkComparison_is_rejected :
    zeroWorkComparison.check = false := by
  norm_num [
    Float32WorkComparison.check,
    Float32WorkComparison.positiveWorkCheck,
    Float32WorkComparison.leftWorkRat,
    Float32WorkComparison.rightWorkRat,
    Float32SamplingComparison.leftTable,
    Float32SamplingComparison.rightTable,
    Float32ReplayTable.positiveWeightCheck,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    zeroWorkComparison, lowCostVersusHighRawBenefit,
    positiveFourWord, positiveTwoWord,
    positiveThree, positiveOne, zeroWord,
    FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

#print axioms Float32WorkComparison.check_sound
#print axioms highRawBenefit_is_betterPerDraw
#print axioms lowCostWinsPerWork_is_accepted
#print axioms lowCostWinsPerWork_is_better
#print axioms zeroWorkComparison_is_rejected

end

end Float32WorkNormalizedPointwiseReplay

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
