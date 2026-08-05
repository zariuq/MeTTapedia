import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointMatrix
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PointwiseCoordinateReplay

/-!
# Exact binary32 pointwise coordinate replay

A finite checkpoint replay cannot certify regional smoothness or a future
convergence rate.  It can nevertheless certify an exact one-state comparison:
decode the recorded binary32 objective and sampling-weight words into dyadic
rationals, enumerate every coordinate proposal, and check whether their
normalized weighted benefit is positive.

The checker in this file authenticates arithmetic over the supplied words.
Binding those words to a particular checkpoint, invocation, and measurement
site is a separate provenance obligation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32PointwiseCoordinateReplay

open Float32CheckpointMatrix
open ImportanceSampledCoordinateDescent
open PointwiseCoordinateReplay

noncomputable section

universe u

variable {Coordinate : Type u}
  [Fintype Coordinate] [Nonempty Coordinate]

/-- One objective value before a coordinate proposal, the objective after
each proposal, and the unnormalized positive weight assigned to each
proposal.  Every scalar is retained as its original binary32 word. -/
structure Float32ReplayTable (Coordinate : Type u) where
  before : FiniteFloat32Word
  after : Coordinate → FiniteFloat32Word
  weight : Coordinate → FiniteFloat32Word

def Float32ReplayTable.beforeRat
    (table : Float32ReplayTable Coordinate) : ℚ :=
  table.before.toRat

def Float32ReplayTable.afterRat
    (table : Float32ReplayTable Coordinate) (coordinate : Coordinate) : ℚ :=
  (table.after coordinate).toRat

def Float32ReplayTable.weightRat
    (table : Float32ReplayTable Coordinate) (coordinate : Coordinate) : ℚ :=
  (table.weight coordinate).toRat

def Float32ReplayTable.benefitRat
    (table : Float32ReplayTable Coordinate) (coordinate : Coordinate) : ℚ :=
  table.beforeRat - table.afterRat coordinate

/-- Exact normalized expected benefit in `ℚ`. -/
def Float32ReplayTable.expectedBenefitRat
    (table : Float32ReplayTable Coordinate) : ℚ :=
  (∑ coordinate,
      table.weightRat coordinate * table.benefitRat coordinate) /
    ∑ coordinate, table.weightRat coordinate

def Float32ReplayTable.beforeReal
    (table : Float32ReplayTable Coordinate) : ℝ :=
  table.before.toReal

def Float32ReplayTable.afterReal
    (table : Float32ReplayTable Coordinate) (coordinate : Coordinate) : ℝ :=
  (table.after coordinate).toReal

def Float32ReplayTable.weightReal
    (table : Float32ReplayTable Coordinate) (coordinate : Coordinate) : ℝ :=
  (table.weight coordinate).toReal

/-- Executable positivity test for every enumerated weight. -/
def Float32ReplayTable.positiveWeightCheck
    (table : Float32ReplayTable Coordinate) : Bool :=
  by
    classical
    exact decide (∀ coordinate, 0 < table.weightRat coordinate)

/-- Accept exactly when all recorded weights are positive and the exact
normalized weighted benefit is positive. -/
def Float32ReplayTable.check
    (table : Float32ReplayTable Coordinate) : Bool :=
  table.positiveWeightCheck &&
    decide (0 < table.expectedBenefitRat)

omit [Nonempty Coordinate] in
theorem Float32ReplayTable.positiveWeightCheck_eq_true_iff
    (table : Float32ReplayTable Coordinate) :
    table.positiveWeightCheck = true ↔
      ∀ coordinate, 0 < table.weightRat coordinate := by
  simp [Float32ReplayTable.positiveWeightCheck]

omit [Nonempty Coordinate] in
theorem Float32ReplayTable.cast_expectedBenefitRat
    (table : Float32ReplayTable Coordinate) :
    (table.expectedBenefitRat : ℝ) =
      weightedAverage table.weightReal
        (replayBenefit table.beforeReal table.afterReal) := by
  simp [
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.weightRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightReal,
    Float32ReplayTable.beforeReal,
    Float32ReplayTable.afterReal,
    weightedAverage,
    totalWeight,
    replayBenefit,
    FiniteFloat32Word.toReal]

omit [Fintype Coordinate] [Nonempty Coordinate] in
theorem Float32ReplayTable.positiveWeightsReal
    (table : Float32ReplayTable Coordinate)
    (positiveRat :
      ∀ coordinate, 0 < table.weightRat coordinate) :
    ∀ coordinate, 0 < table.weightReal coordinate := by
  intro coordinate
  have rational :
      0 < (table.weight coordinate).toRat := by
    simpa [Float32ReplayTable.weightRat] using
      positiveRat coordinate
  have real :
      (0 : ℝ) < ((table.weight coordinate).toRat : ℝ) := by
    exact_mod_cast rational
  simpa [
    Float32ReplayTable.weightReal,
    FiniteFloat32Word.toReal] using real

/-- Re-express the real expected post-proposal objective using the exact
dyadic expected benefit checked from the recorded words. -/
theorem Float32ReplayTable.weightedAverage_after_eq
    (table : Float32ReplayTable Coordinate)
    (positiveRat :
      ∀ coordinate, 0 < table.weightRat coordinate) :
    weightedAverage table.weightReal table.afterReal =
      table.beforeReal - (table.expectedBenefitRat : ℝ) := by
  have positiveReal := table.positiveWeightsReal positiveRat
  rw [weightedAverage_after_eq_before_sub_benefit
    table.weightReal table.afterReal positiveReal table.beforeReal]
  rw [← table.cast_expectedBenefitRat]

/-- A successful word-level check yields strict expected descent for the
exact real values denoted by the same binary32 words. -/
theorem Float32ReplayTable.check_sound
    (table : Float32ReplayTable Coordinate)
    (accepted : table.check = true) :
    weightedAverage table.weightReal table.afterReal <
      table.beforeReal := by
  have pieces := Bool.and_eq_true_iff.mp accepted
  have positiveRat :
      ∀ coordinate, 0 < table.weightRat coordinate :=
    table.positiveWeightCheck_eq_true_iff.mp pieces.1
  have positiveReal := table.positiveWeightsReal positiveRat
  have benefitRat : 0 < table.expectedBenefitRat :=
    of_decide_eq_true pieces.2
  have benefitReal :
      0 <
        weightedAverage table.weightReal
          (replayBenefit table.beforeReal table.afterReal) := by
    rw [← table.cast_expectedBenefitRat]
    exact_mod_cast benefitRat
  exact
    (pointwiseExpectedDescent_iff_positiveBenefit
      table.weightReal table.afterReal positiveReal table.beforeReal).mpr
      benefitReal

/-! ## Exact comparison of two laws on one proposal table -/

/-- Two sampling laws over definitionally the same objective word and
coordinate-proposal words. -/
structure Float32SamplingComparison (Coordinate : Type u) where
  before : FiniteFloat32Word
  after : Coordinate → FiniteFloat32Word
  leftWeight : Coordinate → FiniteFloat32Word
  rightWeight : Coordinate → FiniteFloat32Word

def Float32SamplingComparison.leftTable
    (comparison : Float32SamplingComparison Coordinate) :
    Float32ReplayTable Coordinate where
  before := comparison.before
  after := comparison.after
  weight := comparison.leftWeight

def Float32SamplingComparison.rightTable
    (comparison : Float32SamplingComparison Coordinate) :
    Float32ReplayTable Coordinate where
  before := comparison.before
  after := comparison.after
  weight := comparison.rightWeight

/-- Accept when both laws have positive weights and the left law has strictly
greater exact expected benefit over the shared proposal table. -/
def Float32SamplingComparison.check
    (comparison : Float32SamplingComparison Coordinate) : Bool :=
  comparison.leftTable.positiveWeightCheck &&
    (comparison.rightTable.positiveWeightCheck &&
      decide (
        comparison.rightTable.expectedBenefitRat <
          comparison.leftTable.expectedBenefitRat))

/-- A successful comparison check proves that the left sampling law has the
strictly lower expected post-proposal objective over the shared table. -/
theorem Float32SamplingComparison.check_sound
    (comparison : Float32SamplingComparison Coordinate)
    (accepted : comparison.check = true) :
    weightedAverage comparison.leftTable.weightReal
        comparison.leftTable.afterReal <
      weightedAverage comparison.rightTable.weightReal
        comparison.rightTable.afterReal := by
  have outer := Bool.and_eq_true_iff.mp accepted
  have inner := Bool.and_eq_true_iff.mp outer.2
  have positiveLeftRat :
      ∀ coordinate,
        0 < comparison.leftTable.weightRat coordinate :=
    comparison.leftTable.positiveWeightCheck_eq_true_iff.mp outer.1
  have positiveRightRat :
      ∀ coordinate,
        0 < comparison.rightTable.weightRat coordinate :=
    comparison.rightTable.positiveWeightCheck_eq_true_iff.mp inner.1
  have benefitOrderRat :
      comparison.rightTable.expectedBenefitRat <
        comparison.leftTable.expectedBenefitRat :=
    of_decide_eq_true inner.2
  have benefitOrderReal :
      (comparison.rightTable.expectedBenefitRat : ℝ) <
        (comparison.leftTable.expectedBenefitRat : ℝ) := by
    exact_mod_cast benefitOrderRat
  rw [
    comparison.leftTable.weightedAverage_after_eq positiveLeftRat,
    comparison.rightTable.weightedAverage_after_eq positiveRightRat]
  change
    comparison.leftTable.beforeReal -
          (comparison.leftTable.expectedBenefitRat : ℝ) <
      comparison.leftTable.beforeReal -
          (comparison.rightTable.expectedBenefitRat : ℝ)
  linarith

/-! ## Exact mixed-benefit fixtures -/

def zeroWord : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveThree : FiniteFloat32Word where
  word := 1077936128
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def helpfulBiasedMixedReplay : Float32ReplayTable Bool where
  before := positiveOne
  after
    | false => zeroWord
    | true => positiveThree
  weight
    | false => positiveThree
    | true => positiveOne

def uniformMixedReplay : Float32ReplayTable Bool where
  before := positiveOne
  after
    | false => zeroWord
    | true => positiveThree
  weight := fun _coordinate => positiveOne

def helpfulBiasedVersusUniform :
    Float32SamplingComparison Bool where
  before := positiveOne
  after
    | false => zeroWord
    | true => positiveThree
  leftWeight
    | false => positiveThree
    | true => positiveOne
  rightWeight := fun _coordinate => positiveOne

def uniformVersusHelpfulBiased :
    Float32SamplingComparison Bool where
  before := positiveOne
  after
    | false => zeroWord
    | true => positiveThree
  leftWeight := fun _coordinate => positiveOne
  rightWeight
    | false => positiveThree
    | true => positiveOne

theorem helpfulBiasedMixedReplay_is_accepted :
    helpfulBiasedMixedReplay.check = true := by
  norm_num [
    Float32ReplayTable.check,
    Float32ReplayTable.positiveWeightCheck,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    helpfulBiasedMixedReplay,
    positiveThree,
    positiveOne,
    zeroWord,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa]

theorem helpfulBiasedMixedReplay_descends :
    weightedAverage helpfulBiasedMixedReplay.weightReal
        helpfulBiasedMixedReplay.afterReal <
      helpfulBiasedMixedReplay.beforeReal :=
  helpfulBiasedMixedReplay.check_sound
    helpfulBiasedMixedReplay_is_accepted

/-- Positive weights alone are insufficient: uniform sampling of the same
mixed proposal table is rejected because its exact expected objective rises. -/
theorem uniformMixedReplay_is_rejected :
    uniformMixedReplay.check = false := by
  norm_num [
    Float32ReplayTable.check,
    Float32ReplayTable.positiveWeightCheck,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    uniformMixedReplay,
    positiveThree,
    positiveOne,
    zeroWord,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa]

theorem helpfulBiasedVersusUniform_is_accepted :
    helpfulBiasedVersusUniform.check = true := by
  norm_num [
    Float32SamplingComparison.check,
    Float32SamplingComparison.leftTable,
    Float32SamplingComparison.rightTable,
    Float32ReplayTable.positiveWeightCheck,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    helpfulBiasedVersusUniform,
    positiveThree,
    positiveOne,
    zeroWord,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa]

theorem helpfulBiasedVersusUniform_is_better :
    weightedAverage helpfulBiasedVersusUniform.leftTable.weightReal
        helpfulBiasedVersusUniform.leftTable.afterReal <
      weightedAverage helpfulBiasedVersusUniform.rightTable.weightReal
        helpfulBiasedVersusUniform.rightTable.afterReal :=
  helpfulBiasedVersusUniform.check_sound
    helpfulBiasedVersusUniform_is_accepted

/-- Reversing the two positive sampling laws reverses the strict comparison,
so the executable checker rejects it. -/
theorem uniformVersusHelpfulBiased_is_rejected :
    uniformVersusHelpfulBiased.check = false := by
  norm_num [
    Float32SamplingComparison.check,
    Float32SamplingComparison.leftTable,
    Float32SamplingComparison.rightTable,
    Float32ReplayTable.positiveWeightCheck,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    uniformVersusHelpfulBiased,
    positiveThree,
    positiveOne,
    zeroWord,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa]

#print axioms Float32ReplayTable.cast_expectedBenefitRat
#print axioms Float32ReplayTable.weightedAverage_after_eq
#print axioms Float32ReplayTable.check_sound
#print axioms Float32SamplingComparison.check_sound
#print axioms helpfulBiasedMixedReplay_is_accepted
#print axioms helpfulBiasedMixedReplay_descends
#print axioms uniformMixedReplay_is_rejected
#print axioms helpfulBiasedVersusUniform_is_accepted
#print axioms helpfulBiasedVersusUniform_is_better
#print axioms uniformVersusHelpfulBiased_is_rejected

end

end Float32PointwiseCoordinateReplay

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
