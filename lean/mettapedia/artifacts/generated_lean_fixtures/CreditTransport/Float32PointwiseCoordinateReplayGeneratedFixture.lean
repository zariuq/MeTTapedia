import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32PointwiseCoordinateReplay

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace Float32PointwiseCoordinateReplayGeneratedFixture

open Float32CheckpointMatrix
open Float32PointwiseCoordinateReplay
open ImportanceSampledCoordinateDescent

noncomputable section

-- Source probe SHA-256: ec3564201c8a2cc1b3342c2b8ee7988914f9ceef13abd597bbad51919d88e0d1
-- Enumerated coordinates: 2.

def beforeWord : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord0 : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord1 : FiniteFloat32Word where
  word := 1077936128
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWords : Fin 2 → FiniteFloat32Word :=
  ![afterWord0, afterWord1]

def helpfulBiasedWeightWord0 : FiniteFloat32Word where
  word := 1077936128
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def helpfulBiasedWeightWord1 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def helpfulBiasedWeights : Fin 2 → FiniteFloat32Word :=
  ![helpfulBiasedWeightWord0, helpfulBiasedWeightWord1]

def helpfulBiasedReplay : Float32ReplayTable (Fin 2) where
  before := beforeWord
  after := afterWords
  weight := helpfulBiasedWeights

theorem helpfulBiasedReplay_is_accepted :
    helpfulBiasedReplay.check = true := by
  norm_num [
    Float32ReplayTable.check,
    Float32ReplayTable.positiveWeightCheck,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    helpfulBiasedReplay,
    afterWords,
    helpfulBiasedWeights,
    beforeWord,
    afterWord0,
    afterWord1,
    helpfulBiasedWeightWord0,
    helpfulBiasedWeightWord1,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa,
    Fin.sum_univ_succ]

theorem helpfulBiasedReplay_descends :
    weightedAverage helpfulBiasedReplay.weightReal
        helpfulBiasedReplay.afterReal <
      helpfulBiasedReplay.beforeReal :=
  helpfulBiasedReplay.check_sound helpfulBiasedReplay_is_accepted

def uniformWeightWord0 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord1 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeights : Fin 2 → FiniteFloat32Word :=
  ![uniformWeightWord0, uniformWeightWord1]

def uniformReplay : Float32ReplayTable (Fin 2) where
  before := beforeWord
  after := afterWords
  weight := uniformWeights

theorem uniformReplay_is_rejected :
    uniformReplay.check = false := by
  norm_num [
    Float32ReplayTable.check,
    Float32ReplayTable.positiveWeightCheck,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    uniformReplay,
    afterWords,
    uniformWeights,
    beforeWord,
    afterWord0,
    afterWord1,
    helpfulBiasedWeightWord0,
    helpfulBiasedWeightWord1,
    uniformWeightWord0,
    uniformWeightWord1,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa,
    Fin.sum_univ_succ]

def helpfulBiasedVersusUniformComparison :
    Float32SamplingComparison (Fin 2) where
  before := beforeWord
  after := afterWords
  leftWeight := helpfulBiasedWeights
  rightWeight := uniformWeights

theorem helpfulBiasedVersusUniformComparison_is_accepted :
    helpfulBiasedVersusUniformComparison.check = true := by
  norm_num [
    Float32SamplingComparison.check,
    Float32SamplingComparison.leftTable,
    Float32SamplingComparison.rightTable,
    Float32ReplayTable.check,
    Float32ReplayTable.positiveWeightCheck,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    helpfulBiasedVersusUniformComparison,
    afterWords,
    helpfulBiasedWeights,
    uniformWeights,
    beforeWord,
    afterWord0,
    afterWord1,
    helpfulBiasedWeightWord0,
    helpfulBiasedWeightWord1,
    uniformWeightWord0,
    uniformWeightWord1,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa,
    Fin.sum_univ_succ]

theorem helpfulBiasedVersusUniformComparison_left_is_better :
    weightedAverage
        helpfulBiasedVersusUniformComparison.leftTable.weightReal
        helpfulBiasedVersusUniformComparison.leftTable.afterReal <
      weightedAverage
        helpfulBiasedVersusUniformComparison.rightTable.weightReal
        helpfulBiasedVersusUniformComparison.rightTable.afterReal :=
  helpfulBiasedVersusUniformComparison.check_sound helpfulBiasedVersusUniformComparison_is_accepted

end

end Float32PointwiseCoordinateReplayGeneratedFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
