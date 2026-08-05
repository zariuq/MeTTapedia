import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32WorkNormalizedPointwiseReplay

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace Generation11PointwiseReplay

open Float32CheckpointMatrix
open Float32PointwiseCoordinateReplay
open Float32WorkNormalizedPointwiseReplay
open ImportanceSampledCoordinateDescent
open PointwiseCoordinateReplay
open WorkNormalizedPointwiseReplay

noncomputable section

-- Source probe SHA-256: c33008f04e26033d8b26367118057c5b77baeaa5a2539820b3b6e2b6ea68e9c4
-- Enumerated coordinates: 16.

def beforeWord : FiniteFloat32Word where
  word := 1065829613
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def declaredDrawWorkWord : FiniteFloat32Word where
  word := 1073741824
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord0 : FiniteFloat32Word where
  word := 1065829598
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord1 : FiniteFloat32Word where
  word := 1065829604
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord2 : FiniteFloat32Word where
  word := 1065829607
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord3 : FiniteFloat32Word where
  word := 1065829607
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord4 : FiniteFloat32Word where
  word := 1065829607
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord5 : FiniteFloat32Word where
  word := 1065829607
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord6 : FiniteFloat32Word where
  word := 1065829607
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord7 : FiniteFloat32Word where
  word := 1065829607
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord8 : FiniteFloat32Word where
  word := 1065829607
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord9 : FiniteFloat32Word where
  word := 1065829608
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord10 : FiniteFloat32Word where
  word := 1065829608
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord11 : FiniteFloat32Word where
  word := 1065829608
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord12 : FiniteFloat32Word where
  word := 1065829608
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord13 : FiniteFloat32Word where
  word := 1065829609
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord14 : FiniteFloat32Word where
  word := 1065829609
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWord15 : FiniteFloat32Word where
  word := 1065829609
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def afterWords : Fin 16 → FiniteFloat32Word :=
  ![afterWord0, afterWord1, afterWord2, afterWord3, afterWord4, afterWord5, afterWord6, afterWord7, afterWord8, afterWord9, afterWord10, afterWord11, afterWord12, afterWord13, afterWord14, afterWord15]

def squaredGradientWeightWord0 : FiniteFloat32Word where
  word := 949284580
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord1 : FiniteFloat32Word where
  word := 942111197
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord2 : FiniteFloat32Word where
  word := 940306765
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord3 : FiniteFloat32Word where
  word := 938796625
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord4 : FiniteFloat32Word where
  word := 938452060
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord5 : FiniteFloat32Word where
  word := 938052301
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord6 : FiniteFloat32Word where
  word := 937130946
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord7 : FiniteFloat32Word where
  word := 936987927
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord8 : FiniteFloat32Word where
  word := 936633173
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord9 : FiniteFloat32Word where
  word := 936248975
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord10 : FiniteFloat32Word where
  word := 936100079
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord11 : FiniteFloat32Word where
  word := 935943339
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord12 : FiniteFloat32Word where
  word := 935854595
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord13 : FiniteFloat32Word where
  word := 933930607
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord14 : FiniteFloat32Word where
  word := 933604791
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeightWord15 : FiniteFloat32Word where
  word := 933434042
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def squaredGradientWeights : Fin 16 → FiniteFloat32Word :=
  ![squaredGradientWeightWord0, squaredGradientWeightWord1, squaredGradientWeightWord2, squaredGradientWeightWord3, squaredGradientWeightWord4, squaredGradientWeightWord5, squaredGradientWeightWord6, squaredGradientWeightWord7, squaredGradientWeightWord8, squaredGradientWeightWord9, squaredGradientWeightWord10, squaredGradientWeightWord11, squaredGradientWeightWord12, squaredGradientWeightWord13, squaredGradientWeightWord14, squaredGradientWeightWord15]

theorem squaredGradientWeights_toRat_pos (coordinate : Fin 16) :
    0 < (squaredGradientWeights coordinate).toRat := by
  fin_cases coordinate <;>
    norm_num [
      squaredGradientWeights,
      squaredGradientWeightWord0,
      squaredGradientWeightWord1,
      squaredGradientWeightWord2,
      squaredGradientWeightWord3,
      squaredGradientWeightWord4,
      squaredGradientWeightWord5,
      squaredGradientWeightWord6,
      squaredGradientWeightWord7,
      squaredGradientWeightWord8,
      squaredGradientWeightWord9,
      squaredGradientWeightWord10,
      squaredGradientWeightWord11,
      squaredGradientWeightWord12,
      squaredGradientWeightWord13,
      squaredGradientWeightWord14,
      squaredGradientWeightWord15,
      FiniteFloat32Word.toRat,
      float32Exponent,
      float32Mantissa]

def squaredGradientReplay : Float32ReplayTable (Fin 16) where
  before := beforeWord
  after := afterWords
  weight := squaredGradientWeights

theorem squaredGradientReplay_is_accepted :
    squaredGradientReplay.check = true := by
  have positiveWeights :
      squaredGradientReplay.positiveWeightCheck = true :=
    (Float32ReplayTable.positiveWeightCheck_eq_true_iff
      squaredGradientReplay).mpr fun coordinate => by
      simpa [
        Float32ReplayTable.weightRat,
        squaredGradientReplay] using
        squaredGradientWeights_toRat_pos coordinate
  rw [Float32ReplayTable.check, positiveWeights]
  norm_num [
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    squaredGradientReplay,
    afterWords,
    squaredGradientWeights,
    beforeWord,
    declaredDrawWorkWord,
    afterWord0,
    afterWord1,
    afterWord2,
    afterWord3,
    afterWord4,
    afterWord5,
    afterWord6,
    afterWord7,
    afterWord8,
    afterWord9,
    afterWord10,
    afterWord11,
    afterWord12,
    afterWord13,
    afterWord14,
    afterWord15,
    squaredGradientWeightWord0,
    squaredGradientWeightWord1,
    squaredGradientWeightWord2,
    squaredGradientWeightWord3,
    squaredGradientWeightWord4,
    squaredGradientWeightWord5,
    squaredGradientWeightWord6,
    squaredGradientWeightWord7,
    squaredGradientWeightWord8,
    squaredGradientWeightWord9,
    squaredGradientWeightWord10,
    squaredGradientWeightWord11,
    squaredGradientWeightWord12,
    squaredGradientWeightWord13,
    squaredGradientWeightWord14,
    squaredGradientWeightWord15,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa,
    Fin.sum_univ_succ]

theorem squaredGradientReplay_descends :
    weightedAverage squaredGradientReplay.weightReal
        squaredGradientReplay.afterReal <
      squaredGradientReplay.beforeReal :=
  squaredGradientReplay.check_sound squaredGradientReplay_is_accepted

def uniformWeightWord0 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord1 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord2 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord3 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord4 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord5 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord6 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord7 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord8 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord9 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord10 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord11 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord12 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord13 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord14 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeightWord15 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def uniformWeights : Fin 16 → FiniteFloat32Word :=
  ![uniformWeightWord0, uniformWeightWord1, uniformWeightWord2, uniformWeightWord3, uniformWeightWord4, uniformWeightWord5, uniformWeightWord6, uniformWeightWord7, uniformWeightWord8, uniformWeightWord9, uniformWeightWord10, uniformWeightWord11, uniformWeightWord12, uniformWeightWord13, uniformWeightWord14, uniformWeightWord15]

theorem uniformWeights_toRat_pos (coordinate : Fin 16) :
    0 < (uniformWeights coordinate).toRat := by
  fin_cases coordinate <;>
    norm_num [
      uniformWeights,
      uniformWeightWord0,
      uniformWeightWord1,
      uniformWeightWord2,
      uniformWeightWord3,
      uniformWeightWord4,
      uniformWeightWord5,
      uniformWeightWord6,
      uniformWeightWord7,
      uniformWeightWord8,
      uniformWeightWord9,
      uniformWeightWord10,
      uniformWeightWord11,
      uniformWeightWord12,
      uniformWeightWord13,
      uniformWeightWord14,
      uniformWeightWord15,
      FiniteFloat32Word.toRat,
      float32Exponent,
      float32Mantissa]

def uniformReplay : Float32ReplayTable (Fin 16) where
  before := beforeWord
  after := afterWords
  weight := uniformWeights

theorem uniformReplay_is_accepted :
    uniformReplay.check = true := by
  have positiveWeights :
      uniformReplay.positiveWeightCheck = true :=
    (Float32ReplayTable.positiveWeightCheck_eq_true_iff
      uniformReplay).mpr fun coordinate => by
      simpa [
        Float32ReplayTable.weightRat,
        uniformReplay] using
        uniformWeights_toRat_pos coordinate
  rw [Float32ReplayTable.check, positiveWeights]
  norm_num [
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    uniformReplay,
    afterWords,
    uniformWeights,
    beforeWord,
    declaredDrawWorkWord,
    afterWord0,
    afterWord1,
    afterWord2,
    afterWord3,
    afterWord4,
    afterWord5,
    afterWord6,
    afterWord7,
    afterWord8,
    afterWord9,
    afterWord10,
    afterWord11,
    afterWord12,
    afterWord13,
    afterWord14,
    afterWord15,
    squaredGradientWeightWord0,
    squaredGradientWeightWord1,
    squaredGradientWeightWord2,
    squaredGradientWeightWord3,
    squaredGradientWeightWord4,
    squaredGradientWeightWord5,
    squaredGradientWeightWord6,
    squaredGradientWeightWord7,
    squaredGradientWeightWord8,
    squaredGradientWeightWord9,
    squaredGradientWeightWord10,
    squaredGradientWeightWord11,
    squaredGradientWeightWord12,
    squaredGradientWeightWord13,
    squaredGradientWeightWord14,
    squaredGradientWeightWord15,
    uniformWeightWord0,
    uniformWeightWord1,
    uniformWeightWord2,
    uniformWeightWord3,
    uniformWeightWord4,
    uniformWeightWord5,
    uniformWeightWord6,
    uniformWeightWord7,
    uniformWeightWord8,
    uniformWeightWord9,
    uniformWeightWord10,
    uniformWeightWord11,
    uniformWeightWord12,
    uniformWeightWord13,
    uniformWeightWord14,
    uniformWeightWord15,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa,
    Fin.sum_univ_succ]

theorem uniformReplay_descends :
    weightedAverage uniformReplay.weightReal
        uniformReplay.afterReal <
      uniformReplay.beforeReal :=
  uniformReplay.check_sound uniformReplay_is_accepted

def squaredGradientVersusUniformComparison :
    Float32SamplingComparison (Fin 16) where
  before := beforeWord
  after := afterWords
  leftWeight := squaredGradientWeights
  rightWeight := uniformWeights

theorem squaredGradientVersusUniformComparison_is_accepted :
    squaredGradientVersusUniformComparison.check = true := by
  have leftPositive :
      squaredGradientVersusUniformComparison.leftTable.positiveWeightCheck =
        true :=
    (Float32ReplayTable.positiveWeightCheck_eq_true_iff
      squaredGradientVersusUniformComparison.leftTable).mpr fun coordinate => by
      simpa [
        Float32SamplingComparison.leftTable,
        Float32ReplayTable.weightRat,
        squaredGradientVersusUniformComparison] using
        squaredGradientWeights_toRat_pos coordinate
  have rightPositive :
      squaredGradientVersusUniformComparison.rightTable.positiveWeightCheck =
        true :=
    (Float32ReplayTable.positiveWeightCheck_eq_true_iff
      squaredGradientVersusUniformComparison.rightTable).mpr fun coordinate => by
      simpa [
        Float32SamplingComparison.rightTable,
        Float32ReplayTable.weightRat,
        squaredGradientVersusUniformComparison] using
        uniformWeights_toRat_pos coordinate
  rw [
    Float32SamplingComparison.check,
    leftPositive,
    rightPositive]
  norm_num [
    Float32SamplingComparison.leftTable,
    Float32SamplingComparison.rightTable,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    squaredGradientVersusUniformComparison,
    afterWords,
    squaredGradientWeights,
    uniformWeights,
    beforeWord,
    declaredDrawWorkWord,
    afterWord0,
    afterWord1,
    afterWord2,
    afterWord3,
    afterWord4,
    afterWord5,
    afterWord6,
    afterWord7,
    afterWord8,
    afterWord9,
    afterWord10,
    afterWord11,
    afterWord12,
    afterWord13,
    afterWord14,
    afterWord15,
    squaredGradientWeightWord0,
    squaredGradientWeightWord1,
    squaredGradientWeightWord2,
    squaredGradientWeightWord3,
    squaredGradientWeightWord4,
    squaredGradientWeightWord5,
    squaredGradientWeightWord6,
    squaredGradientWeightWord7,
    squaredGradientWeightWord8,
    squaredGradientWeightWord9,
    squaredGradientWeightWord10,
    squaredGradientWeightWord11,
    squaredGradientWeightWord12,
    squaredGradientWeightWord13,
    squaredGradientWeightWord14,
    squaredGradientWeightWord15,
    uniformWeightWord0,
    uniformWeightWord1,
    uniformWeightWord2,
    uniformWeightWord3,
    uniformWeightWord4,
    uniformWeightWord5,
    uniformWeightWord6,
    uniformWeightWord7,
    uniformWeightWord8,
    uniformWeightWord9,
    uniformWeightWord10,
    uniformWeightWord11,
    uniformWeightWord12,
    uniformWeightWord13,
    uniformWeightWord14,
    uniformWeightWord15,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa,
    Fin.sum_univ_succ]

def squaredGradientVersusUniformComparisonWork :
    Float32WorkComparison (Fin 16) where
  sampling := squaredGradientVersusUniformComparison
  leftWork := declaredDrawWorkWord
  rightWork := declaredDrawWorkWord

theorem squaredGradientVersusUniformComparisonWork_is_accepted :
    squaredGradientVersusUniformComparisonWork.check = true := by
  have leftPositive :
      squaredGradientVersusUniformComparisonWork.sampling.leftTable.positiveWeightCheck =
        true :=
    (Float32ReplayTable.positiveWeightCheck_eq_true_iff
      squaredGradientVersusUniformComparisonWork.sampling.leftTable).mpr
      fun coordinate => by
      simpa [
        squaredGradientVersusUniformComparisonWork,
        Float32SamplingComparison.leftTable,
        Float32ReplayTable.weightRat,
        squaredGradientVersusUniformComparison] using
        squaredGradientWeights_toRat_pos coordinate
  have rightPositive :
      squaredGradientVersusUniformComparisonWork.sampling.rightTable.positiveWeightCheck =
        true :=
    (Float32ReplayTable.positiveWeightCheck_eq_true_iff
      squaredGradientVersusUniformComparisonWork.sampling.rightTable).mpr
      fun coordinate => by
      simpa [
        squaredGradientVersusUniformComparisonWork,
        Float32SamplingComparison.rightTable,
        Float32ReplayTable.weightRat,
        squaredGradientVersusUniformComparison] using
        uniformWeights_toRat_pos coordinate
  rw [
    Float32WorkComparison.check,
    leftPositive,
    rightPositive]
  norm_num [
    Float32WorkComparison.positiveWorkCheck,
    Float32WorkComparison.leftWorkRat,
    Float32WorkComparison.rightWorkRat,
    squaredGradientVersusUniformComparisonWork,
    Float32SamplingComparison.leftTable,
    Float32SamplingComparison.rightTable,
    Float32ReplayTable.expectedBenefitRat,
    Float32ReplayTable.benefitRat,
    Float32ReplayTable.beforeRat,
    Float32ReplayTable.afterRat,
    Float32ReplayTable.weightRat,
    squaredGradientVersusUniformComparison,
    afterWords,
    squaredGradientWeights,
    uniformWeights,
    beforeWord,
    declaredDrawWorkWord,
    afterWord0,
    afterWord1,
    afterWord2,
    afterWord3,
    afterWord4,
    afterWord5,
    afterWord6,
    afterWord7,
    afterWord8,
    afterWord9,
    afterWord10,
    afterWord11,
    afterWord12,
    afterWord13,
    afterWord14,
    afterWord15,
    squaredGradientWeightWord0,
    squaredGradientWeightWord1,
    squaredGradientWeightWord2,
    squaredGradientWeightWord3,
    squaredGradientWeightWord4,
    squaredGradientWeightWord5,
    squaredGradientWeightWord6,
    squaredGradientWeightWord7,
    squaredGradientWeightWord8,
    squaredGradientWeightWord9,
    squaredGradientWeightWord10,
    squaredGradientWeightWord11,
    squaredGradientWeightWord12,
    squaredGradientWeightWord13,
    squaredGradientWeightWord14,
    squaredGradientWeightWord15,
    uniformWeightWord0,
    uniformWeightWord1,
    uniformWeightWord2,
    uniformWeightWord3,
    uniformWeightWord4,
    uniformWeightWord5,
    uniformWeightWord6,
    uniformWeightWord7,
    uniformWeightWord8,
    uniformWeightWord9,
    uniformWeightWord10,
    uniformWeightWord11,
    uniformWeightWord12,
    uniformWeightWord13,
    uniformWeightWord14,
    uniformWeightWord15,
    FiniteFloat32Word.toRat,
    float32Exponent,
    float32Mantissa,
    Fin.sum_univ_succ]

theorem squaredGradientVersusUniformComparisonWork_left_is_better :
    expectedBenefitPerWork
        squaredGradientVersusUniformComparisonWork.sampling.rightTable.weightReal
        (replayBenefit
          squaredGradientVersusUniformComparisonWork.sampling.rightTable.beforeReal
          squaredGradientVersusUniformComparisonWork.sampling.rightTable.afterReal)
        squaredGradientVersusUniformComparisonWork.rightWorkReal <
      expectedBenefitPerWork
        squaredGradientVersusUniformComparisonWork.sampling.leftTable.weightReal
        (replayBenefit
          squaredGradientVersusUniformComparisonWork.sampling.leftTable.beforeReal
          squaredGradientVersusUniformComparisonWork.sampling.leftTable.afterReal)
        squaredGradientVersusUniformComparisonWork.leftWorkReal :=
  squaredGradientVersusUniformComparisonWork.check_sound
    squaredGradientVersusUniformComparisonWork_is_accepted

theorem squaredGradientVersusUniformComparison_left_is_better :
    weightedAverage
        squaredGradientVersusUniformComparison.leftTable.weightReal
        squaredGradientVersusUniformComparison.leftTable.afterReal <
      weightedAverage
        squaredGradientVersusUniformComparison.rightTable.weightReal
        squaredGradientVersusUniformComparison.rightTable.afterReal :=
  squaredGradientVersusUniformComparison.check_sound squaredGradientVersusUniformComparison_is_accepted

end

end Generation11PointwiseReplay
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
