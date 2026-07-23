import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineReplayCertificate

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace UnifiedCarrierDecisionSiteFixture

open Float32CheckpointMatrix
open Float32AffineReplayCertificate

-- Source probe SHA-256: 9b50e1afb93e89cfbdc6748389c6bb92a902ad25c1777a7a3603216a1ffe0db6
-- Hidden affine site: 0 (unified_carrier_evidence_output_projection)

def word0 : FiniteFloat32Word where
  word := 1055823838
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word1 : FiniteFloat32Word where
  word := 3203113100
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word2 : FiniteFloat32Word where
  word := 3196138574
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word3 : FiniteFloat32Word where
  word := 3190597704
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word4 : FiniteFloat32Word where
  word := 1052264170
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word5 : FiniteFloat32Word where
  word := 3201812860
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word6 : FiniteFloat32Word where
  word := 1046632284
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word7 : FiniteFloat32Word where
  word := 3196171520
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word8 : FiniteFloat32Word where
  word := 1051036134
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word9 : FiniteFloat32Word where
  word := 3196372298
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word10 : FiniteFloat32Word where
  word := 3204285010
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word11 : FiniteFloat32Word where
  word := 3194193892
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word12 : FiniteFloat32Word where
  word := 3196364292
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word13 : FiniteFloat32Word where
  word := 1054394906
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word14 : FiniteFloat32Word where
  word := 3196408066
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word15 : FiniteFloat32Word where
  word := 1056552212
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word16 : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word17 : FiniteFloat32Word where
  word := 1058457172
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word18 : FiniteFloat32Word where
  word := 1055407628
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word19 : FiniteFloat32Word where
  word := 1050189217
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word20 : FiniteFloat32Word where
  word := 1049536537
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word21 : FiniteFloat32Word where
  word := 3177669548
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word22 : FiniteFloat32Word where
  word := 1015279176
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word23 : FiniteFloat32Word where
  word := 3188456383
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word24 : FiniteFloat32Word where
  word := 1036529581
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def weightRow0 : Fin 4 → FiniteFloat32Word :=
  ![word0, word1, word2, word3]

def weightRow1 : Fin 4 → FiniteFloat32Word :=
  ![word4, word5, word6, word7]

def weightRow2 : Fin 4 → FiniteFloat32Word :=
  ![word8, word9, word10, word11]

def weightRow3 : Fin 4 → FiniteFloat32Word :=
  ![word12, word13, word14, word15]

def sharedWeightRows : Fin 4 → Fin 4 → FiniteFloat32Word :=
  ![weightRow0, weightRow1, weightRow2, weightRow3]

def sharedBias : Fin 4 → FiniteFloat32Word :=
  ![word16, word16, word16, word16]

def replay0Input : Fin 4 → FiniteFloat32Word :=
  ![word17, word18, word19, word20]

def replay0Output : Fin 4 → FiniteFloat32Word :=
  ![word21, word22, word23, word24]

def replay0 : Float32AffineReplay 4 4 :=
  Float32AffineReplay.ofRows
    replay0Input
    sharedWeightRows
    sharedBias
    replay0Output
    ((14174825 : ℚ) / 562949953421312)

def replay0CoordinateBudget : Fin 4 → ℚ :=
  ![((3471289 : ℚ) / 562949953421312),
    ((5159785 : ℚ) / 562949953421312),
    ((1817169 : ℚ) / 281474976710656),
    ((1909413 : ℚ) / 562949953421312)]

set_option maxHeartbeats 800000 in
theorem replay0_coordinate0_arithmetic :
    |word21.toRat -
      (word16.toRat +
        ∑ column, (weightRow0 column).toRat *
          (replay0Input column).toRat)| ≤
      ((3471289 : ℚ) / 562949953421312) := by
  norm_num [replay0Input, weightRow0, word0, word1, word2, word3,
    word16, word17, word18, word19, word20, word21,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    Fin.sum_univ_succ]

theorem replay0_coordinate0_is_bounded :
    |(replay0.output 0).toRat - replay0.idealOutputRat 0| ≤
      replay0CoordinateBudget 0 := by
  simpa [replay0, replay0Output, sharedBias, sharedWeightRows,
    replay0CoordinateBudget] using
    (Float32AffineReplay.ofRows_coordinate_bound
      replay0Input sharedWeightRows sharedBias replay0Output
      ((14174825 : ℚ) / 562949953421312)
      (replay0CoordinateBudget 0) 0 replay0_coordinate0_arithmetic)

set_option maxHeartbeats 800000 in
theorem replay0_coordinate1_arithmetic :
    |word22.toRat -
      (word16.toRat +
        ∑ column, (weightRow1 column).toRat *
          (replay0Input column).toRat)| ≤
      ((5159785 : ℚ) / 562949953421312) := by
  norm_num [replay0Input, weightRow1, word4, word5, word6, word7,
    word16, word17, word18, word19, word20, word22,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    Fin.sum_univ_succ]

theorem replay0_coordinate1_is_bounded :
    |(replay0.output 1).toRat - replay0.idealOutputRat 1| ≤
      replay0CoordinateBudget 1 := by
  simpa [replay0, replay0Output, sharedBias, sharedWeightRows,
    replay0CoordinateBudget] using
    (Float32AffineReplay.ofRows_coordinate_bound
      replay0Input sharedWeightRows sharedBias replay0Output
      ((14174825 : ℚ) / 562949953421312)
      (replay0CoordinateBudget 1) 1 replay0_coordinate1_arithmetic)

set_option maxHeartbeats 800000 in
theorem replay0_coordinate2_arithmetic :
    |word23.toRat -
      (word16.toRat +
        ∑ column, (weightRow2 column).toRat *
          (replay0Input column).toRat)| ≤
      ((1817169 : ℚ) / 281474976710656) := by
  norm_num [replay0Input, weightRow2, word8, word9, word10, word11,
    word16, word17, word18, word19, word20, word23,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    Fin.sum_univ_succ]

theorem replay0_coordinate2_is_bounded :
    |(replay0.output 2).toRat - replay0.idealOutputRat 2| ≤
      replay0CoordinateBudget 2 := by
  simpa [replay0, replay0Output, sharedBias, sharedWeightRows,
    replay0CoordinateBudget] using
    (Float32AffineReplay.ofRows_coordinate_bound
      replay0Input sharedWeightRows sharedBias replay0Output
      ((14174825 : ℚ) / 562949953421312)
      (replay0CoordinateBudget 2) 2 replay0_coordinate2_arithmetic)

set_option maxHeartbeats 800000 in
theorem replay0_coordinate3_arithmetic :
    |word24.toRat -
      (word16.toRat +
        ∑ column, (weightRow3 column).toRat *
          (replay0Input column).toRat)| ≤
      ((1909413 : ℚ) / 562949953421312) := by
  norm_num [replay0Input, weightRow3, word12, word13, word14, word15,
    word16, word17, word18, word19, word20, word24,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    Fin.sum_univ_succ]

theorem replay0_coordinate3_is_bounded :
    |(replay0.output 3).toRat - replay0.idealOutputRat 3| ≤
      replay0CoordinateBudget 3 := by
  simpa [replay0, replay0Output, sharedBias, sharedWeightRows,
    replay0CoordinateBudget] using
    (Float32AffineReplay.ofRows_coordinate_bound
      replay0Input sharedWeightRows sharedBias replay0Output
      ((14174825 : ℚ) / 562949953421312)
      (replay0CoordinateBudget 3) 3 replay0_coordinate3_arithmetic)

theorem replay0_all_coordinates_are_bounded : ∀ row,
    |(replay0.output row).toRat - replay0.idealOutputRat row| ≤
      replay0CoordinateBudget row := by
  intro row
  fin_cases row
  · exact replay0_coordinate0_is_bounded
  · exact replay0_coordinate1_is_bounded
  · exact replay0_coordinate2_is_bounded
  · exact replay0_coordinate3_is_bounded

theorem replay0_is_accepted : replay0.check = true := by
  refine replay0.check_of_coordinate_bounds replay0CoordinateBudget
    (by norm_num) (by norm_num)
    (by norm_num [replay0, Float32AffineReplay.ofRows])
    replay0_all_coordinates_are_bounded ?_
  norm_num [replay0, Float32AffineReplay.ofRows,
    replay0CoordinateBudget, Fin.sum_univ_succ]

def certificateBatch : Float32AffineReplayBatch 4 4 where
  expectedCount := 1
  entries := [replay0]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [certificateBatch, Float32AffineReplayBatch.check,
    replay0_is_accepted]

theorem certificateBatch_total_error_is_bounded :
    certificateBatch.totalObservedError ≤
      certificateBatch.totalCertifiedError :=
  certificateBatch.totalObservedError_le certificateBatch_is_accepted

#print axioms certificateBatch_is_accepted
#print axioms certificateBatch_total_error_is_bounded

end UnifiedCarrierDecisionSiteFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
