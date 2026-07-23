import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineReplayCertificate

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedAffineReplayBatchFixture

open Float32CheckpointMatrix
open Float32AffineReplayCertificate

-- Source probe SHA-256: 4ce991ddc31493ab097d31c7fe569e133274f39a08036fbf04d7638a5cb21432
-- Hidden affine site: 0 (base_hidden_transition)

def word0 : FiniteFloat32Word where
  word := 1077936128
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word1 : FiniteFloat32Word where
  word := 1082130432
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word2 : FiniteFloat32Word where
  word := 1084227584
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word3 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word4 : FiniteFloat32Word where
  word := 1073741824
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word5 : FiniteFloat32Word where
  word := 1098907648
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def sharedWeight : Fin (1 * 2) → FiniteFloat32Word :=
  ![word0, word1]

def sharedBias : Fin 1 → FiniteFloat32Word :=
  ![word2]

def replay0 : Float32AffineReplay 1 2 where
  input := ![word3, word4]
  weight := sharedWeight
  bias := sharedBias
  output := ![word5]
  localError := (0 : ℚ)

theorem replay0_is_accepted : replay0.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat,
    replay0, word0, word1, word2, word3, word4, word5, sharedWeight, sharedBias,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

def replay1 : Float32AffineReplay 1 2 where
  input := ![word3, word4]
  weight := sharedWeight
  bias := sharedBias
  output := ![word5]
  localError := (0 : ℚ)

theorem replay1_is_accepted : replay1.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat,
    replay1, word0, word1, word2, word3, word4, word5, sharedWeight, sharedBias,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

def certificateBatch : Float32AffineReplayBatch 1 2 where
  expectedCount := 2
  entries := [replay0, replay1]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [certificateBatch, Float32AffineReplayBatch.check,
    replay0_is_accepted, replay1_is_accepted]

theorem certificateBatch_total_error_is_bounded :
    certificateBatch.totalObservedError ≤
      certificateBatch.totalCertifiedError :=
  certificateBatch.totalObservedError_le certificateBatch_is_accepted

#print axioms certificateBatch_is_accepted
#print axioms certificateBatch_total_error_is_bounded

end GeneratedAffineReplayBatchFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
