import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineReplayCertificate

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedHiddenStageAffineReplayBatchFixture

open Float32CheckpointMatrix
open Float32AffineReplayCertificate

-- Source probe SHA-256: 73e07f928513b525872a3c22a830bac75bc2c0a5878162666952383625652ec0
-- Hidden affine site: 0 (base_hidden_transition)

def word0 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word1 : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word2 : FiniteFloat32Word where
  word := 1058157655
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word3 : FiniteFloat32Word where
  word := 3205641303
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def sharedWeight : Fin (1 * 1) → FiniteFloat32Word :=
  ![word0]

def sharedBias : Fin 1 → FiniteFloat32Word :=
  ![word1]

def replay0 : Float32AffineReplay 1 1 where
  input := ![word2]
  weight := sharedWeight
  bias := sharedBias
  output := ![word2]
  localError := (0 : ℚ)

theorem replay0_is_accepted : replay0.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat,
    replay0, word0, word1, word2, word3, sharedWeight, sharedBias,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

def replay1 : Float32AffineReplay 1 1 where
  input := ![word3]
  weight := sharedWeight
  bias := sharedBias
  output := ![word3]
  localError := (0 : ℚ)

theorem replay1_is_accepted : replay1.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat,
    replay1, word0, word1, word2, word3, sharedWeight, sharedBias,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

def certificateBatch : Float32AffineReplayBatch 1 1 where
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

end GeneratedHiddenStageAffineReplayBatchFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
