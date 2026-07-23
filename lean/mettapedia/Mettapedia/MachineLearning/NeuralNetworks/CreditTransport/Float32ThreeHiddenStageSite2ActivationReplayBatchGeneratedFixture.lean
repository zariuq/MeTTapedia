import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayBatchCertificate

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedThreeHiddenStageSite2ActivationReplayBatchFixture

open Float32CheckpointMatrix
open Float32ActivationReplayCertificate
open Float32ActivationReplayBatchCertificate
open RationalExpEnclosureCertificate
open RationalActivationEnclosureCertificate
open RationalRangeReducedExpEnclosureCertificate
open RationalRangeReducedActivationEnclosureCertificate

noncomputable section

-- Source probe SHA-256: 68a5a3a1aa70540ec9b2f9f2cbe892b52c7c8e579eb2b8a0adb1aba9db262167
-- Site 2, flat indices [0, 2).

def replay0 : Float32ActivationReplay where
  input := {
    word := 0
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 0
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := (0 : ℚ)
    runtimeValue := (0 : ℚ)
    localError := (0 : ℚ)
    outputLower := (0 : ℚ)
    outputUpper := (0 : ℚ)
    expCertificate := {
      argument := (0 : ℚ)
      halvings := 0
      reduced := {
        argument := (0 : ℚ)
        terms := 8
        lower := (1 : ℚ)
        upper := (1 : ℚ)
      }
      lower := (1 : ℚ)
      upper := (1 : ℚ)
    }
  }

theorem replay0_is_accepted : replay0.check = true := by
  norm_num [replay0, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay1 : Float32ActivationReplay where
  input := {
    word := 0
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 0
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := (0 : ℚ)
    runtimeValue := (0 : ℚ)
    localError := (0 : ℚ)
    outputLower := (0 : ℚ)
    outputUpper := (0 : ℚ)
    expCertificate := {
      argument := (0 : ℚ)
      halvings := 0
      reduced := {
        argument := (0 : ℚ)
        terms := 8
        lower := (1 : ℚ)
        upper := (1 : ℚ)
      }
      lower := (1 : ℚ)
      upper := (1 : ℚ)
    }
  }

theorem replay1_is_accepted : replay1.check = true := by
  norm_num [replay1, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def certificateBatch : Float32ActivationReplayBatch where
  expectedCount := 2
  entries := [replay0, replay1]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [certificateBatch, Float32ActivationReplayBatch.check,
    replay0_is_accepted, replay1_is_accepted]

theorem certificateBatch_total_error_is_bounded :
    certificateBatch.totalAbsoluteError ≤ certificateBatch.totalCertifiedError :=
  certificateBatch.totalAbsoluteError_le certificateBatch_is_accepted

#print axioms certificateBatch_is_accepted
#print axioms certificateBatch_total_error_is_bounded

end

end GeneratedThreeHiddenStageSite2ActivationReplayBatchFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
