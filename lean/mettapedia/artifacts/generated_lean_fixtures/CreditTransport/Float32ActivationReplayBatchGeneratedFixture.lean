import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayBatchCertificate

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedActivationReplayBatchFixture

open Float32CheckpointMatrix
open Float32ActivationReplayCertificate
open Float32ActivationReplayBatchCertificate
open RationalExpEnclosureCertificate
open RationalActivationEnclosureCertificate
open RationalRangeReducedExpEnclosureCertificate
open RationalRangeReducedActivationEnclosureCertificate

noncomputable section

-- Source probe SHA-256: 4204368886c7ec8750b0d4f2b8163df18868e02470da9dcbc788810d0dfd2124
-- Site 0, flat indices [0, 2).

def replay0 : Float32ActivationReplay where
  input := {
    word := 1056964608
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1050673152
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((1 : ℚ) / 2)
    runtimeValue := ((5 : ℚ) / 16)
    localError := ((85 : ℚ) / 61712)
    outputLower := ((1200 : ℚ) / 3857)
    outputUpper := ((2400 : ℚ) / 7711)
    expCertificate := {
      argument := ((-1 : ℚ) / 2)
      halvings := 0
      reduced := {
        argument := ((-1 : ℚ) / 2)
        terms := 5
        lower := ((2911 : ℚ) / 4800)
        upper := ((1457 : ℚ) / 2400)
      }
      lower := ((2911 : ℚ) / 4800)
      upper := ((1457 : ℚ) / 2400)
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
    word := 1073741824
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1071644672
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := (2 : ℚ)
    runtimeValue := ((7 : ℚ) / 4)
    localError := ((2697 : ℚ) / 181316)
    outputLower := ((80000 : ℚ) / 45929)
    outputUpper := ((80000 : ℚ) / 45329)
    expCertificate := {
      argument := (-2 : ℚ)
      halvings := 1
      reduced := {
        argument := (-1 : ℚ)
        terms := 5
        lower := ((73 : ℚ) / 200)
        upper := ((77 : ℚ) / 200)
      }
      lower := ((5329 : ℚ) / 40000)
      upper := ((5929 : ℚ) / 40000)
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

end GeneratedActivationReplayBatchFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
