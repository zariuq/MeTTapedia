import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineSiLUReplayCertificate

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedThreeHiddenStageSite1AffineSiLUReplayBatchFixture

open Float32CheckpointMatrix
open Float32AffineReplayCertificate
open Float32ActivationReplayCertificate
open Float32AffineSiLUReplayCertificate
open RationalExpEnclosureCertificate
open RationalActivationEnclosureCertificate
open RationalRangeReducedExpEnclosureCertificate
open RationalRangeReducedActivationEnclosureCertificate

noncomputable section

-- Source probe SHA-256: 68a5a3a1aa70540ec9b2f9f2cbe892b52c7c8e579eb2b8a0adb1aba9db262167
-- Affine sidecar SHA-256: 555e6e5fee55a463d7d2ce67b043a955372da654b633bfe3db4377c426513398
-- Sidecar hashes are provenance metadata; the kernel checks the payload below.
-- Hidden affine-SiLU site: 1 (error_dependent_hidden_transition)

def word0 : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word1 : FiniteFloat32Word where
  word := 1055788564
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word2 : FiniteFloat32Word where
  word := 2147483648
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def sharedWeight : Fin (1 * 1) → FiniteFloat32Word :=
  ![word0]

def sharedBias : Fin 1 → FiniteFloat32Word :=
  ![word0]

def affineReplay0 : Float32AffineReplay 1 1 where
  input := ![word1]
  weight := sharedWeight
  bias := sharedBias
  output := ![word0]
  localError := (0 : ℚ)

theorem affineReplay0_is_accepted : affineReplay0.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat,
    affineReplay0, word0, word1, word2, sharedWeight, sharedBias,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

def activation0_0 : Float32ActivationReplay where
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

theorem activation0_0_is_accepted : activation0_0.check = true := by
  norm_num [activation0_0, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay0 : Float32AffineSiLUReplay 1 1 where
  affine := affineReplay0
  activation := ![activation0_0]
  radius := (0 : ℚ)

theorem replay0_is_accepted : replay0.check = true := by
  apply (Float32AffineSiLUReplay.check_eq_true_iff replay0).mpr
  refine ⟨(Float32AffineReplay.check_eq_true_iff affineReplay0).mp
      affineReplay0_is_accepted, by norm_num [replay0], ?_⟩
  intro row
  fin_cases row
  · refine ⟨(Float32ActivationReplay.check_eq_true_iff
        activation0_0).mp activation0_0_is_accepted,
        rfl, rfl, ?_, ?_⟩
    · norm_num [replay0, affineReplay0,
        word0, word1, word2, sharedWeight, sharedBias,
        FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]
    · norm_num [replay0, affineReplay0,
        Float32AffineReplay.idealOutputRat,
        word0, word1, word2, sharedWeight, sharedBias,
        FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
        rowMajorIndex]

def affineReplay1 : Float32AffineReplay 1 1 where
  input := ![word2]
  weight := sharedWeight
  bias := sharedBias
  output := ![word0]
  localError := (0 : ℚ)

theorem affineReplay1_is_accepted : affineReplay1.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat,
    affineReplay1, word0, word1, word2, sharedWeight, sharedBias,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

def activation1_0 : Float32ActivationReplay where
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

theorem activation1_0_is_accepted : activation1_0.check = true := by
  norm_num [activation1_0, Float32ActivationReplay.check,
    ActivationCertificate.check, ActivationCertificate.argument,
    ActivationCertificate.runtimeValue, RangeReducedActivationEnclosure.check,
    RangeReducedExpEnclosure.check, ExpEnclosure.check, expScale,
    expTaylorRat, expTaylorErrorRat, activationLowerRat,
    activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def replay1 : Float32AffineSiLUReplay 1 1 where
  affine := affineReplay1
  activation := ![activation1_0]
  radius := (0 : ℚ)

theorem replay1_is_accepted : replay1.check = true := by
  apply (Float32AffineSiLUReplay.check_eq_true_iff replay1).mpr
  refine ⟨(Float32AffineReplay.check_eq_true_iff affineReplay1).mp
      affineReplay1_is_accepted, by norm_num [replay1], ?_⟩
  intro row
  fin_cases row
  · refine ⟨(Float32ActivationReplay.check_eq_true_iff
        activation1_0).mp activation1_0_is_accepted,
        rfl, rfl, ?_, ?_⟩
    · norm_num [replay1, affineReplay1,
        word0, word1, word2, sharedWeight, sharedBias,
        FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]
    · norm_num [replay1, affineReplay1,
        Float32AffineReplay.idealOutputRat,
        word0, word1, word2, sharedWeight, sharedBias,
        FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
        rowMajorIndex]

def certificateBatch : Float32AffineSiLUReplayBatch 1 1 where
  expectedCount := 2
  entries := [replay0, replay1]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [certificateBatch, Float32AffineSiLUReplayBatch.check,
    replay0_is_accepted, replay1_is_accepted]

theorem certificateBatch_total_error_is_bounded :
    certificateBatch.totalObservedError ≤
      certificateBatch.totalCertifiedError :=
  certificateBatch.totalObservedError_le certificateBatch_is_accepted

#print axioms certificateBatch_is_accepted
#print axioms certificateBatch_total_error_is_bounded

end

end GeneratedThreeHiddenStageSite1AffineSiLUReplayBatchFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
