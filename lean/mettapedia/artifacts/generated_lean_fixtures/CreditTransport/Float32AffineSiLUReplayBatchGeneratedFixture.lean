import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineSiLUReplayCertificate

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedAffineSiLUReplayBatchFixture

open Float32CheckpointMatrix
open Float32AffineReplayCertificate
open Float32ActivationReplayCertificate
open Float32AffineSiLUReplayCertificate
open RationalExpEnclosureCertificate
open RationalActivationEnclosureCertificate
open RationalRangeReducedExpEnclosureCertificate
open RationalRangeReducedActivationEnclosureCertificate

noncomputable section

-- Source probe SHA-256: 3a919234edb95095a834c77b9e8a19832a21c83596049d4b922784912d7912ce
-- Affine sidecar SHA-256: 61b9788cdcd535eb9f4fa48614056a464740309470384de79d7cffd0d5bd5cfc
-- Sidecar hashes are provenance metadata; the kernel checks the payload below.
-- Hidden affine-SiLU site: 0 (base_hidden_transition)

def word0 : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word1 : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word2 : FiniteFloat32Word where
  word := 1056964608
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def word3 : FiniteFloat32Word where
  word := 1073741824
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def sharedWeight : Fin (1 * 1) → FiniteFloat32Word :=
  ![word0]

def sharedBias : Fin 1 → FiniteFloat32Word :=
  ![word1]

def affineReplay0 : Float32AffineReplay 1 1 where
  input := ![word2]
  weight := sharedWeight
  bias := sharedBias
  output := ![word2]
  localError := (0 : ℚ)

theorem affineReplay0_is_accepted : affineReplay0.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat,
    affineReplay0, word0, word1, word2, word3, sharedWeight, sharedBias,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

def activation0_0 : Float32ActivationReplay where
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
  radius := ((1 : ℚ) / 2)

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
        word0, word1, word2, word3, sharedWeight, sharedBias,
        FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]
    · norm_num [replay0, affineReplay0,
        Float32AffineReplay.idealOutputRat,
        word0, word1, word2, word3, sharedWeight, sharedBias,
        FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
        rowMajorIndex]

def affineReplay1 : Float32AffineReplay 1 1 where
  input := ![word3]
  weight := sharedWeight
  bias := sharedBias
  output := ![word3]
  localError := (0 : ℚ)

theorem affineReplay1_is_accepted : affineReplay1.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat,
    affineReplay1, word0, word1, word2, word3, sharedWeight, sharedBias,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa,
    rowMajorIndex]

def activation1_0 : Float32ActivationReplay where
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
  radius := (2 : ℚ)

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
        word0, word1, word2, word3, sharedWeight, sharedBias,
        FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]
    · norm_num [replay1, affineReplay1,
        Float32AffineReplay.idealOutputRat,
        word0, word1, word2, word3, sharedWeight, sharedBias,
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

end GeneratedAffineSiLUReplayBatchFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
