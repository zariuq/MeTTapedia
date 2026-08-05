import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineSiLUReplayCertificate

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedAffineSiLUMessyReplayBatchFixture

open Float32CheckpointMatrix
open Float32AffineReplayCertificate
open Float32ActivationReplayCertificate
open Float32AffineSiLUReplayCertificate
open RationalExpEnclosureCertificate
open RationalActivationEnclosureCertificate
open RationalRangeReducedExpEnclosureCertificate
open RationalRangeReducedActivationEnclosureCertificate

noncomputable section

-- Source probe SHA-256: 73e07f928513b525872a3c22a830bac75bc2c0a5878162666952383625652ec0
-- Affine sidecar SHA-256: 898e5f696d83018471e199559fa9b0993a86194cd1c37580f0bfadfcd6777689
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
    word := 1058157655
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 1052433121
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((9581655 : ℚ) / 16777216)
    runtimeValue := ((12245729 : ℚ) / 33554432)
    localError := ((338532309798055348366664053401422343678237039909305483085490541 : ℚ) / 2362613962177409331440891839117545895710467023128199166563544530419712)
    outputLower := ((25696726232826859540983708272752317546341217156590714738442240 : ℚ) / 70411411395873914729819754054537766805088629584201715869846541)
    outputUpper := ((25696726232826859540983708272752317546341217156590714738442240 : ℚ) / 70411382978481332404640073749945935479118437264209960894690291)
    expCertificate := {
      argument := ((-9581655 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((-9581655 : ℚ) / 16777216)
        terms := 8
        lower := ((25417117739229604689465135164393382608496753438291761506251763 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((25417146156622187014644815468985213934466945758283516481408013 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((25417117739229604689465135164393382608496753438291761506251763 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      upper := ((25417146156622187014644815468985213934466945758283516481408013 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
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
  radius := ((9581655 : ℚ) / 16777216)

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
    word := 3205641303
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  output := {
    word := 3193117594
    word_lt_two_pow_32 := by norm_num
    exponent_lt_255 := by norm_num [float32Exponent]
  }
  enclosure := .rangeReduced {
    operation := .silu
    argument := ((-9581655 : ℚ) / 16777216)
    runtimeValue := ((-6917581 : ℚ) / 33554432)
    localError := ((157627437293966114789881590631066028919659141678805765645946729 : ℚ) / 4182377681244505485664461459057579810686021741698891871303873773699072)
    outputLower := ((-25696726232826859540983708272752317546341217156590714738442240 : ℚ) / 124644568003550335337652607532071465572298221042719241121526771)
    outputUpper := ((-25696726232826859540983708272752317546341217156590714738442240 : ℚ) / 124644596420942917662832287836663296898268413362710996096683021)
    expCertificate := {
      argument := ((9581655 : ℚ) / 16777216)
      halvings := 0
      reduced := {
        argument := ((9581655 : ℚ) / 16777216)
        terms := 8
        lower := ((79650302764298607622477668946518912701676537216801041733088243 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
        upper := ((79650331181691189947657349251110744027646729536792796708244493 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      }
      lower := ((79650302764298607622477668946518912701676537216801041733088243 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
      upper := ((79650331181691189947657349251110744027646729536792796708244493 : ℚ) / 44994265239251727715174938585552552870621683825918199388438528)
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
  radius := ((9581655 : ℚ) / 16777216)

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

end GeneratedAffineSiLUMessyReplayBatchFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
