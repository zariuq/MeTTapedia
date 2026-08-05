import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32HiddenStageReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageSite2AffineSiLUReplayBatchGeneratedFixture
import Mathlib.Tactic

/-! This file is generated from authenticated source-side replay records.
The kernel checks only the exact word arithmetic and interior connections;
the recorded SHA-256 values bind those words to external source artifacts. -/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedThreeHiddenStageSite2HiddenStageReplayBatchFixture

open Float32CheckpointMatrix
open Float32AffineSiLUReplayCertificate
open Float32AddMaskReplayCertificate
open Float32HiddenStageReplayCertificate

noncomputable section

-- source probe SHA-256: 68a5a3a1aa70540ec9b2f9f2cbe892b52c7c8e579eb2b8a0adb1aba9db262167
-- affine-SiLU batch SHA-256: 5501397ba5b3c14f00e6e35d0e4944511cd3aa450eb962fe704440217531ff8a

def invocation0Row0Activation : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row0Error : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row0Sum : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row0Center : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation0Row0Add : Float32AddReplay where
  left := invocation0Row0Activation
  right := invocation0Row0Error
  output := invocation0Row0Sum
  localError := (0 : ℚ)

def invocation0Row0Mask : Float32MaskReplay where
  active := true
  input := invocation0Row0Sum
  output := invocation0Row0Center
  localError := (0 : ℚ)

def invocation0Row0AddMask : Float32AddMaskReplay where
  add := invocation0Row0Add
  mask := invocation0Row0Mask

theorem invocation0Row0AddMask_is_accepted : invocation0Row0AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation0Row0AddMask, invocation0Row0Add, invocation0Row0Mask,
    boolRat, invocation0Row0Activation, invocation0Row0Error, invocation0Row0Sum, invocation0Row0Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def hiddenReplay0 : Float32HiddenStageReplay 1 1 where
  affineSiLU := GeneratedThreeHiddenStageSite2AffineSiLUReplayBatchFixture.replay0
  errorSite := ![invocation0Row0Error]
  addMask := ![invocation0Row0AddMask]

theorem hiddenReplay0_is_accepted : hiddenReplay0.check = true := by
  apply (Float32HiddenStageReplay.check_eq_true_iff hiddenReplay0).mpr
  refine ⟨(Float32AffineSiLUReplay.check_eq_true_iff
      GeneratedThreeHiddenStageSite2AffineSiLUReplayBatchFixture.replay0).mp
      GeneratedThreeHiddenStageSite2AffineSiLUReplayBatchFixture.replay0_is_accepted, ?_⟩
  intro row
  fin_cases row
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation0Row0AddMask).mp
        invocation0Row0AddMask_is_accepted, rfl, rfl⟩

def invocation1Row0Activation : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation1Row0Error : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation1Row0Sum : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation1Row0Center : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def invocation1Row0Add : Float32AddReplay where
  left := invocation1Row0Activation
  right := invocation1Row0Error
  output := invocation1Row0Sum
  localError := (0 : ℚ)

def invocation1Row0Mask : Float32MaskReplay where
  active := false
  input := invocation1Row0Sum
  output := invocation1Row0Center
  localError := (0 : ℚ)

def invocation1Row0AddMask : Float32AddMaskReplay where
  add := invocation1Row0Add
  mask := invocation1Row0Mask

theorem invocation1Row0AddMask_is_accepted : invocation1Row0AddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, invocation1Row0AddMask, invocation1Row0Add, invocation1Row0Mask,
    boolRat, invocation1Row0Activation, invocation1Row0Error, invocation1Row0Sum, invocation1Row0Center,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def hiddenReplay1 : Float32HiddenStageReplay 1 1 where
  affineSiLU := GeneratedThreeHiddenStageSite2AffineSiLUReplayBatchFixture.replay1
  errorSite := ![invocation1Row0Error]
  addMask := ![invocation1Row0AddMask]

theorem hiddenReplay1_is_accepted : hiddenReplay1.check = true := by
  apply (Float32HiddenStageReplay.check_eq_true_iff hiddenReplay1).mpr
  refine ⟨(Float32AffineSiLUReplay.check_eq_true_iff
      GeneratedThreeHiddenStageSite2AffineSiLUReplayBatchFixture.replay1).mp
      GeneratedThreeHiddenStageSite2AffineSiLUReplayBatchFixture.replay1_is_accepted, ?_⟩
  intro row
  fin_cases row
  · exact ⟨(Float32AddMaskReplay.check_eq_true_iff invocation1Row0AddMask).mp
        invocation1Row0AddMask_is_accepted, rfl, rfl⟩

def certificateBatch : Float32HiddenStageReplayBatch 1 1 where
  expectedCount := 2
  entries := [hiddenReplay0, hiddenReplay1]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [Float32HiddenStageReplayBatch.check, certificateBatch,
    hiddenReplay0_is_accepted, hiddenReplay1_is_accepted]

theorem certificateBatch_total_error_is_bounded :
    certificateBatch.totalObservedError ≤
      certificateBatch.totalCertifiedError :=
  certificateBatch.totalObservedError_le certificateBatch_is_accepted

#print axioms certificateBatch_is_accepted
#print axioms certificateBatch_total_error_is_bounded

end
end GeneratedThreeHiddenStageSite2HiddenStageReplayBatchFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
