import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReadoutReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageSite0HiddenStageReplayBatchGeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageSite1HiddenStageReplayBatchGeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageSite2HiddenStageReplayBatchGeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReadoutAffineReplayBatchGeneratedFixture
import Mathlib.Tactic

/-! This file is generated from source-bound replay batches.  Lean checks
the embedded word arithmetic through the imported batches and every raw-word
connection.  Recorded digests bind those batches to external source bytes. -/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedThreeHiddenStageReadoutReplayBatchFixture

open Float32ThreeHiddenStageReplayCertificate
open Float32ThreeHiddenStageReadoutReplayCertificate

noncomputable section

-- source probe SHA-256: 68a5a3a1aa70540ec9b2f9f2cbe892b52c7c8e579eb2b8a0adb1aba9db262167
-- hidden stage 0 batch SHA-256: e519a23aa265be142666e69e077358319ba7ef24aae0cc55f66746345f852ef3
-- hidden stage 1 batch SHA-256: 83e0b7873958daa5a2c557dd51a02e6209377f5792df8dfed272006883a88ba0
-- hidden stage 2 batch SHA-256: 52ff5fab62dfe830c490cdfba1e8ef3ffb88b0eec7f726cb27b3f4fdb400a0e4
-- readout affine batch SHA-256: b97f0529797ea58fc7b5f6235566527e1552d812b44636f2d21474b4e7d88fc6

def hiddenReplay0 : Float32ThreeHiddenStageReplay 1 1 where
  first := GeneratedThreeHiddenStageSite0HiddenStageReplayBatchFixture.hiddenReplay0
  second := GeneratedThreeHiddenStageSite1HiddenStageReplayBatchFixture.hiddenReplay0
  third := GeneratedThreeHiddenStageSite2HiddenStageReplayBatchFixture.hiddenReplay0

theorem hiddenReplay0_is_accepted : hiddenReplay0.check = true := by
  apply (Float32ThreeHiddenStageReplay.check_eq_true_iff hiddenReplay0).mpr
  refine ⟨
    (Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.check_eq_true_iff
      GeneratedThreeHiddenStageSite0HiddenStageReplayBatchFixture.hiddenReplay0).mp
        GeneratedThreeHiddenStageSite0HiddenStageReplayBatchFixture.hiddenReplay0_is_accepted,
    (Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.check_eq_true_iff
      GeneratedThreeHiddenStageSite1HiddenStageReplayBatchFixture.hiddenReplay0).mp
        GeneratedThreeHiddenStageSite1HiddenStageReplayBatchFixture.hiddenReplay0_is_accepted,
    (Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.check_eq_true_iff
      GeneratedThreeHiddenStageSite2HiddenStageReplayBatchFixture.hiddenReplay0).mp
        GeneratedThreeHiddenStageSite2HiddenStageReplayBatchFixture.hiddenReplay0_is_accepted,
    by intro row; fin_cases row; rfl,
    by intro row; fin_cases row; rfl⟩

def replay0 : Float32ThreeHiddenStageReadoutReplay
    1 1 1 where
  hidden := hiddenReplay0
  readout := GeneratedThreeHiddenStageReadoutAffineReplayBatchFixture.replay0

theorem replay0_is_accepted : replay0.check = true := by
  apply (Float32ThreeHiddenStageReadoutReplay.check_eq_true_iff replay0).mpr
  refine ⟨
    (Float32ThreeHiddenStageReplay.check_eq_true_iff hiddenReplay0).mp
      hiddenReplay0_is_accepted,
    (Float32AffineReplayCertificate.Float32AffineReplay.check_eq_true_iff
      GeneratedThreeHiddenStageReadoutAffineReplayBatchFixture.replay0).mp
        GeneratedThreeHiddenStageReadoutAffineReplayBatchFixture.replay0_is_accepted,
    by intro column; fin_cases column; rfl⟩

def hiddenReplay1 : Float32ThreeHiddenStageReplay 1 1 where
  first := GeneratedThreeHiddenStageSite0HiddenStageReplayBatchFixture.hiddenReplay1
  second := GeneratedThreeHiddenStageSite1HiddenStageReplayBatchFixture.hiddenReplay1
  third := GeneratedThreeHiddenStageSite2HiddenStageReplayBatchFixture.hiddenReplay1

theorem hiddenReplay1_is_accepted : hiddenReplay1.check = true := by
  apply (Float32ThreeHiddenStageReplay.check_eq_true_iff hiddenReplay1).mpr
  refine ⟨
    (Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.check_eq_true_iff
      GeneratedThreeHiddenStageSite0HiddenStageReplayBatchFixture.hiddenReplay1).mp
        GeneratedThreeHiddenStageSite0HiddenStageReplayBatchFixture.hiddenReplay1_is_accepted,
    (Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.check_eq_true_iff
      GeneratedThreeHiddenStageSite1HiddenStageReplayBatchFixture.hiddenReplay1).mp
        GeneratedThreeHiddenStageSite1HiddenStageReplayBatchFixture.hiddenReplay1_is_accepted,
    (Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.check_eq_true_iff
      GeneratedThreeHiddenStageSite2HiddenStageReplayBatchFixture.hiddenReplay1).mp
        GeneratedThreeHiddenStageSite2HiddenStageReplayBatchFixture.hiddenReplay1_is_accepted,
    by intro row; fin_cases row; rfl,
    by intro row; fin_cases row; rfl⟩

def replay1 : Float32ThreeHiddenStageReadoutReplay
    1 1 1 where
  hidden := hiddenReplay1
  readout := GeneratedThreeHiddenStageReadoutAffineReplayBatchFixture.replay1

theorem replay1_is_accepted : replay1.check = true := by
  apply (Float32ThreeHiddenStageReadoutReplay.check_eq_true_iff replay1).mpr
  refine ⟨
    (Float32ThreeHiddenStageReplay.check_eq_true_iff hiddenReplay1).mp
      hiddenReplay1_is_accepted,
    (Float32AffineReplayCertificate.Float32AffineReplay.check_eq_true_iff
      GeneratedThreeHiddenStageReadoutAffineReplayBatchFixture.replay1).mp
        GeneratedThreeHiddenStageReadoutAffineReplayBatchFixture.replay1_is_accepted,
    by intro column; fin_cases column; rfl⟩

def certificateBatch : Float32ThreeHiddenStageReadoutReplayBatch
    1 1 1 where
  expectedCount := 2
  entries := [replay0, replay1]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [Float32ThreeHiddenStageReadoutReplayBatch.check, certificateBatch,
    replay0_is_accepted, replay1_is_accepted]

#print axioms certificateBatch_is_accepted

end
end GeneratedThreeHiddenStageReadoutReplayBatchFixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
