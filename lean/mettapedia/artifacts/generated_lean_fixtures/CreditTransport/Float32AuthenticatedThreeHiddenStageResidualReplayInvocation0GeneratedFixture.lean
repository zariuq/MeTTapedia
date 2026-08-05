import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageResidualReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedHiddenStageReplaySite0Invocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedHiddenStageReplaySite1Invocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedHiddenStageReplaySite2Invocation0GeneratedFixture
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AuthenticatedAffineMaskReplayReadoutInvocation0GeneratedFixture
import Mathlib.Tactic

/-! Generated from source-bound hidden-stage and masked-readout records.
Lean checks the supplied arithmetic and every raw-word connection;
recorded digests bind the batches to external runtime artifacts. -/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace GeneratedAuthenticatedThreeHiddenStageResidualReplayInvocation0Fixture

open Float32ThreeHiddenStageReplayCertificate
open Float32ThreeHiddenStageResidualReplayCertificate

noncomputable section

-- source probe SHA-256: beb12bfe26f0d944d8a2c55afb8bbb3b1937978f40a171bdae2875ae190c117b
-- hidden stage 0 batch SHA-256: 98b0bc99d20b07dadd2edbc6386295c3ab1caa31d4c9bc2addb6f1824b98ab56
-- hidden stage 1 batch SHA-256: 2dba4fb30f92292ef9bd2920a10abb5454146e1fec9f386a4c659f993c03ce3f
-- hidden stage 2 batch SHA-256: bb662de350692d9b755f7b9304650fa9144544ef7cd138fe67fbed8682580fbb
-- affine-mask readout batch SHA-256: 80e6ba561ec4636b7240e707f0bd44ab3a5204c0a172fd4e6dd75ef6b9043471

def hiddenReplay0 : Float32ThreeHiddenStageReplay 64 256 where
  first := GeneratedAuthenticatedHiddenStageReplaySite0Invocation0Fixture.hiddenReplay0
  second := GeneratedAuthenticatedHiddenStageReplaySite1Invocation0Fixture.hiddenReplay0
  third := GeneratedAuthenticatedHiddenStageReplaySite2Invocation0Fixture.hiddenReplay0

theorem hiddenReplay0_first_to_second_wire : ∀ row,
    (hiddenReplay0.second.affineSiLU.affine.input row).word =
      (hiddenReplay0.first.addMask row).mask.output.word := by
  intro row
  fin_cases row <;> decide

theorem hiddenReplay0_second_to_third_wire : ∀ row,
    (hiddenReplay0.third.affineSiLU.affine.input row).word =
      (hiddenReplay0.second.addMask row).mask.output.word := by
  intro row
  fin_cases row <;> decide

theorem hiddenReplay0_is_accepted : hiddenReplay0.check = true := by
  apply (Float32ThreeHiddenStageReplay.check_eq_true_iff hiddenReplay0).mpr
  refine ⟨
    (Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.check_eq_true_iff
      GeneratedAuthenticatedHiddenStageReplaySite0Invocation0Fixture.hiddenReplay0).mp
        GeneratedAuthenticatedHiddenStageReplaySite0Invocation0Fixture.hiddenReplay0_is_accepted,
    (Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.check_eq_true_iff
      GeneratedAuthenticatedHiddenStageReplaySite1Invocation0Fixture.hiddenReplay0).mp
        GeneratedAuthenticatedHiddenStageReplaySite1Invocation0Fixture.hiddenReplay0_is_accepted,
    (Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.check_eq_true_iff
      GeneratedAuthenticatedHiddenStageReplaySite2Invocation0Fixture.hiddenReplay0).mp
        GeneratedAuthenticatedHiddenStageReplaySite2Invocation0Fixture.hiddenReplay0_is_accepted,
    hiddenReplay0_first_to_second_wire,
    hiddenReplay0_second_to_third_wire⟩

def replay0 : Float32ThreeHiddenStageResidualReplay
    256 64 256 where
  hidden := hiddenReplay0
  readout := GeneratedAuthenticatedAffineMaskReplayReadoutInvocation0Fixture.replay0

theorem replay0_hidden_to_readout_wire : ∀ column,
    (replay0.readout.affine.input column).word =
      (replay0.hidden.third.addMask column).mask.output.word := by
  intro column
  fin_cases column <;> decide

theorem replay0_is_accepted : replay0.check = true := by
  apply (Float32ThreeHiddenStageResidualReplay.check_eq_true_iff replay0).mpr
  refine ⟨
    (Float32ThreeHiddenStageReplay.check_eq_true_iff hiddenReplay0).mp
      hiddenReplay0_is_accepted,
    (Float32AffineMaskReplayCertificate.Float32AffineMaskReplay.check_eq_true_iff
      GeneratedAuthenticatedAffineMaskReplayReadoutInvocation0Fixture.replay0).mp
        GeneratedAuthenticatedAffineMaskReplayReadoutInvocation0Fixture.replay0_is_accepted,
    replay0_hidden_to_readout_wire⟩

def certificateBatch : Float32ThreeHiddenStageResidualReplayBatch
    256 64 256 where
  expectedCount := 1
  entries := [replay0]

theorem certificateBatch_is_accepted : certificateBatch.check = true := by
  simp [Float32ThreeHiddenStageResidualReplayBatch.check, certificateBatch,
    replay0_is_accepted]

#print axioms certificateBatch_is_accepted

end
end GeneratedAuthenticatedThreeHiddenStageResidualReplayInvocation0Fixture
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
