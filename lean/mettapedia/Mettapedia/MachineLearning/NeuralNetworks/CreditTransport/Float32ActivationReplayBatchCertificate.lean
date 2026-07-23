import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayCertificate
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Finite batches of binary32 activation replay certificates

An untrusted producer may emit many activation records from one traced tensor.
This module checks the declared nonzero batch size, checks every member with the
single-pair kernel checker, and transports the pointwise bounds to a summed
absolute-error bound.  Trace provenance and the association between a batch and
a checkpoint remain separate obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32ActivationReplayBatchCertificate

open Float32ActivationReplayCertificate
open RationalRangeReducedActivationEnclosureCertificate
open RegisteredUnaryExpressionCertificate

noncomputable section

/-- A nonempty declared batch of concrete activation replay records. -/
structure Float32ActivationReplayBatch where
  expectedCount : Nat
  entries : List Float32ActivationReplay
  deriving Repr

/-- Propositional meaning mirrored by the executable batch checker. -/
def Float32ActivationReplayBatch.Valid
    (batch : Float32ActivationReplayBatch) : Prop :=
  0 < batch.expectedCount ∧
  batch.entries.length = batch.expectedCount ∧
  ∀ certificate ∈ batch.entries, certificate.Valid

/-- Check the nonempty count contract and every activation replay. -/
def Float32ActivationReplayBatch.check
    (batch : Float32ActivationReplayBatch) : Bool :=
  decide (0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount) &&
  batch.entries.all Float32ActivationReplay.check

theorem Float32ActivationReplayBatch.check_eq_true_iff
    (batch : Float32ActivationReplayBatch) :
    batch.check = true ↔ batch.Valid := by
  simp [Float32ActivationReplayBatch.check,
    Float32ActivationReplayBatch.Valid, List.all_eq_true,
    Float32ActivationReplay.check_eq_true_iff, and_assoc]

/-- Every member of an accepted batch inherits the single-pair theorem. -/
theorem Float32ActivationReplayBatch.sound_of_mem
    (batch : Float32ActivationReplayBatch) (hcheck : batch.check = true)
    {certificate : Float32ActivationReplay}
    (hmem : certificate ∈ batch.entries) :
    |certificate.output.toReal -
        certificate.enclosure.operation.realMap certificate.input.toReal| ≤
      (certificate.enclosure.localError : ℝ) := by
  have hvalid := (batch.check_eq_true_iff.mp hcheck).2.2 certificate hmem
  exact certificate.sound <| certificate.check_eq_true_iff.mpr hvalid

/-- Sum of the exact-real absolute discrepancies represented by the batch. -/
def Float32ActivationReplayBatch.totalAbsoluteError
    (batch : Float32ActivationReplayBatch) : ℝ :=
  (batch.entries.map fun certificate =>
    |certificate.output.toReal -
      certificate.enclosure.operation.realMap certificate.input.toReal|).sum

/-- Sum of the rational error budgets claimed by the batch. -/
def Float32ActivationReplayBatch.totalCertifiedError
    (batch : Float32ActivationReplayBatch) : ℝ :=
  (batch.entries.map fun certificate =>
    (certificate.enclosure.localError : ℝ)).sum

/-- Pointwise replay soundness composes into one conservative batch error
budget. -/
theorem Float32ActivationReplayBatch.totalAbsoluteError_le
    (batch : Float32ActivationReplayBatch) (hcheck : batch.check = true) :
    batch.totalAbsoluteError ≤ batch.totalCertifiedError := by
  apply List.sum_le_sum
  intro certificate hmem
  exact batch.sound_of_mem hcheck hmem

/-! ## Positive and corrupt batches -/

def twoReplayBatch : Float32ActivationReplayBatch where
  expectedCount := 2
  entries := [sigmoidHalfReplay, sigmoidTwoReplay]

theorem twoReplayBatch_is_accepted : twoReplayBatch.check = true := by
  simp [twoReplayBatch, Float32ActivationReplayBatch.check,
    sigmoidHalfReplay_is_accepted, sigmoidTwoReplay_is_accepted]

theorem twoReplayBatch_total_error_is_bounded :
    twoReplayBatch.totalAbsoluteError ≤ twoReplayBatch.totalCertifiedError :=
  twoReplayBatch.totalAbsoluteError_le twoReplayBatch_is_accepted

/-- Empty batches are rejected rather than certifying a tensor vacuously. -/
def emptyReplayBatch : Float32ActivationReplayBatch where
  expectedCount := 0
  entries := []

theorem emptyReplayBatch_is_rejected : emptyReplayBatch.check = false := by
  rfl

/-- A producer cannot declare two records while supplying only one. -/
def countMismatchBatch : Float32ActivationReplayBatch where
  expectedCount := 2
  entries := [sigmoidHalfReplay]

theorem countMismatchBatch_is_rejected : countMismatchBatch.check = false := by
  rfl

/-- One corrupt replay rejects the whole otherwise well-formed batch. -/
def corruptMemberBatch : Float32ActivationReplayBatch where
  expectedCount := 2
  entries := [sigmoidHalfReplay, mismatchedOutputReplay]

theorem corruptMemberBatch_is_rejected : corruptMemberBatch.check = false := by
  simp [corruptMemberBatch, Float32ActivationReplayBatch.check,
    sigmoidHalfReplay_is_accepted, mismatchedOutputReplay_is_rejected]

#print axioms Float32ActivationReplayBatch.check_eq_true_iff
#print axioms Float32ActivationReplayBatch.sound_of_mem
#print axioms Float32ActivationReplayBatch.totalAbsoluteError_le
#print axioms twoReplayBatch_total_error_is_bounded
#print axioms emptyReplayBatch_is_rejected
#print axioms countMismatchBatch_is_rejected
#print axioms corruptMemberBatch_is_rejected

end

end Float32ActivationReplayBatchCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
