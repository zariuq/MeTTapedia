import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReplayCertificate
import Mathlib.Tactic

/-!
# Exact binary32 replay from three hidden stages through the final readout

This module closes the local finite-precision path of the audited deep
error-coordinate adapter.  It connects the third masked center to the final
affine residual readout by exact binary32 word equality and adds the readout's
local replay error to the three-stage mismatch recurrence.

The readout point-pair rate remains an explicit premise.  Source provenance,
endpoint identity, backend evaluation order, and task-gradient transport are
separate obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32ThreeHiddenStageReadoutReplayCertificate

open Float32CheckpointMatrix
open Float32AffineReplayCertificate
open Float32HiddenStageReplayCertificate
open Float32ThreeHiddenStageReplayCertificate
open FinitePrecisionEvaluationError

noncomputable section

/-- Three word-connected hidden stages followed by one observed affine
residual readout. -/
structure Float32ThreeHiddenStageReadoutReplay
    (outputDim hiddenDim inputDim : ℕ) where
  hidden : Float32ThreeHiddenStageReplay hiddenDim inputDim
  readout : Float32AffineReplay outputDim hiddenDim

def Float32ThreeHiddenStageReadoutReplay.Valid
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReadoutReplay
      outputDim hiddenDim inputDim) : Prop :=
  replay.hidden.Valid ∧ replay.readout.Valid ∧
    ∀ column,
      (replay.readout.input column).word =
        (replay.hidden.third.addMask column).mask.output.word

def Float32ThreeHiddenStageReadoutReplay.check
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReadoutReplay
      outputDim hiddenDim inputDim) : Bool :=
  replay.hidden.check && replay.readout.check &&
    decide (∀ column,
      (replay.readout.input column).word =
        (replay.hidden.third.addMask column).mask.output.word)

theorem Float32ThreeHiddenStageReadoutReplay.check_eq_true_iff
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReadoutReplay
      outputDim hiddenDim inputDim) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32ThreeHiddenStageReadoutReplay.check,
    Float32ThreeHiddenStageReadoutReplay.Valid,
    Float32ThreeHiddenStageReplay.check_eq_true_iff,
    Float32AffineReplay.check_eq_true_iff, and_assoc]

private theorem finiteWord_toReal_eq_of_word_eq
    {left right : FiniteFloat32Word} (hword : left.word = right.word) :
    left.toReal = right.toReal := by
  simp [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat, hword]

/-- The third observed masked center is exactly the vector decoded as the
final affine readout's input. -/
theorem Float32ThreeHiddenStageReadoutReplay.readout_runtimeInput_eq_hiddenOutput
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReadoutReplay
      outputDim hiddenDim inputDim)
    (hcheck : replay.check = true) :
    replay.readout.decodedInput = replay.hidden.third.decodedOutput := by
  have hwire := (replay.check_eq_true_iff.mp hcheck).2.2
  ext column
  simpa [Float32AffineReplay.decodedInput,
    Float32HiddenStageReplay.decodedOutput,
    Float32AddMaskReplayCertificate.Float32AddMaskReplay.decodedOutput] using
    finiteWord_toReal_eq_of_word_eq (hwire column)

/-- Complete conservative mismatch budget through the residual readout. -/
def Float32ThreeHiddenStageReadoutReplay.totalCertifiedError
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReadoutReplay
      outputDim hiddenDim inputDim)
    (rateFirst rateSecond rateThird rateReadout inputError : ℝ) : ℝ :=
  propagatedEvaluationError rateReadout (replay.readout.localError : ℝ)
    (replay.hidden.totalCertifiedError
      rateFirst rateSecond rateThird inputError)

/-- The complete observed adapter residual is bounded by the three hidden
local budgets, their explicit point-pair transport, and the final affine
readout's local replay budget and point-pair rate. -/
theorem Float32ThreeHiddenStageReadoutReplay.sound
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageReadoutReplay
      outputDim hiddenDim inputDim)
    (hcheck : replay.check = true)
    (exactInput : EuclideanSpace ℝ (Fin inputDim))
    (rateFirst rateSecond rateThird rateReadout inputError : ℝ)
    (hrateFirst : 0 ≤ rateFirst) (hrateSecond : 0 ≤ rateSecond)
    (hrateThird : 0 ≤ rateThird) (hrateReadout : 0 ≤ rateReadout)
    (hpairFirst :
      ‖replay.hidden.first.idealBlockAtRecordedError
          replay.hidden.first.runtimePreviousCenter -
        replay.hidden.first.idealBlockAtRecordedError exactInput‖ ≤
          rateFirst *
            ‖replay.hidden.first.runtimePreviousCenter - exactInput‖)
    (hpairSecond :
      ‖replay.hidden.second.idealBlockAtRecordedError
          replay.hidden.first.decodedOutput -
        replay.hidden.second.idealBlockAtRecordedError
          (replay.hidden.first.idealBlockAtRecordedError exactInput)‖ ≤
        rateSecond *
          ‖replay.hidden.first.decodedOutput -
            replay.hidden.first.idealBlockAtRecordedError exactInput‖)
    (hpairThird :
      ‖replay.hidden.third.idealBlockAtRecordedError
          replay.hidden.second.decodedOutput -
        replay.hidden.third.idealBlockAtRecordedError
          (replay.hidden.second.idealBlockAtRecordedError
            (replay.hidden.first.idealBlockAtRecordedError exactInput))‖ ≤
        rateThird *
          ‖replay.hidden.second.decodedOutput -
            replay.hidden.second.idealBlockAtRecordedError
              (replay.hidden.first.idealBlockAtRecordedError exactInput)‖)
    (hpairReadout :
      ‖replay.readout.idealAffine replay.hidden.third.decodedOutput -
        replay.readout.idealAffine
          (replay.hidden.third.idealBlockAtRecordedError
            (replay.hidden.second.idealBlockAtRecordedError
              (replay.hidden.first.idealBlockAtRecordedError exactInput)))‖ ≤
        rateReadout *
          ‖replay.hidden.third.decodedOutput -
            replay.hidden.third.idealBlockAtRecordedError
              (replay.hidden.second.idealBlockAtRecordedError
                (replay.hidden.first.idealBlockAtRecordedError exactInput))‖)
    (hinput :
      ‖replay.hidden.first.runtimePreviousCenter - exactInput‖ ≤ inputError) :
    ‖replay.readout.decodedOutput -
      replay.readout.idealAffine
        (replay.hidden.third.idealBlockAtRecordedError
          (replay.hidden.second.idealBlockAtRecordedError
            (replay.hidden.first.idealBlockAtRecordedError exactInput)))‖ ≤
      replay.totalCertifiedError rateFirst rateSecond rateThird
        rateReadout inputError := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have hhiddenCheck : replay.hidden.check = true :=
    replay.hidden.check_eq_true_iff.mpr hvalid.1
  have hreadoutCheck : replay.readout.check = true :=
    replay.readout.check_eq_true_iff.mpr hvalid.2.1
  have hhidden := replay.hidden.sound hhiddenCheck exactInput
    rateFirst rateSecond rateThird inputError
    hrateFirst hrateSecond hrateThird
    hpairFirst hpairSecond hpairThird hinput
  have hlocalReadout :=
    replay.readout.toLocalEvaluationErrorCertificate hreadoutCheck
  rw [replay.readout_runtimeInput_eq_hiddenOutput hcheck] at hlocalReadout
  exact outputMismatch_le_propagatedEvaluationError
    replay.readout.idealAffine
    (replay.hidden.third.idealBlockAtRecordedError
      (replay.hidden.second.idealBlockAtRecordedError
        (replay.hidden.first.idealBlockAtRecordedError exactInput)))
    replay.hidden.third.decodedOutput replay.readout.decodedOutput
    rateReadout (replay.readout.localError : ℝ)
    (replay.hidden.totalCertifiedError
      rateFirst rateSecond rateThird inputError)
    hrateReadout hlocalReadout hpairReadout hhidden

/-! ## Finite invocation batches -/

structure Float32ThreeHiddenStageReadoutReplayBatch
    (outputDim hiddenDim inputDim : ℕ) where
  expectedCount : ℕ
  entries : List (Float32ThreeHiddenStageReadoutReplay
    outputDim hiddenDim inputDim)

def Float32ThreeHiddenStageReadoutReplayBatch.Valid
    {outputDim hiddenDim inputDim : ℕ}
    (batch : Float32ThreeHiddenStageReadoutReplayBatch
      outputDim hiddenDim inputDim) : Prop :=
  0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount ∧
    ∀ replay ∈ batch.entries, replay.Valid

def Float32ThreeHiddenStageReadoutReplayBatch.check
    {outputDim hiddenDim inputDim : ℕ}
    (batch : Float32ThreeHiddenStageReadoutReplayBatch
      outputDim hiddenDim inputDim) : Bool :=
  decide (0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount) &&
    batch.entries.all Float32ThreeHiddenStageReadoutReplay.check

theorem Float32ThreeHiddenStageReadoutReplayBatch.check_eq_true_iff
    {outputDim hiddenDim inputDim : ℕ}
    (batch : Float32ThreeHiddenStageReadoutReplayBatch
      outputDim hiddenDim inputDim) :
    batch.check = true ↔ batch.Valid := by
  simp [Float32ThreeHiddenStageReadoutReplayBatch.check,
    Float32ThreeHiddenStageReadoutReplayBatch.Valid, List.all_eq_true,
    Float32ThreeHiddenStageReadoutReplay.check_eq_true_iff, and_assoc]

/-! ## Positive and negative executable fixtures -/

def zeroReadout : Float32AffineReplay 1 1 where
  input := ![Float32HiddenStageReplayCertificate.zeroWord]
  weight := ![Float32CheckpointMatrix.positiveOne]
  bias := ![Float32HiddenStageReplayCertificate.zeroWord]
  output := ![Float32HiddenStageReplayCertificate.zeroWord]
  localError := 0

theorem zeroReadout_is_accepted : zeroReadout.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, zeroReadout,
    Float32CheckpointMatrix.positiveOne,
    Float32HiddenStageReplayCertificate.zeroWord,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa, rowMajorIndex]

def fullFixture : Float32ThreeHiddenStageReadoutReplay 1 1 1 where
  hidden := Float32ThreeHiddenStageReplayCertificate.threeStageFixture
  readout := zeroReadout

theorem fullFixture_is_accepted : fullFixture.check = true := by
  apply (Float32ThreeHiddenStageReadoutReplay.check_eq_true_iff
    fullFixture).mpr
  exact ⟨(Float32ThreeHiddenStageReplay.check_eq_true_iff
      Float32ThreeHiddenStageReplayCertificate.threeStageFixture).mp
        Float32ThreeHiddenStageReplayCertificate.threeStageFixture_is_accepted,
    (Float32AffineReplay.check_eq_true_iff zeroReadout).mp
      zeroReadout_is_accepted,
    by intro column; fin_cases column; rfl⟩

def fullFixtureBatch : Float32ThreeHiddenStageReadoutReplayBatch 1 1 1 where
  expectedCount := 1
  entries := [fullFixture]

theorem fullFixtureBatch_is_accepted : fullFixtureBatch.check = true := by
  simp [Float32ThreeHiddenStageReadoutReplayBatch.check, fullFixtureBatch,
    fullFixture_is_accepted]

def emptyFullFixtureBatch :
    Float32ThreeHiddenStageReadoutReplayBatch 1 1 1 where
  expectedCount := 0
  entries := []

theorem emptyFullFixtureBatch_is_rejected :
    emptyFullFixtureBatch.check = false := by
  norm_num [Float32ThreeHiddenStageReadoutReplayBatch.check,
    emptyFullFixtureBatch]

/-- An independently valid affine invocation that consumes and returns one,
rather than consuming the third stage's observed zero center. -/
def oneReadout : Float32AffineReplay 1 1 where
  input := ![Float32CheckpointMatrix.positiveOne]
  weight := ![Float32CheckpointMatrix.positiveOne]
  bias := ![Float32HiddenStageReplayCertificate.zeroWord]
  output := ![Float32CheckpointMatrix.positiveOne]
  localError := 0

theorem oneReadout_is_accepted : oneReadout.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, oneReadout,
    Float32CheckpointMatrix.positiveOne,
    Float32HiddenStageReplayCertificate.zeroWord,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa, rowMajorIndex]

def miswiredFullFixture : Float32ThreeHiddenStageReadoutReplay 1 1 1 :=
  { fullFixture with readout := oneReadout }

theorem miswiredFullFixture_is_rejected : miswiredFullFixture.check = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  have hwire :=
    (Float32ThreeHiddenStageReadoutReplay.check_eq_true_iff
      miswiredFullFixture).mp hcheck
  have hcolumn := hwire.2.2 (0 : Fin 1)
  norm_num [miswiredFullFixture, fullFixture, oneReadout,
    Float32ThreeHiddenStageReplayCertificate.threeStageFixture,
    Float32ThreeHiddenStageReplayCertificate.zeroHiddenStageAfterZero,
    Float32ThreeHiddenStageReplayCertificate.zeroAddMask,
    Float32HiddenStageReplayCertificate.zeroWord,
    Float32CheckpointMatrix.positiveOne] at hcolumn

#print axioms Float32ThreeHiddenStageReadoutReplay.check_eq_true_iff
#print axioms Float32ThreeHiddenStageReadoutReplay.readout_runtimeInput_eq_hiddenOutput
#print axioms Float32ThreeHiddenStageReadoutReplay.sound
#print axioms Float32ThreeHiddenStageReadoutReplayBatch.check_eq_true_iff
#print axioms fullFixture_is_accepted
#print axioms fullFixtureBatch_is_accepted
#print axioms emptyFullFixtureBatch_is_rejected
#print axioms miswiredFullFixture_is_rejected

end

end Float32ThreeHiddenStageReadoutReplayCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
