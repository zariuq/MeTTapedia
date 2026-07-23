import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineMaskReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ThreeHiddenStageReplayCertificate
import Mathlib.Tactic

/-!
# Exact binary32 replay of the three-stage residual adapter

The audited deep error-coordinate adapter applies three hidden stages, an
affine residual readout, and a Boolean node mask.  This module connects those
observed operations by exact binary32 word equality and composes their local
evaluation-error certificates.

The four point-pair rates remain explicit premises.  The kernel checks the
embedded arithmetic and interior word connections.  Source provenance,
endpoint identity, backend evaluation order, and invocation coverage remain
external obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32ThreeHiddenStageResidualReplayCertificate

open Float32CheckpointMatrix
open Float32AffineMaskReplayCertificate
open Float32ThreeHiddenStageReplayCertificate
open FinitePrecisionEvaluationError

noncomputable section

/-- Three word-connected hidden stages followed by an observed affine
readout and Boolean node mask. -/
structure Float32ThreeHiddenStageResidualReplay
    (outputDim hiddenDim inputDim : ℕ) where
  hidden : Float32ThreeHiddenStageReplay hiddenDim inputDim
  readout : Float32AffineMaskReplay outputDim hiddenDim

def Float32ThreeHiddenStageResidualReplay.Valid
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageResidualReplay
      outputDim hiddenDim inputDim) : Prop :=
  replay.hidden.Valid ∧ replay.readout.Valid ∧
    ∀ column,
      (replay.readout.affine.input column).word =
        (replay.hidden.third.addMask column).mask.output.word

def Float32ThreeHiddenStageResidualReplay.check
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageResidualReplay
      outputDim hiddenDim inputDim) : Bool :=
  replay.hidden.check && replay.readout.check &&
    decide (∀ column,
      (replay.readout.affine.input column).word =
        (replay.hidden.third.addMask column).mask.output.word)

theorem Float32ThreeHiddenStageResidualReplay.check_eq_true_iff
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageResidualReplay
      outputDim hiddenDim inputDim) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32ThreeHiddenStageResidualReplay.check,
    Float32ThreeHiddenStageResidualReplay.Valid,
    Float32ThreeHiddenStageReplay.check_eq_true_iff,
    Float32AffineMaskReplay.check_eq_true_iff, and_assoc]

private theorem finiteWord_toReal_eq_of_word_eq
    {left right : FiniteFloat32Word} (hword : left.word = right.word) :
    left.toReal = right.toReal := by
  simp [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat, hword]

/-- The third observed hidden center is exactly the vector decoded as the
final affine readout's input. -/
theorem
    Float32ThreeHiddenStageResidualReplay.readout_runtimeInput_eq_hiddenOutput
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageResidualReplay
      outputDim hiddenDim inputDim)
    (hcheck : replay.check = true) :
    replay.readout.decodedInput = replay.hidden.third.decodedOutput := by
  have hwire := (replay.check_eq_true_iff.mp hcheck).2.2
  ext column
  simpa [Float32AffineMaskReplay.decodedInput,
    Float32AffineReplayCertificate.Float32AffineReplay.decodedInput,
    Float32HiddenStageReplayCertificate.Float32HiddenStageReplay.decodedOutput,
    Float32AddMaskReplayCertificate.Float32AddMaskReplay.decodedOutput] using
    finiteWord_toReal_eq_of_word_eq (hwire column)

/-- Complete conservative mismatch budget through the masked residual
readout. -/
def Float32ThreeHiddenStageResidualReplay.totalCertifiedError
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageResidualReplay
      outputDim hiddenDim inputDim)
    (rateFirst rateSecond rateThird rateReadout inputError : ℝ) : ℝ :=
  propagatedEvaluationError rateReadout
    (replay.readout.totalCertifiedErrorRat : ℝ)
    (replay.hidden.totalCertifiedError
      rateFirst rateSecond rateThird inputError)

/-- The observed masked residual is bounded by the local binary32 replay
budgets and four explicit point-pair transport obligations. -/
theorem Float32ThreeHiddenStageResidualReplay.sound
    {outputDim hiddenDim inputDim : ℕ}
    (replay : Float32ThreeHiddenStageResidualReplay
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
      ‖replay.readout.idealMap replay.hidden.third.decodedOutput -
        replay.readout.idealMap
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
      replay.readout.idealMap
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
    replay.readout.idealMap
    (replay.hidden.third.idealBlockAtRecordedError
      (replay.hidden.second.idealBlockAtRecordedError
        (replay.hidden.first.idealBlockAtRecordedError exactInput)))
    replay.hidden.third.decodedOutput replay.readout.decodedOutput
    rateReadout (replay.readout.totalCertifiedErrorRat : ℝ)
    (replay.hidden.totalCertifiedError
      rateFirst rateSecond rateThird inputError)
    hrateReadout hlocalReadout hpairReadout hhidden

/-! ## Finite invocation batches -/

structure Float32ThreeHiddenStageResidualReplayBatch
    (outputDim hiddenDim inputDim : ℕ) where
  expectedCount : ℕ
  entries : List (Float32ThreeHiddenStageResidualReplay
    outputDim hiddenDim inputDim)

def Float32ThreeHiddenStageResidualReplayBatch.Valid
    {outputDim hiddenDim inputDim : ℕ}
    (batch : Float32ThreeHiddenStageResidualReplayBatch
      outputDim hiddenDim inputDim) : Prop :=
  0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount ∧
    ∀ replay ∈ batch.entries, replay.Valid

def Float32ThreeHiddenStageResidualReplayBatch.check
    {outputDim hiddenDim inputDim : ℕ}
    (batch : Float32ThreeHiddenStageResidualReplayBatch
      outputDim hiddenDim inputDim) : Bool :=
  decide (0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount) &&
    batch.entries.all Float32ThreeHiddenStageResidualReplay.check

theorem Float32ThreeHiddenStageResidualReplayBatch.check_eq_true_iff
    {outputDim hiddenDim inputDim : ℕ}
    (batch : Float32ThreeHiddenStageResidualReplayBatch
      outputDim hiddenDim inputDim) :
    batch.check = true ↔ batch.Valid := by
  simp [Float32ThreeHiddenStageResidualReplayBatch.check,
    Float32ThreeHiddenStageResidualReplayBatch.Valid, List.all_eq_true,
    Float32ThreeHiddenStageResidualReplay.check_eq_true_iff, and_assoc]

/-! ## Positive and negative executable fixtures -/

/-- An exact identity affine invocation at the zero input. -/
def zeroReadout :
    Float32AffineReplayCertificate.Float32AffineReplay 1 1 where
  input := ![Float32HiddenStageReplayCertificate.zeroWord]
  weight := ![Float32CheckpointMatrix.positiveOne]
  bias := ![Float32HiddenStageReplayCertificate.zeroWord]
  output := ![Float32HiddenStageReplayCertificate.zeroWord]
  localError := 0

theorem zeroReadout_is_accepted : zeroReadout.check = true := by
  norm_num [Float32AffineReplayCertificate.Float32AffineReplay.check,
    Float32AffineReplayCertificate.Float32AffineReplay.Valid,
    Float32AffineReplayCertificate.Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplayCertificate.Float32AffineReplay.idealOutputRat,
    zeroReadout, Float32CheckpointMatrix.positiveOne,
    Float32HiddenStageReplayCertificate.zeroWord,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa, rowMajorIndex]

def zeroMaskedReadout : Float32AffineMaskReplay 1 1 where
  affine := zeroReadout
  mask := ![Float32AffineMaskReplayCertificate.activeZeroMask]

theorem zeroMaskedReadout_is_accepted :
    zeroMaskedReadout.check = true := by
  apply (Float32AffineMaskReplay.check_eq_true_iff zeroMaskedReadout).mpr
  exact ⟨
    (Float32AffineReplayCertificate.Float32AffineReplay.check_eq_true_iff
      zeroReadout).mp zeroReadout_is_accepted,
    by intro row; fin_cases row
       exact ⟨
         (Float32AddMaskReplayCertificate.Float32MaskReplay.check_eq_true_iff
           Float32AffineMaskReplayCertificate.activeZeroMask).mp
             (by norm_num [Float32AddMaskReplayCertificate.Float32MaskReplay.check,
               Float32AffineMaskReplayCertificate.activeZeroMask,
               Float32AffineMaskReplayCertificate.zeroWord,
               Float32AddMaskReplayCertificate.boolRat,
               FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]),
         rfl⟩⟩

def fullFixture : Float32ThreeHiddenStageResidualReplay 1 1 1 where
  hidden := Float32ThreeHiddenStageReplayCertificate.threeStageFixture
  readout := zeroMaskedReadout

theorem fullFixture_is_accepted : fullFixture.check = true := by
  apply (Float32ThreeHiddenStageResidualReplay.check_eq_true_iff
    fullFixture).mpr
  exact ⟨
    (Float32ThreeHiddenStageReplay.check_eq_true_iff
      Float32ThreeHiddenStageReplayCertificate.threeStageFixture).mp
        Float32ThreeHiddenStageReplayCertificate.threeStageFixture_is_accepted,
    (Float32AffineMaskReplay.check_eq_true_iff zeroMaskedReadout).mp
      zeroMaskedReadout_is_accepted,
    by intro column; fin_cases column; rfl⟩

def fullFixtureBatch : Float32ThreeHiddenStageResidualReplayBatch 1 1 1 where
  expectedCount := 1
  entries := [fullFixture]

theorem fullFixtureBatch_is_accepted : fullFixtureBatch.check = true := by
  simp [Float32ThreeHiddenStageResidualReplayBatch.check, fullFixtureBatch,
    fullFixture_is_accepted]

def emptyFullFixtureBatch :
    Float32ThreeHiddenStageResidualReplayBatch 1 1 1 where
  expectedCount := 0
  entries := []

theorem emptyFullFixtureBatch_is_rejected :
    emptyFullFixtureBatch.check = false := by
  norm_num [Float32ThreeHiddenStageResidualReplayBatch.check,
    emptyFullFixtureBatch]

/-- An independently valid masked affine invocation that consumes one rather
than the third stage's observed zero center. -/
def miswiredFullFixture : Float32ThreeHiddenStageResidualReplay 1 1 1 :=
  { fullFixture with
    readout := Float32AffineMaskReplayCertificate.activeFixture }

theorem miswiredFullFixture_is_rejected :
    miswiredFullFixture.check = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  have hwire :=
    (Float32ThreeHiddenStageResidualReplay.check_eq_true_iff
      miswiredFullFixture).mp hcheck
  have hcolumn := hwire.2.2 (0 : Fin 1)
  norm_num [miswiredFullFixture, fullFixture,
    Float32AffineMaskReplayCertificate.activeFixture,
    Float32AffineMaskReplayCertificate.identityAffine,
    Float32AffineMaskReplayCertificate.oneWord,
    Float32ThreeHiddenStageReplayCertificate.threeStageFixture,
    Float32ThreeHiddenStageReplayCertificate.zeroHiddenStageAfterZero,
    Float32ThreeHiddenStageReplayCertificate.zeroAddMask,
    Float32HiddenStageReplayCertificate.zeroWord] at hcolumn

#print axioms Float32ThreeHiddenStageResidualReplay.check_eq_true_iff
#print axioms Float32ThreeHiddenStageResidualReplay.readout_runtimeInput_eq_hiddenOutput
#print axioms Float32ThreeHiddenStageResidualReplay.sound
#print axioms Float32ThreeHiddenStageResidualReplayBatch.check_eq_true_iff
#print axioms fullFixture_is_accepted
#print axioms fullFixtureBatch_is_accepted
#print axioms emptyFullFixtureBatch_is_rejected
#print axioms miswiredFullFixture_is_rejected

end

end Float32ThreeHiddenStageResidualReplayCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
