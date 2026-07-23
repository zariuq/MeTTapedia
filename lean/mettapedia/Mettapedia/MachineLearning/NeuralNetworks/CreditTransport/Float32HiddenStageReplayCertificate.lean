import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineSiLUReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AddMaskReplayCertificate
import Mathlib.Tactic

/-!
# Exact binary32 hidden-stage replay certificates

The audited hidden adapter evaluates one stage as

`(SiLU(affine(previousCenter)) + errorSite) * nodeMask`.

This module composes the independently checked affine--SiLU and addition--mask
replays.  Exact word equalities bind the observed activation to the addition's
left input and the recorded error-site word to its right input.  The
addition--mask certificate separately binds the addition output to the mask
input.

The kernel certifies arithmetic among the supplied words.  Trace provenance,
checkpoint identity, runtime evaluation order, and invocation coverage remain
external obligations and must be bound by source hashes and a verifier.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32HiddenStageReplayCertificate

open scoped BigOperators
open Float32CheckpointMatrix
open Float32AffineSiLUReplayCertificate
open Float32AddMaskReplayCertificate
open FinitePrecisionEvaluationError
open FiniteMatrixOperatorBounds
open SiLUTransitionBounds

noncomputable section

/-- One observed hidden stage, with every output coordinate connected through
exact binary32 words. -/
structure Float32HiddenStageReplay (rows columns : ℕ) where
  affineSiLU : Float32AffineSiLUReplay rows columns
  errorSite : Fin rows → FiniteFloat32Word
  addMask : Fin rows → Float32AddMaskReplay

def Float32HiddenStageReplay.Valid
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns) : Prop :=
  replay.affineSiLU.Valid ∧
    ∀ row,
      (replay.addMask row).Valid ∧
      (replay.addMask row).add.left.word =
        (replay.affineSiLU.activation row).output.word ∧
      (replay.addMask row).add.right.word = (replay.errorSite row).word

def Float32HiddenStageReplay.check
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns) : Bool :=
  replay.affineSiLU.check &&
    decide (∀ row,
      (replay.addMask row).check = true ∧
      (replay.addMask row).add.left.word =
        (replay.affineSiLU.activation row).output.word ∧
      (replay.addMask row).add.right.word = (replay.errorSite row).word)

theorem Float32HiddenStageReplay.check_eq_true_iff
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32HiddenStageReplay.check, Float32HiddenStageReplay.Valid,
    Float32AffineSiLUReplay.check_eq_true_iff,
    Float32AddMaskReplay.check_eq_true_iff]

/-- Exact-real input pair: previous center and observed error-site value. -/
def Float32HiddenStageReplay.decodedInput
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns) :
    EuclideanSpace ℝ (Fin columns) × EuclideanSpace ℝ (Fin rows) :=
  (replay.affineSiLU.affine.decodedInput,
    WithLp.toLp 2 fun row ↦ (replay.errorSite row).toReal)

/-- Observed binary32 center after the Boolean node mask. -/
def Float32HiddenStageReplay.decodedOutput
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns) :
    EuclideanSpace ℝ (Fin rows) :=
  WithLp.toLp 2 fun row ↦ (replay.addMask row).decodedOutput

/-- Runtime previous-center vector consumed by the stage's affine map. -/
def Float32HiddenStageReplay.runtimePreviousCenter
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns) :
    EuclideanSpace ℝ (Fin columns) :=
  replay.affineSiLU.affine.decodedInput

/-- Exact-real hidden-stage map represented by this trace. -/
def Float32HiddenStageReplay.idealBlock
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns)
    (input : EuclideanSpace ℝ (Fin columns) ×
      EuclideanSpace ℝ (Fin rows)) :
    EuclideanSpace ℝ (Fin rows) :=
  WithLp.toLp 2 fun row ↦
    (boolRat (replay.addMask row).mask.active : ℝ) *
      (sourceSiLU (replay.affineSiLU.affine.idealAffine input.1 row) +
        input.2 row)

/-- Exact-real stage map with the recorded error-site vector held fixed.  This
is the form consumed by a multi-stage recurrence over previous centers. -/
def Float32HiddenStageReplay.idealBlockAtRecordedError
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns)
    (previousCenter : EuclideanSpace ℝ (Fin columns)) :
    EuclideanSpace ℝ (Fin rows) :=
  replay.idealBlock (previousCenter, replay.decodedInput.2)

def Float32HiddenStageReplay.totalAddMaskErrorRat
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns) : ℚ :=
  ∑ row, (replay.addMask row).totalCertifiedErrorRat

/-- Conservative full-stage budget.  Inactive coordinates could permit a
tighter masked affine--SiLU budget; retaining the full upstream budget keeps
this certificate compositional without inferring activity from zero values. -/
def Float32HiddenStageReplay.totalCertifiedErrorRat
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns) : ℚ :=
  replay.totalAddMaskErrorRat + replay.affineSiLU.totalCertifiedErrorRat

private theorem finiteWord_toReal_eq_of_word_eq
    {left right : FiniteFloat32Word} (hword : left.word = right.word) :
    left.toReal = right.toReal := by
  simp [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat, hword]

/-- The observed coordinate differs from the exact-real hidden-stage
coordinate by at most its local addition--mask budget plus the upstream
affine--SiLU coordinate mismatch. -/
theorem Float32HiddenStageReplay.coordinate_error_le
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns)
    (hcheck : replay.check = true) (row : Fin rows) :
    |replay.decodedOutput row -
        replay.idealBlock replay.decodedInput row| ≤
      ((replay.addMask row).totalCertifiedErrorRat : ℝ) +
        |replay.affineSiLU.decodedOutput row -
          replay.affineSiLU.idealBlock
            replay.affineSiLU.affine.decodedInput row| := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  rcases hvalid.2 row with ⟨haddMask, hleft, hright⟩
  have haddMaskCheck : (replay.addMask row).check = true :=
    (replay.addMask row).check_eq_true_iff.mpr haddMask
  have haddMaskSound := (replay.addMask row).sound haddMaskCheck
  have hleftReal :
      (replay.addMask row).add.left.toReal =
        replay.affineSiLU.decodedOutput row := by
    simpa [Float32AffineSiLUReplay.decodedOutput] using
      finiteWord_toReal_eq_of_word_eq hleft
  have hrightReal :
      (replay.addMask row).add.right.toReal =
        replay.decodedInput.2 row := by
    simpa [Float32HiddenStageReplay.decodedInput] using
      finiteWord_toReal_eq_of_word_eq hright
  have hlocal :
      |replay.decodedOutput row -
          (boolRat (replay.addMask row).mask.active : ℝ) *
            (replay.affineSiLU.decodedOutput row +
              replay.decodedInput.2 row)| ≤
        ((replay.addMask row).totalCertifiedErrorRat : ℝ) := by
    simpa [Float32HiddenStageReplay.decodedOutput,
      Float32AddMaskReplay.idealMap,
      Float32AddMaskReplay.decodedInput, hleftReal, hrightReal] using
      haddMaskSound
  have htransport :
      |(boolRat (replay.addMask row).mask.active : ℝ) *
          (replay.affineSiLU.decodedOutput row + replay.decodedInput.2 row) -
        (boolRat (replay.addMask row).mask.active : ℝ) *
          (replay.affineSiLU.idealBlock
              replay.affineSiLU.affine.decodedInput row +
            replay.decodedInput.2 row)| ≤
        |replay.affineSiLU.decodedOutput row -
          replay.affineSiLU.idealBlock
            replay.affineSiLU.affine.decodedInput row| := by
    cases (replay.addMask row).mask.active <;> simp [boolRat]
  calc
    |replay.decodedOutput row -
        replay.idealBlock replay.decodedInput row| ≤
      |replay.decodedOutput row -
          (boolRat (replay.addMask row).mask.active : ℝ) *
            (replay.affineSiLU.decodedOutput row +
              replay.decodedInput.2 row)| +
        |(boolRat (replay.addMask row).mask.active : ℝ) *
            (replay.affineSiLU.decodedOutput row +
              replay.decodedInput.2 row) -
          (boolRat (replay.addMask row).mask.active : ℝ) *
            (replay.affineSiLU.idealBlock
                replay.affineSiLU.affine.decodedInput row +
              replay.decodedInput.2 row)| := by
        simpa [Float32HiddenStageReplay.idealBlock,
          Float32HiddenStageReplay.decodedInput,
          Float32AffineSiLUReplay.idealBlock] using
          (abs_sub_le (replay.decodedOutput row)
            ((boolRat (replay.addMask row).mask.active : ℝ) *
              (replay.affineSiLU.decodedOutput row +
                replay.decodedInput.2 row))
            ((boolRat (replay.addMask row).mask.active : ℝ) *
              (replay.affineSiLU.idealBlock
                  replay.affineSiLU.affine.decodedInput row +
                replay.decodedInput.2 row)))
    _ ≤ ((replay.addMask row).totalCertifiedErrorRat : ℝ) +
        |replay.affineSiLU.decodedOutput row -
          replay.affineSiLU.idealBlock
            replay.affineSiLU.affine.decodedInput row| :=
      add_le_add hlocal htransport

/-- The entrywise mismatch of the complete hidden stage is bounded by the
sum of the downstream addition--mask budgets and the upstream affine--SiLU
budget. -/
theorem Float32HiddenStageReplay.totalCoordinateError_le
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns)
    (hcheck : replay.check = true) :
    (∑ row, |replay.decodedOutput row -
      replay.idealBlock replay.decodedInput row|) ≤
      (replay.totalCertifiedErrorRat : ℝ) := by
  have haffineSiLUCheck : replay.affineSiLU.check = true :=
    replay.affineSiLU.check_eq_true_iff.mpr
      (replay.check_eq_true_iff.mp hcheck).1
  calc
    (∑ row, |replay.decodedOutput row -
      replay.idealBlock replay.decodedInput row|) ≤
        ∑ row, (((replay.addMask row).totalCertifiedErrorRat : ℝ) +
          |replay.affineSiLU.decodedOutput row -
            replay.affineSiLU.idealBlock
              replay.affineSiLU.affine.decodedInput row|) :=
      Finset.sum_le_sum fun row _ ↦ replay.coordinate_error_le hcheck row
    _ = (∑ row, ((replay.addMask row).totalCertifiedErrorRat : ℝ)) +
        (∑ row, |replay.affineSiLU.decodedOutput row -
          replay.affineSiLU.idealBlock
            replay.affineSiLU.affine.decodedInput row|) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ row, ((replay.addMask row).totalCertifiedErrorRat : ℝ)) +
        (replay.affineSiLU.totalCertifiedErrorRat : ℝ) :=
      add_le_add (le_refl _)
        (replay.affineSiLU.totalCoordinateError_le haffineSiLUCheck)
    _ = (replay.totalCertifiedErrorRat : ℝ) := by
      simp [Float32HiddenStageReplay.totalCertifiedErrorRat,
        Float32HiddenStageReplay.totalAddMaskErrorRat, Rat.cast_sum]

theorem Float32HiddenStageReplay.sound
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns)
    (hcheck : replay.check = true) :
    ‖replay.decodedOutput - replay.idealBlock replay.decodedInput‖ ≤
      (replay.totalCertifiedErrorRat : ℝ) := by
  exact (euclidean_norm_le_entrywiseL1 _).trans
    (replay.totalCoordinateError_le hcheck)

theorem Float32HiddenStageReplay.toLocalEvaluationErrorCertificate
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns)
    (hcheck : replay.check = true) :
    LocalEvaluationErrorCertificate replay.idealBlock replay.decodedInput
      replay.decodedOutput (replay.totalCertifiedErrorRat : ℝ) := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have hupstreamNonneg :
      0 ≤ (replay.affineSiLU.totalCertifiedErrorRat : ℝ) :=
    (replay.affineSiLU.toLocalEvaluationErrorCertificate
      (replay.affineSiLU.check_eq_true_iff.mpr hvalid.1)).localError_nonneg
  have hdownstreamNonneg :
      0 ≤ (∑ row, ((replay.addMask row).totalCertifiedErrorRat : ℝ)) :=
    Finset.sum_nonneg fun row _ ↦
      ((replay.addMask row).toLocalEvaluationErrorCertificate
        ((replay.addMask row).check_eq_true_iff.mpr (hvalid.2 row).1)).localError_nonneg
  refine
    { localError_nonneg := ?_
      output_error_le := replay.sound hcheck }
  rw [Float32HiddenStageReplay.totalCertifiedErrorRat,
    Float32HiddenStageReplay.totalAddMaskErrorRat, Rat.cast_add,
    Rat.cast_sum]
  exact add_nonneg hdownstreamNonneg hupstreamNonneg

/-- Repackage the local theorem as a map from the previous center alone while
holding the source-recorded error site fixed. -/
theorem Float32HiddenStageReplay.toPreviousCenterLocalCertificate
    {rows columns : ℕ} (replay : Float32HiddenStageReplay rows columns)
    (hcheck : replay.check = true) :
    LocalEvaluationErrorCertificate replay.idealBlockAtRecordedError
      replay.runtimePreviousCenter replay.decodedOutput
      (replay.totalCertifiedErrorRat : ℝ) := by
  have hlocal := replay.toLocalEvaluationErrorCertificate hcheck
  refine
    { localError_nonneg := hlocal.localError_nonneg
      output_error_le := ?_ }
  simpa [Float32HiddenStageReplay.idealBlockAtRecordedError,
    Float32HiddenStageReplay.runtimePreviousCenter,
    Float32HiddenStageReplay.decodedInput] using hlocal.output_error_le

/-! ## Finite invocation batches -/

structure Float32HiddenStageReplayBatch (rows columns : ℕ) where
  expectedCount : ℕ
  entries : List (Float32HiddenStageReplay rows columns)

def Float32HiddenStageReplayBatch.Valid
    {rows columns : ℕ}
    (batch : Float32HiddenStageReplayBatch rows columns) : Prop :=
  0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount ∧
    ∀ replay ∈ batch.entries, replay.Valid

def Float32HiddenStageReplayBatch.check
    {rows columns : ℕ}
    (batch : Float32HiddenStageReplayBatch rows columns) : Bool :=
  decide (0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount) &&
    batch.entries.all Float32HiddenStageReplay.check

theorem Float32HiddenStageReplayBatch.check_eq_true_iff
    {rows columns : ℕ}
    (batch : Float32HiddenStageReplayBatch rows columns) :
    batch.check = true ↔ batch.Valid := by
  simp [Float32HiddenStageReplayBatch.check,
    Float32HiddenStageReplayBatch.Valid, List.all_eq_true,
    Float32HiddenStageReplay.check_eq_true_iff, and_assoc]

def Float32HiddenStageReplayBatch.totalObservedError
    {rows columns : ℕ}
    (batch : Float32HiddenStageReplayBatch rows columns) : ℝ :=
  (batch.entries.map fun replay ↦
    ‖replay.decodedOutput - replay.idealBlock replay.decodedInput‖).sum

def Float32HiddenStageReplayBatch.totalCertifiedError
    {rows columns : ℕ}
    (batch : Float32HiddenStageReplayBatch rows columns) : ℝ :=
  (batch.entries.map fun replay ↦
    (replay.totalCertifiedErrorRat : ℝ)).sum

theorem Float32HiddenStageReplayBatch.totalObservedError_le
    {rows columns : ℕ}
    (batch : Float32HiddenStageReplayBatch rows columns)
    (hcheck : batch.check = true) :
    batch.totalObservedError ≤ batch.totalCertifiedError := by
  apply List.sum_le_sum
  intro replay hmem
  have hvalid := (batch.check_eq_true_iff.mp hcheck).2.2 replay hmem
  exact replay.sound (replay.check_eq_true_iff.mpr hvalid)

/-! ## Positive and negative fixtures -/

def zeroWord : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def hiddenAdd : Float32AddReplay where
  left := Float32ActivationReplayCertificate.positiveFiveSixteenths
  right := zeroWord
  output := Float32ActivationReplayCertificate.positiveFiveSixteenths
  localError := 0

def hiddenMask : Float32MaskReplay where
  active := true
  input := Float32ActivationReplayCertificate.positiveFiveSixteenths
  output := Float32ActivationReplayCertificate.positiveFiveSixteenths
  localError := 0

def hiddenAddMask : Float32AddMaskReplay where
  add := hiddenAdd
  mask := hiddenMask

theorem hiddenAddMask_is_accepted : hiddenAddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check, hiddenAddMask, hiddenAdd, hiddenMask, boolRat,
    zeroWord, Float32ActivationReplayCertificate.positiveFiveSixteenths,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def hiddenStage : Float32HiddenStageReplay 1 1 where
  affineSiLU := halfSiLUReplay
  errorSite := fun _ ↦ zeroWord
  addMask := fun _ ↦ hiddenAddMask

theorem hiddenStage_is_accepted : hiddenStage.check = true := by
  apply (Float32HiddenStageReplay.check_eq_true_iff hiddenStage).mpr
  refine ⟨(Float32AffineSiLUReplay.check_eq_true_iff halfSiLUReplay).mp
    halfSiLUReplay_is_accepted, ?_⟩
  intro row
  fin_cases row
  exact ⟨(Float32AddMaskReplay.check_eq_true_iff hiddenAddMask).mp
    hiddenAddMask_is_accepted, rfl, rfl⟩

theorem hiddenStage_sound :
    ‖hiddenStage.decodedOutput - hiddenStage.idealBlock hiddenStage.decodedInput‖ ≤
      (hiddenStage.totalCertifiedErrorRat : ℝ) :=
  hiddenStage.sound hiddenStage_is_accepted

def hiddenStageBatch : Float32HiddenStageReplayBatch 1 1 where
  expectedCount := 1
  entries := [hiddenStage]

theorem hiddenStageBatch_is_accepted : hiddenStageBatch.check = true := by
  simp [Float32HiddenStageReplayBatch.check, hiddenStageBatch,
    hiddenStage_is_accepted]

theorem hiddenStageBatch_total_error_is_bounded :
    hiddenStageBatch.totalObservedError ≤
      hiddenStageBatch.totalCertifiedError :=
  hiddenStageBatch.totalObservedError_le hiddenStageBatch_is_accepted

/-- The component replay is valid, but the separately recorded error-site word
does not equal the addition's right input. -/
def wrongErrorBinding : Float32HiddenStageReplay 1 1 :=
  { hiddenStage with
    errorSite := fun _ ↦ Float32AddMaskReplayCertificate.positiveQuarter }

theorem wrongErrorBinding_is_rejected : wrongErrorBinding.check = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  have hvalid :=
    (Float32HiddenStageReplay.check_eq_true_iff wrongErrorBinding).mp hcheck
  have hword := (hvalid.2 (0 : Fin 1)).2.2
  norm_num [wrongErrorBinding, hiddenStage, hiddenAddMask, hiddenAdd,
    zeroWord, Float32AddMaskReplayCertificate.positiveQuarter] at hword

/-- Empty batches are rejected even when their declared count is zero. -/
def emptyHiddenStageBatch : Float32HiddenStageReplayBatch 1 1 where
  expectedCount := 0
  entries := []

theorem emptyHiddenStageBatch_is_rejected :
    emptyHiddenStageBatch.check = false := by
  norm_num [Float32HiddenStageReplayBatch.check, emptyHiddenStageBatch]

#print axioms Float32HiddenStageReplay.check_eq_true_iff
#print axioms Float32HiddenStageReplay.coordinate_error_le
#print axioms Float32HiddenStageReplay.totalCoordinateError_le
#print axioms Float32HiddenStageReplay.sound
#print axioms Float32HiddenStageReplay.toLocalEvaluationErrorCertificate
#print axioms Float32HiddenStageReplay.toPreviousCenterLocalCertificate
#print axioms Float32HiddenStageReplayBatch.totalObservedError_le
#print axioms hiddenStage_is_accepted
#print axioms hiddenStageBatch_total_error_is_bounded
#print axioms wrongErrorBinding_is_rejected
#print axioms emptyHiddenStageBatch_is_rejected

end

end Float32HiddenStageReplayCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
