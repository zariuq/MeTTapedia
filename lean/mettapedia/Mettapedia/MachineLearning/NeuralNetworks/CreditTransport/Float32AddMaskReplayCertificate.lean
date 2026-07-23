import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointMatrix
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionEvaluationError
import Mathlib.Tactic

/-!
# Exact binary32 addition and Boolean-mask replay certificates

The audited hidden adapter forms a state coordinate by adding a predicted
activation to an inferred error and then multiplying by a zero-one node mask.
This module checks those two observed binary32 operations pointwise.  Exact
word equality connects the recorded addition output to the mask input.

The kernel certifies arithmetic among the supplied words.  Trace provenance,
backend evaluation order, and coverage of actual invocations remain external
obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32AddMaskReplayCertificate

open Float32CheckpointMatrix
open FinitePrecisionEvaluationError

noncomputable section

/-- Rational zero-one scalar represented by a Boolean runtime mask. -/
def boolRat : Bool → ℚ
  | false => 0
  | true => 1

/-- One observed binary32 addition with an exact decoded-real error budget. -/
structure Float32AddReplay where
  left : FiniteFloat32Word
  right : FiniteFloat32Word
  output : FiniteFloat32Word
  localError : ℚ

def Float32AddReplay.Valid (replay : Float32AddReplay) : Prop :=
  0 ≤ replay.localError ∧
    |replay.output.toRat - (replay.left.toRat + replay.right.toRat)| ≤
      replay.localError

def Float32AddReplay.check (replay : Float32AddReplay) : Bool :=
  decide (0 ≤ replay.localError ∧
    |replay.output.toRat - (replay.left.toRat + replay.right.toRat)| ≤
      replay.localError)

theorem Float32AddReplay.check_eq_true_iff (replay : Float32AddReplay) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32AddReplay.check, Float32AddReplay.Valid]

theorem Float32AddReplay.sound (replay : Float32AddReplay)
    (hcheck : replay.check = true) :
    |replay.output.toReal - (replay.left.toReal + replay.right.toReal)| ≤
      (replay.localError : ℝ) := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  rw [← replay.output.cast_toRat, ← replay.left.cast_toRat,
    ← replay.right.cast_toRat, ← Rat.cast_add, ← Rat.cast_sub,
    ← Rat.cast_abs]
  exact_mod_cast hvalid.2

/-- One observed multiplication by a Boolean node mask. -/
structure Float32MaskReplay where
  active : Bool
  input : FiniteFloat32Word
  output : FiniteFloat32Word
  localError : ℚ

def Float32MaskReplay.Valid (replay : Float32MaskReplay) : Prop :=
  0 ≤ replay.localError ∧
    |replay.output.toRat - boolRat replay.active * replay.input.toRat| ≤
      replay.localError

def Float32MaskReplay.check (replay : Float32MaskReplay) : Bool :=
  decide (0 ≤ replay.localError ∧
    |replay.output.toRat - boolRat replay.active * replay.input.toRat| ≤
      replay.localError)

theorem Float32MaskReplay.check_eq_true_iff (replay : Float32MaskReplay) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32MaskReplay.check, Float32MaskReplay.Valid]

theorem Float32MaskReplay.sound (replay : Float32MaskReplay)
    (hcheck : replay.check = true) :
    |replay.output.toReal - (boolRat replay.active : ℝ) * replay.input.toReal| ≤
      (replay.localError : ℝ) := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  rw [← replay.output.cast_toRat, ← replay.input.cast_toRat,
    ← Rat.cast_mul, ← Rat.cast_sub, ← Rat.cast_abs]
  exact_mod_cast hvalid.2

/-- Addition followed by masking, connected by the exact intermediate word. -/
structure Float32AddMaskReplay where
  add : Float32AddReplay
  mask : Float32MaskReplay

def Float32AddMaskReplay.Valid (replay : Float32AddMaskReplay) : Prop :=
  replay.add.Valid ∧ replay.mask.Valid ∧
    replay.mask.input.word = replay.add.output.word

def Float32AddMaskReplay.check (replay : Float32AddMaskReplay) : Bool :=
  replay.add.check && replay.mask.check &&
    decide (replay.mask.input.word = replay.add.output.word)

theorem Float32AddMaskReplay.check_eq_true_iff
    (replay : Float32AddMaskReplay) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32AddMaskReplay.check, Float32AddMaskReplay.Valid,
    Float32AddReplay.check_eq_true_iff,
    Float32MaskReplay.check_eq_true_iff, and_assoc]

def Float32AddMaskReplay.decodedInput (replay : Float32AddMaskReplay) : ℝ × ℝ :=
  (replay.add.left.toReal, replay.add.right.toReal)

def Float32AddMaskReplay.decodedOutput (replay : Float32AddMaskReplay) : ℝ :=
  replay.mask.output.toReal

def Float32AddMaskReplay.idealMap (replay : Float32AddMaskReplay) :
    ℝ × ℝ → ℝ :=
  fun input ↦ (boolRat replay.mask.active : ℝ) * (input.1 + input.2)

/-- The mask-local error plus the active branch's addition error. -/
def Float32AddMaskReplay.totalCertifiedErrorRat
    (replay : Float32AddMaskReplay) : ℚ :=
  replay.mask.localError + boolRat replay.mask.active * replay.add.localError

private theorem finiteWord_toReal_eq_of_word_eq
    {left right : FiniteFloat32Word} (hword : left.word = right.word) :
    left.toReal = right.toReal := by
  simp [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat, hword]

theorem Float32AddMaskReplay.sound (replay : Float32AddMaskReplay)
    (hcheck : replay.check = true) :
    |replay.decodedOutput - replay.idealMap replay.decodedInput| ≤
      (replay.totalCertifiedErrorRat : ℝ) := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have hadd := replay.add.sound <|
    replay.add.check_eq_true_iff.mpr hvalid.1
  have hmask := replay.mask.sound <|
    replay.mask.check_eq_true_iff.mpr hvalid.2.1
  have hword : replay.mask.input.toReal = replay.add.output.toReal :=
    finiteWord_toReal_eq_of_word_eq hvalid.2.2
  cases hactive : replay.mask.active with
  | false =>
      simpa [Float32AddMaskReplay.decodedOutput,
        Float32AddMaskReplay.idealMap,
        Float32AddMaskReplay.decodedInput,
        Float32AddMaskReplay.totalCertifiedErrorRat,
        hactive, boolRat] using hmask
  | true =>
      have htriangle :
          |replay.mask.output.toReal -
              (replay.add.left.toReal + replay.add.right.toReal)| ≤
            |replay.mask.output.toReal - replay.mask.input.toReal| +
              |replay.mask.input.toReal -
                (replay.add.left.toReal + replay.add.right.toReal)| :=
        abs_sub_le _ _ _
      calc
        |replay.decodedOutput - replay.idealMap replay.decodedInput| ≤
            |replay.mask.output.toReal - replay.mask.input.toReal| +
              |replay.mask.input.toReal -
                (replay.add.left.toReal + replay.add.right.toReal)| := by
          simpa [Float32AddMaskReplay.decodedOutput,
            Float32AddMaskReplay.idealMap,
            Float32AddMaskReplay.decodedInput, hactive, boolRat] using htriangle
        _ = |replay.mask.output.toReal - replay.mask.input.toReal| +
              |replay.add.output.toReal -
                (replay.add.left.toReal + replay.add.right.toReal)| := by
          rw [hword]
        _ ≤ (replay.mask.localError : ℝ) +
              (replay.add.localError : ℝ) :=
          add_le_add (by simpa [hactive, boolRat] using hmask) hadd
        _ = (replay.totalCertifiedErrorRat : ℝ) := by
          simp [Float32AddMaskReplay.totalCertifiedErrorRat, hactive, boolRat]

theorem Float32AddMaskReplay.toLocalEvaluationErrorCertificate
    (replay : Float32AddMaskReplay) (hcheck : replay.check = true) :
    LocalEvaluationErrorCertificate replay.idealMap replay.decodedInput
      replay.decodedOutput (replay.totalCertifiedErrorRat : ℝ) := by
  refine
    { localError_nonneg := ?_
      output_error_le := by
        simpa [Real.norm_eq_abs] using replay.sound hcheck }
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have hadd : 0 ≤ replay.add.localError := hvalid.1.1
  have hmask : 0 ≤ replay.mask.localError := hvalid.2.1.1
  have htotalRat : 0 ≤ replay.totalCertifiedErrorRat := by
    cases hactive : replay.mask.active with
    | false =>
        simpa [Float32AddMaskReplay.totalCertifiedErrorRat, hactive, boolRat]
          using hmask
    | true =>
        simpa [Float32AddMaskReplay.totalCertifiedErrorRat, hactive, boolRat]
          using add_nonneg hmask hadd
  exact_mod_cast htotalRat

/-! ## Finite batches -/

structure Float32AddMaskReplayBatch where
  expectedCount : ℕ
  entries : List Float32AddMaskReplay

def Float32AddMaskReplayBatch.Valid (batch : Float32AddMaskReplayBatch) : Prop :=
  0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount ∧
    ∀ replay ∈ batch.entries, replay.Valid

def Float32AddMaskReplayBatch.check (batch : Float32AddMaskReplayBatch) : Bool :=
  decide (0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount) &&
    batch.entries.all Float32AddMaskReplay.check

theorem Float32AddMaskReplayBatch.check_eq_true_iff
    (batch : Float32AddMaskReplayBatch) :
    batch.check = true ↔ batch.Valid := by
  simp [Float32AddMaskReplayBatch.check, Float32AddMaskReplayBatch.Valid,
    List.all_eq_true, Float32AddMaskReplay.check_eq_true_iff, and_assoc]

def Float32AddMaskReplayBatch.totalObservedError
    (batch : Float32AddMaskReplayBatch) : ℝ :=
  (batch.entries.map fun replay ↦
    |replay.decodedOutput - replay.idealMap replay.decodedInput|).sum

def Float32AddMaskReplayBatch.totalCertifiedError
    (batch : Float32AddMaskReplayBatch) : ℝ :=
  (batch.entries.map fun replay ↦
    (replay.totalCertifiedErrorRat : ℝ)).sum

theorem Float32AddMaskReplayBatch.totalObservedError_le
    (batch : Float32AddMaskReplayBatch) (hcheck : batch.check = true) :
    batch.totalObservedError ≤ batch.totalCertifiedError := by
  apply List.sum_le_sum
  intro replay hmem
  have hvalid := (batch.check_eq_true_iff.mp hcheck).2.2 replay hmem
  exact replay.sound <| replay.check_eq_true_iff.mpr hvalid

/-! ## Positive and negative fixtures -/

def positiveHalf : FiniteFloat32Word where
  word := 1056964608
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveQuarter : FiniteFloat32Word where
  word := 1048576000
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveThreeQuarters : FiniteFloat32Word where
  word := 1061158912
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def zeroWord : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def exactAdd : Float32AddReplay where
  left := positiveHalf
  right := positiveQuarter
  output := positiveThreeQuarters
  localError := 0

theorem exactAdd_is_accepted : exactAdd.check = true := by
  norm_num [Float32AddReplay.check, Float32AddReplay.Valid, exactAdd,
    positiveHalf, positiveQuarter,
    positiveThreeQuarters, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa]

def activeMask : Float32MaskReplay where
  active := true
  input := positiveThreeQuarters
  output := positiveThreeQuarters
  localError := 0

theorem activeMask_is_accepted : activeMask.check = true := by
  norm_num [Float32MaskReplay.check, Float32MaskReplay.Valid, activeMask,
    boolRat, positiveThreeQuarters, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def activeAddMask : Float32AddMaskReplay where
  add := exactAdd
  mask := activeMask

theorem activeAddMask_is_accepted : activeAddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, activeAddMask, exactAdd,
    activeMask, Float32AddReplay.check, Float32AddReplay.Valid,
    Float32MaskReplay.check, Float32MaskReplay.Valid, boolRat,
    positiveHalf, positiveQuarter, positiveThreeQuarters,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def inactiveMask : Float32MaskReplay where
  active := false
  input := positiveThreeQuarters
  output := zeroWord
  localError := 0

def inactiveAddMask : Float32AddMaskReplay where
  add := exactAdd
  mask := inactiveMask

theorem inactiveAddMask_is_accepted : inactiveAddMask.check = true := by
  norm_num [Float32AddMaskReplay.check, Float32AddReplay.check,
    Float32MaskReplay.check,
    Float32MaskReplay.Valid, inactiveAddMask, inactiveMask, exactAdd,
    boolRat, positiveHalf, positiveQuarter, positiveThreeQuarters, zeroWord,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

def positiveBatch : Float32AddMaskReplayBatch where
  expectedCount := 2
  entries := [activeAddMask, inactiveAddMask]

theorem positiveBatch_is_accepted : positiveBatch.check = true := by
  simp [Float32AddMaskReplayBatch.check, positiveBatch,
    activeAddMask_is_accepted, inactiveAddMask_is_accepted]

theorem positiveBatch_total_error_is_bounded :
    positiveBatch.totalObservedError ≤ positiveBatch.totalCertifiedError :=
  positiveBatch.totalObservedError_le positiveBatch_is_accepted

/-- Both operations are valid, but the mask consumes a different word. -/
def halfActiveMask : Float32MaskReplay where
  active := true
  input := positiveHalf
  output := positiveHalf
  localError := 0

theorem halfActiveMask_is_accepted : halfActiveMask.check = true := by
  norm_num [Float32MaskReplay.check, Float32MaskReplay.Valid,
    halfActiveMask, boolRat, positiveHalf, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

def miswiredAddMask : Float32AddMaskReplay where
  add := exactAdd
  mask := halfActiveMask

theorem miswiredAddMask_is_rejected : miswiredAddMask.check = false := by
  norm_num [Float32AddMaskReplay.check, miswiredAddMask, exactAdd,
    halfActiveMask, Float32AddReplay.check, Float32AddReplay.Valid,
    Float32MaskReplay.check, Float32MaskReplay.Valid, boolRat,
    positiveHalf, positiveQuarter,
    positiveThreeQuarters, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa]

/-- A false mask cannot retain the unmasked word at zero local error. -/
def corruptInactiveMask : Float32MaskReplay where
  active := false
  input := positiveThreeQuarters
  output := positiveThreeQuarters
  localError := 0

theorem corruptInactiveMask_is_rejected : corruptInactiveMask.check = false := by
  norm_num [Float32MaskReplay.check, Float32MaskReplay.Valid,
    corruptInactiveMask, boolRat, positiveThreeQuarters,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

/-- Empty batches are rejected even when the declared count is zero. -/
def emptyBatch : Float32AddMaskReplayBatch where
  expectedCount := 0
  entries := []

theorem emptyBatch_is_rejected : emptyBatch.check = false := by
  norm_num [Float32AddMaskReplayBatch.check, emptyBatch]

#print axioms Float32AddReplay.sound
#print axioms Float32MaskReplay.sound
#print axioms Float32AddMaskReplay.check_eq_true_iff
#print axioms Float32AddMaskReplay.sound
#print axioms Float32AddMaskReplay.toLocalEvaluationErrorCertificate
#print axioms Float32AddMaskReplayBatch.totalObservedError_le
#print axioms positiveBatch_total_error_is_bounded
#print axioms halfActiveMask_is_accepted
#print axioms miswiredAddMask_is_rejected
#print axioms corruptInactiveMask_is_rejected
#print axioms emptyBatch_is_rejected

end

end Float32AddMaskReplayCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
