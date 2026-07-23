import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineReplayCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AddMaskReplayCertificate
import Mathlib.Tactic

/-!
# Exact binary32 affine-to-mask replay certificates

The audited deep error-coordinate adapter applies a final affine readout and
then multiplies that readout by the Boolean node mask.  This module treats the
mask as a distinct runtime operation and connects each recorded affine output
word to its corresponding mask input word.

The kernel checks arithmetic and the interior word connection.  Runtime source
identity, endpoint hashes, backend evaluation order, and invocation coverage
remain external obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32AffineMaskReplayCertificate

open Float32CheckpointMatrix
open Float32AffineReplayCertificate
open Float32AddMaskReplayCertificate
open FiniteMatrixOperatorBounds
open FinitePrecisionEvaluationError

noncomputable section

/-- One observed affine map followed coordinatewise by a Boolean mask. -/
structure Float32AffineMaskReplay (rows columns : ℕ) where
  affine : Float32AffineReplay rows columns
  mask : Fin rows → Float32MaskReplay

def Float32AffineMaskReplay.Valid
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns) : Prop :=
  replay.affine.Valid ∧
    ∀ row, (replay.mask row).Valid ∧
      (replay.mask row).input.word = (replay.affine.output row).word

def Float32AffineMaskReplay.check
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns) : Bool :=
  replay.affine.check &&
    decide (∀ row, (replay.mask row).check = true ∧
      (replay.mask row).input.word = (replay.affine.output row).word)

theorem Float32AffineMaskReplay.check_eq_true_iff
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32AffineMaskReplay.check, Float32AffineMaskReplay.Valid,
    Float32AffineReplay.check_eq_true_iff,
    Float32MaskReplay.check_eq_true_iff]

def Float32AffineMaskReplay.decodedInput
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns) :
    EuclideanSpace ℝ (Fin columns) :=
  replay.affine.decodedInput

def Float32AffineMaskReplay.decodedOutput
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns) :
    EuclideanSpace ℝ (Fin rows) :=
  WithLp.toLp 2 fun row ↦ (replay.mask row).output.toReal

def Float32AffineMaskReplay.idealMap
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns) :
    EuclideanSpace ℝ (Fin columns) → EuclideanSpace ℝ (Fin rows) :=
  fun input ↦ WithLp.toLp 2 fun row ↦
    (boolRat (replay.mask row).active : ℝ) *
      replay.affine.idealAffine input row

def Float32AffineMaskReplay.totalMaskErrorRat
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns) : ℚ :=
  ∑ row, (replay.mask row).localError

/-- Conservative local error: every mask-local error plus the accepted
entrywise affine budget. -/
def Float32AffineMaskReplay.totalCertifiedErrorRat
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns) : ℚ :=
  replay.totalMaskErrorRat + replay.affine.localError

private theorem finiteWord_toReal_eq_of_word_eq
    {left right : FiniteFloat32Word} (hword : left.word = right.word) :
    left.toReal = right.toReal := by
  simp [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat, hword]

theorem Float32AffineMaskReplay.coordinate_error_le
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns)
    (hcheck : replay.check = true) (row : Fin rows) :
    |replay.decodedOutput row -
        replay.idealMap replay.decodedInput row| ≤
      ((replay.mask row).localError : ℝ) +
        |replay.affine.decodedOutput row -
          replay.affine.idealAffine replay.affine.decodedInput row| := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have hmaskCheck : (replay.mask row).check = true :=
    (replay.mask row).check_eq_true_iff.mpr (hvalid.2 row).1
  have hmask := (replay.mask row).sound hmaskCheck
  have hwire :
      (replay.mask row).input.toReal =
        (replay.affine.output row).toReal :=
    finiteWord_toReal_eq_of_word_eq (hvalid.2 row).2
  cases hactive : (replay.mask row).active with
  | false =>
      have hnonneg :
          0 ≤ |replay.affine.decodedOutput row -
            replay.affine.idealAffine replay.affine.decodedInput row| :=
        abs_nonneg _
      exact (by
        simpa [Float32AffineMaskReplay.decodedOutput,
          Float32AffineMaskReplay.idealMap,
          Float32AffineMaskReplay.decodedInput, hactive, boolRat] using
            hmask.trans (le_add_of_nonneg_right hnonneg))
  | true =>
      have htriangle :
          |(replay.mask row).output.toReal -
              replay.affine.idealAffine replay.affine.decodedInput row| ≤
            |(replay.mask row).output.toReal -
              (replay.mask row).input.toReal| +
            |(replay.mask row).input.toReal -
              replay.affine.idealAffine replay.affine.decodedInput row| :=
        abs_sub_le _ _ _
      calc
        |replay.decodedOutput row -
            replay.idealMap replay.decodedInput row| ≤
            |(replay.mask row).output.toReal -
              (replay.mask row).input.toReal| +
            |(replay.mask row).input.toReal -
              replay.affine.idealAffine replay.affine.decodedInput row| := by
          simpa [Float32AffineMaskReplay.decodedOutput,
            Float32AffineMaskReplay.idealMap,
            Float32AffineMaskReplay.decodedInput, hactive, boolRat] using
              htriangle
        _ = |(replay.mask row).output.toReal -
              (replay.mask row).input.toReal| +
            |replay.affine.decodedOutput row -
              replay.affine.idealAffine replay.affine.decodedInput row| := by
          rw [hwire]
          rfl
        _ ≤ ((replay.mask row).localError : ℝ) +
            |replay.affine.decodedOutput row -
              replay.affine.idealAffine replay.affine.decodedInput row| :=
          add_le_add
            (by simpa [hactive, boolRat] using hmask) (le_refl _)

theorem Float32AffineMaskReplay.totalCoordinateError_le
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns)
    (hcheck : replay.check = true) :
    (∑ row, |replay.decodedOutput row -
      replay.idealMap replay.decodedInput row|) ≤
      (replay.totalCertifiedErrorRat : ℝ) := by
  have haffineCheck : replay.affine.check = true :=
    replay.affine.check_eq_true_iff.mpr
      (replay.check_eq_true_iff.mp hcheck).1
  have haffineBound :
      (replay.affine.totalAbsoluteErrorRat : ℝ) ≤
        (replay.affine.localError : ℝ) := by
    exact_mod_cast
      (replay.affine.check_eq_true_iff.mp haffineCheck).2.2.2
  calc
    (∑ row, |replay.decodedOutput row -
      replay.idealMap replay.decodedInput row|) ≤
        ∑ row, (((replay.mask row).localError : ℝ) +
          |replay.affine.decodedOutput row -
            replay.affine.idealAffine replay.affine.decodedInput row|) :=
      Finset.sum_le_sum fun row _ ↦ replay.coordinate_error_le hcheck row
    _ = (∑ row, ((replay.mask row).localError : ℝ)) +
        (∑ row, |replay.affine.decodedOutput row -
          replay.affine.idealAffine replay.affine.decodedInput row|) := by
      rw [Finset.sum_add_distrib]
    _ = (replay.totalMaskErrorRat : ℝ) +
        (replay.affine.totalAbsoluteErrorRat : ℝ) := by
      rw [replay.affine.totalAbsoluteErrorReal_eq]
      simp [Float32AffineMaskReplay.totalMaskErrorRat, Rat.cast_sum]
    _ ≤ (replay.totalMaskErrorRat : ℝ) +
        (replay.affine.localError : ℝ) :=
      add_le_add (le_refl _) haffineBound
    _ = (replay.totalCertifiedErrorRat : ℝ) := by
      simp [Float32AffineMaskReplay.totalCertifiedErrorRat, Rat.cast_add]

theorem Float32AffineMaskReplay.sound
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns)
    (hcheck : replay.check = true) :
    ‖replay.decodedOutput - replay.idealMap replay.decodedInput‖ ≤
      (replay.totalCertifiedErrorRat : ℝ) := by
  exact (euclidean_norm_le_entrywiseL1 _).trans
    (replay.totalCoordinateError_le hcheck)

theorem Float32AffineMaskReplay.toLocalEvaluationErrorCertificate
    {rows columns : ℕ} (replay : Float32AffineMaskReplay rows columns)
    (hcheck : replay.check = true) :
    LocalEvaluationErrorCertificate replay.idealMap replay.decodedInput
      replay.decodedOutput (replay.totalCertifiedErrorRat : ℝ) := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have hmaskNonneg : 0 ≤ replay.totalMaskErrorRat := by
    exact Finset.sum_nonneg fun row _ ↦ (hvalid.2 row).1.1
  have haffineNonneg : 0 ≤ replay.affine.localError := hvalid.1.2.2.1
  refine
    { localError_nonneg := ?_
      output_error_le := replay.sound hcheck }
  exact_mod_cast add_nonneg hmaskNonneg haffineNonneg

/-! ## Finite batches -/

structure Float32AffineMaskReplayBatch (rows columns : ℕ) where
  expectedCount : ℕ
  entries : List (Float32AffineMaskReplay rows columns)

def Float32AffineMaskReplayBatch.Valid
    {rows columns : ℕ}
    (batch : Float32AffineMaskReplayBatch rows columns) : Prop :=
  0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount ∧
    ∀ replay ∈ batch.entries, replay.Valid

def Float32AffineMaskReplayBatch.check
    {rows columns : ℕ}
    (batch : Float32AffineMaskReplayBatch rows columns) : Bool :=
  decide (0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount) &&
    batch.entries.all Float32AffineMaskReplay.check

theorem Float32AffineMaskReplayBatch.check_eq_true_iff
    {rows columns : ℕ}
    (batch : Float32AffineMaskReplayBatch rows columns) :
    batch.check = true ↔ batch.Valid := by
  simp [Float32AffineMaskReplayBatch.check,
    Float32AffineMaskReplayBatch.Valid, List.all_eq_true,
    Float32AffineMaskReplay.check_eq_true_iff, and_assoc]

def Float32AffineMaskReplayBatch.totalObservedError
    {rows columns : ℕ}
    (batch : Float32AffineMaskReplayBatch rows columns) : ℝ :=
  (batch.entries.map fun replay ↦
    ‖replay.decodedOutput - replay.idealMap replay.decodedInput‖).sum

def Float32AffineMaskReplayBatch.totalCertifiedError
    {rows columns : ℕ}
    (batch : Float32AffineMaskReplayBatch rows columns) : ℝ :=
  (batch.entries.map fun replay ↦
    (replay.totalCertifiedErrorRat : ℝ)).sum

theorem Float32AffineMaskReplayBatch.totalObservedError_le
    {rows columns : ℕ}
    (batch : Float32AffineMaskReplayBatch rows columns)
    (hcheck : batch.check = true) :
    batch.totalObservedError ≤ batch.totalCertifiedError := by
  apply List.sum_le_sum
  intro replay hmem
  have hvalid := (batch.check_eq_true_iff.mp hcheck).2.2 replay hmem
  exact replay.sound <| replay.check_eq_true_iff.mpr hvalid

/-! ## Positive and negative fixtures -/

def zeroWord : FiniteFloat32Word where
  word := 0
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def oneWord : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def identityAffine : Float32AffineReplay 1 1 where
  input := ![oneWord]
  weight := ![oneWord]
  bias := ![zeroWord]
  output := ![oneWord]
  localError := 0

theorem identityAffine_is_accepted : identityAffine.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, identityAffine, zeroWord, oneWord,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa, rowMajorIndex]

def activeOneMask : Float32MaskReplay where
  active := true
  input := oneWord
  output := oneWord
  localError := 0

def inactiveOneMask : Float32MaskReplay where
  active := false
  input := oneWord
  output := zeroWord
  localError := 0

def activeZeroMask : Float32MaskReplay where
  active := true
  input := zeroWord
  output := zeroWord
  localError := 0

def corruptActiveMask : Float32MaskReplay where
  active := true
  input := oneWord
  output := zeroWord
  localError := 0

def activeFixture : Float32AffineMaskReplay 1 1 where
  affine := identityAffine
  mask := ![activeOneMask]

def inactiveFixture : Float32AffineMaskReplay 1 1 where
  affine := identityAffine
  mask := ![inactiveOneMask]

def miswiredFixture : Float32AffineMaskReplay 1 1 where
  affine := identityAffine
  mask := ![activeZeroMask]

def corruptFixture : Float32AffineMaskReplay 1 1 where
  affine := identityAffine
  mask := ![corruptActiveMask]

theorem activeFixture_is_accepted : activeFixture.check = true := by
  rw [Float32AffineMaskReplay.check]
  rw [show activeFixture.affine.check = true from identityAffine_is_accepted]
  simp [activeFixture, Float32MaskReplay.check, activeOneMask,
    identityAffine, oneWord, boolRat, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

theorem inactiveFixture_is_accepted : inactiveFixture.check = true := by
  rw [Float32AffineMaskReplay.check]
  rw [show inactiveFixture.affine.check = true from identityAffine_is_accepted]
  simp [inactiveFixture, Float32MaskReplay.check, inactiveOneMask,
    identityAffine, zeroWord, oneWord, boolRat, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

theorem miswiredFixture_is_rejected : miswiredFixture.check = false := by
  rw [Float32AffineMaskReplay.check]
  rw [show miswiredFixture.affine.check = true from identityAffine_is_accepted]
  simp [miswiredFixture, Float32MaskReplay.check, activeZeroMask,
    identityAffine, zeroWord, oneWord, boolRat, FiniteFloat32Word.toRat,
    float32Exponent, float32Mantissa]

theorem corruptFixture_is_rejected : corruptFixture.check = false := by
  norm_num [Float32AffineMaskReplay.check, corruptFixture,
    identityAffine_is_accepted, Float32MaskReplay.check,
    corruptActiveMask, zeroWord, oneWord, boolRat,
    FiniteFloat32Word.toRat, float32Exponent, float32Mantissa]

#print axioms Float32AffineMaskReplay.check_eq_true_iff
#print axioms Float32AffineMaskReplay.coordinate_error_le
#print axioms Float32AffineMaskReplay.totalCoordinateError_le
#print axioms Float32AffineMaskReplay.sound
#print axioms Float32AffineMaskReplay.toLocalEvaluationErrorCertificate
#print axioms Float32AffineMaskReplayBatch.check_eq_true_iff
#print axioms Float32AffineMaskReplayBatch.totalObservedError_le
#print axioms activeFixture_is_accepted
#print axioms inactiveFixture_is_accepted
#print axioms miswiredFixture_is_rejected
#print axioms corruptFixture_is_rejected

end

end Float32AffineMaskReplayCertificate
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
