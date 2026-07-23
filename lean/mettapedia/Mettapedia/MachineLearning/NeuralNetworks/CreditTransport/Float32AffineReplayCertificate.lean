import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointMatrix
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionEvaluationError
import Mathlib.Tactic

/-!
# Exact binary32 affine replay certificates

A traced affine layer supplies finite binary32 words for its input, row-major
weight, bias, and observed output.  This module decodes those words exactly,
recomputes the declared real affine map at the decoded input, and checks a
rational entrywise error budget.  The resulting Euclidean local-evaluation
certificate is independent of the runtime's internal accumulation order: it
relates the observed output words to the mathematical affine map after the
fact.  It is a pointwise certificate and does not claim a uniform regional
roundoff bound or identify a particular BLAS/CUDA evaluation schedule.

The kernel certifies the arithmetic relation among the supplied words.  An
external source-correspondence verifier and its hashes must separately bind
those words to a checkpoint invocation.  A source hash printed in generated
Lean as a comment is provenance metadata, not kernel evidence.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32AffineReplayCertificate

open scoped BigOperators
open Float32CheckpointMatrix
open FiniteMatrixOperatorBounds
open FinitePrecisionEvaluationError

noncomputable section

/-- Exact replay payload for one nonempty affine map with a row-major weight
tensor of shape `[rows, columns]`. -/
structure Float32AffineReplay (rows columns : ℕ) where
  input : Fin columns → FiniteFloat32Word
  weight : Fin (rows * columns) → FiniteFloat32Word
  bias : Fin rows → FiniteFloat32Word
  output : Fin rows → FiniteFloat32Word
  localError : ℚ

/-- Construct a replay from a matrix-shaped weight family.  This is
extensionally the flat row-major representation above, but generated proofs
can retain the row boundary while checking a dot product. -/
def Float32AffineReplay.ofRows {rows columns : ℕ}
    (input : Fin columns → FiniteFloat32Word)
    (weightRows : Fin rows → Fin columns → FiniteFloat32Word)
    (bias output : Fin rows → FiniteFloat32Word)
    (localError : ℚ) : Float32AffineReplay rows columns where
  input := input
  weight := rowMajorFlatten weightRows
  bias := bias
  output := output
  localError := localError

/-- Exact rational result of one affine output coordinate. -/
def Float32AffineReplay.idealOutputRat
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns)
    (row : Fin rows) : ℚ :=
  (replay.bias row).toRat +
    ∑ column, (replay.weight (rowMajorIndex rows columns row column)).toRat *
      (replay.input column).toRat

@[simp]
theorem Float32AffineReplay.ofRows_idealOutputRat
    {rows columns : ℕ}
    (input : Fin columns → FiniteFloat32Word)
    (weightRows : Fin rows → Fin columns → FiniteFloat32Word)
    (bias output : Fin rows → FiniteFloat32Word)
    (localError : ℚ) (row : Fin rows) :
    (Float32AffineReplay.ofRows input weightRows bias output localError).idealOutputRat row =
      (bias row).toRat +
        ∑ column, (weightRows row column).toRat * (input column).toRat := by
  simp [Float32AffineReplay.idealOutputRat, Float32AffineReplay.ofRows]

/-- A row-local arithmetic inequality lifts directly to the corresponding
coordinate of a row-constructed replay.  Generated certificates use this
bridge to keep the concrete matrix and vector payload out of the proposition
being normalized by `norm_num`. -/
theorem Float32AffineReplay.ofRows_coordinate_bound
    {rows columns : ℕ}
    (input : Fin columns → FiniteFloat32Word)
    (weightRows : Fin rows → Fin columns → FiniteFloat32Word)
    (bias output : Fin rows → FiniteFloat32Word)
    (localError coordinateError : ℚ) (row : Fin rows)
    (hrow :
      |(output row).toRat -
        ((bias row).toRat +
          ∑ column, (weightRows row column).toRat * (input column).toRat)| ≤
        coordinateError) :
    |((Float32AffineReplay.ofRows input weightRows bias output localError).output row).toRat -
        (Float32AffineReplay.ofRows input weightRows bias output localError).idealOutputRat row| ≤
      coordinateError := by
  rw [Float32AffineReplay.ofRows_idealOutputRat]
  simpa [Float32AffineReplay.ofRows] using hrow

/-- Exact rational entrywise one-norm of the discrepancy between the observed
binary32 output and the decoded-real affine map. -/
def Float32AffineReplay.totalAbsoluteErrorRat
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns) : ℚ :=
  ∑ row, |(replay.output row).toRat - replay.idealOutputRat row|

/-- Propositional contract mirrored by the executable checker. -/
def Float32AffineReplay.Valid
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns) : Prop :=
  0 < rows ∧ 0 < columns ∧ 0 ≤ replay.localError ∧
    replay.totalAbsoluteErrorRat ≤ replay.localError

/-- Check nonempty dimensions, a nonnegative rational budget, and the complete
exact-rational affine discrepancy. -/
def Float32AffineReplay.check
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns) : Bool :=
  decide (0 < rows ∧ 0 < columns ∧ 0 ≤ replay.localError ∧
    replay.totalAbsoluteErrorRat ≤ replay.localError)

theorem Float32AffineReplay.check_eq_true_iff
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns) :
    replay.check = true ↔ replay.Valid := by
  simp [Float32AffineReplay.check, Float32AffineReplay.Valid]

/-- Assemble an affine replay certificate from independently checked output
coordinates.  Generated certificates use this theorem to keep exact dyadic
dot products small enough for the kernel to audit one row at a time. -/
theorem Float32AffineReplay.check_of_coordinate_bounds
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns)
    (coordinateBudget : Fin rows → ℚ)
    (hrows : 0 < rows) (hcolumns : 0 < columns)
    (hbudget : 0 ≤ replay.localError)
    (hcoordinate : ∀ row,
      |(replay.output row).toRat - replay.idealOutputRat row| ≤
        coordinateBudget row)
    (htotal : ∑ row, coordinateBudget row ≤ replay.localError) :
    replay.check = true := by
  apply replay.check_eq_true_iff.mpr
  refine ⟨hrows, hcolumns, hbudget, ?_⟩
  exact (Finset.sum_le_sum fun row _ ↦ hcoordinate row).trans htotal

/-- Every output-coordinate discrepancy is bounded by the accepted replay's
entrywise aggregate budget.  This is the reusable bridge from an already
checked affine invocation to a later coordinatewise runtime stage. -/
theorem Float32AffineReplay.coordinateAbsoluteErrorRat_le_localError
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns)
    (hcheck : replay.check = true) (row : Fin rows) :
    |(replay.output row).toRat - replay.idealOutputRat row| ≤
      replay.localError := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun index : Fin rows ↦
      |(replay.output index).toRat - replay.idealOutputRat index|)
    (fun index _ ↦ abs_nonneg _)
    (Finset.mem_univ row)
  have hterm :
      |(replay.output row).toRat - replay.idealOutputRat row| ≤
        replay.totalAbsoluteErrorRat := by
    simpa [Float32AffineReplay.totalAbsoluteErrorRat] using hsingle
  exact hterm.trans hvalid.2.2.2

/-- The ideal affine coordinate lies within the observed coordinate's
absolute magnitude plus the replay's accepted aggregate error budget. -/
theorem Float32AffineReplay.idealOutputRat_abs_le_output_abs_add_localError
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns)
    (hcheck : replay.check = true) (row : Fin rows) :
    |replay.idealOutputRat row| ≤
      |(replay.output row).toRat| + replay.localError := by
  calc
    |replay.idealOutputRat row| =
        |(replay.output row).toRat -
          ((replay.output row).toRat - replay.idealOutputRat row)| := by
      ring_nf
    _ ≤ |(replay.output row).toRat| +
        |(replay.output row).toRat - replay.idealOutputRat row| :=
      abs_sub _ _
    _ ≤ |(replay.output row).toRat| + replay.localError := by
      gcongr
      exact replay.coordinateAbsoluteErrorRat_le_localError hcheck row

/-- Decoded runtime input as a Euclidean vector. -/
def Float32AffineReplay.decodedInput
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns) :
    EuclideanSpace ℝ (Fin columns) :=
  WithLp.toLp 2 fun column ↦ (replay.input column).toReal

/-- Decoded observed runtime output as a Euclidean vector. -/
def Float32AffineReplay.decodedOutput
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns) :
    EuclideanSpace ℝ (Fin rows) :=
  WithLp.toLp 2 fun row ↦ (replay.output row).toReal

/-- The declared exact-real affine map using the row-major decoded weight and
decoded bias. -/
def Float32AffineReplay.idealAffine
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns)
    (value : EuclideanSpace ℝ (Fin columns)) : EuclideanSpace ℝ (Fin rows) :=
  WithLp.toLp 2 fun row ↦
    (replay.bias row).toReal +
      ∑ column,
        (replay.weight (rowMajorIndex rows columns row column)).toReal *
          value column

theorem Float32AffineReplay.totalAbsoluteErrorReal_eq
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns) :
    (∑ row,
      |replay.decodedOutput row - replay.idealAffine replay.decodedInput row|) =
        (replay.totalAbsoluteErrorRat : ℝ) := by
  simp [Float32AffineReplay.decodedOutput, Float32AffineReplay.idealAffine,
    Float32AffineReplay.decodedInput, Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, FiniteFloat32Word.toReal,
    Rat.cast_sum, Rat.cast_abs]

/-- An accepted replay bounds the Euclidean discrepancy between the observed
output and the exact decoded-real affine result. -/
theorem Float32AffineReplay.sound
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns)
    (hcheck : replay.check = true) :
    ‖replay.decodedOutput - replay.idealAffine replay.decodedInput‖ ≤
      (replay.localError : ℝ) := by
  have hvalid := replay.check_eq_true_iff.mp hcheck
  calc
    ‖replay.decodedOutput - replay.idealAffine replay.decodedInput‖ ≤
        ∑ row,
          |replay.decodedOutput row -
            replay.idealAffine replay.decodedInput row| :=
      euclidean_norm_le_entrywiseL1 _
    _ = (replay.totalAbsoluteErrorRat : ℝ) :=
      replay.totalAbsoluteErrorReal_eq
    _ ≤ (replay.localError : ℝ) := by
      exact_mod_cast hvalid.2.2.2

/-- The exact binary32 replay discharges the generic local-evaluation-error
interface used by the compositional finite-precision recurrence. -/
theorem Float32AffineReplay.toLocalEvaluationErrorCertificate
    {rows columns : ℕ} (replay : Float32AffineReplay rows columns)
    (hcheck : replay.check = true) :
    LocalEvaluationErrorCertificate replay.idealAffine replay.decodedInput
      replay.decodedOutput (replay.localError : ℝ) := by
  refine
    { localError_nonneg := ?_
      output_error_le := replay.sound hcheck }
  exact_mod_cast (replay.check_eq_true_iff.mp hcheck).2.2.1

/-- A nonempty collection of affine invocations sharing dimensions.  Generated
proof files may share weight and bias definitions between the entries. -/
structure Float32AffineReplayBatch (rows columns : ℕ) where
  expectedCount : ℕ
  entries : List (Float32AffineReplay rows columns)

def Float32AffineReplayBatch.Valid
    {rows columns : ℕ} (batch : Float32AffineReplayBatch rows columns) : Prop :=
  0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount ∧
    ∀ replay ∈ batch.entries, replay.Valid

def Float32AffineReplayBatch.check
    {rows columns : ℕ} (batch : Float32AffineReplayBatch rows columns) : Bool :=
  decide (0 < batch.expectedCount ∧
    batch.entries.length = batch.expectedCount) &&
    batch.entries.all Float32AffineReplay.check

theorem Float32AffineReplayBatch.check_eq_true_iff
    {rows columns : ℕ} (batch : Float32AffineReplayBatch rows columns) :
    batch.check = true ↔ batch.Valid := by
  simp [Float32AffineReplayBatch.check, Float32AffineReplayBatch.Valid,
    List.all_eq_true, Float32AffineReplay.check_eq_true_iff, and_assoc]

theorem Float32AffineReplayBatch.sound_of_mem
    {rows columns : ℕ} (batch : Float32AffineReplayBatch rows columns)
    (hcheck : batch.check = true) {replay : Float32AffineReplay rows columns}
    (hmem : replay ∈ batch.entries) :
    ‖replay.decodedOutput - replay.idealAffine replay.decodedInput‖ ≤
      (replay.localError : ℝ) := by
  have hvalid := (batch.check_eq_true_iff.mp hcheck).2.2 replay hmem
  exact replay.sound <| replay.check_eq_true_iff.mpr hvalid

def Float32AffineReplayBatch.totalObservedError
    {rows columns : ℕ} (batch : Float32AffineReplayBatch rows columns) : ℝ :=
  (batch.entries.map fun replay ↦
    ‖replay.decodedOutput - replay.idealAffine replay.decodedInput‖).sum

def Float32AffineReplayBatch.totalCertifiedError
    {rows columns : ℕ} (batch : Float32AffineReplayBatch rows columns) : ℝ :=
  (batch.entries.map fun replay ↦ (replay.localError : ℝ)).sum

theorem Float32AffineReplayBatch.totalObservedError_le
    {rows columns : ℕ} (batch : Float32AffineReplayBatch rows columns)
    (hcheck : batch.check = true) :
    batch.totalObservedError ≤ batch.totalCertifiedError := by
  apply List.sum_le_sum
  intro replay hmem
  exact batch.sound_of_mem hcheck hmem

/-! ## Positive and corrupt fixtures -/

def positiveTwo : FiniteFloat32Word where
  word := 1073741824
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveThree : FiniteFloat32Word where
  word := 1077936128
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveFour : FiniteFloat32Word where
  word := 1082130432
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveFive : FiniteFloat32Word where
  word := 1084227584
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveFifteen : FiniteFloat32Word where
  word := 1097859072
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def positiveSixteen : FiniteFloat32Word where
  word := 1098907648
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

/-- `[3,4] * [1,2] + 5 = 16` is exactly representable and needs no local
error budget. -/
def exactAffineReplay : Float32AffineReplay 1 2 where
  input := ![positiveOne, positiveTwo]
  weight := ![positiveThree, positiveFour]
  bias := ![positiveFive]
  output := ![positiveSixteen]
  localError := 0

theorem exactAffineReplay_is_accepted : exactAffineReplay.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, exactAffineReplay,
    positiveOne, positiveTwo, positiveThree, positiveFour, positiveFive,
    positiveSixteen, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa, rowMajorIndex]

theorem exactAffineReplay_has_zero_local_error :
    ‖exactAffineReplay.decodedOutput -
      exactAffineReplay.idealAffine exactAffineReplay.decodedInput‖ ≤ 0 :=
  by
    simpa [exactAffineReplay] using
      exactAffineReplay.sound exactAffineReplay_is_accepted

def exactAffineReplayBatch : Float32AffineReplayBatch 1 2 where
  expectedCount := 1
  entries := [exactAffineReplay]

theorem exactAffineReplayBatch_is_accepted :
    exactAffineReplayBatch.check = true := by
  simp [exactAffineReplayBatch, Float32AffineReplayBatch.check,
    exactAffineReplay_is_accepted]

theorem exactAffineReplayBatch_total_error_is_bounded :
    exactAffineReplayBatch.totalObservedError ≤
      exactAffineReplayBatch.totalCertifiedError :=
  exactAffineReplayBatch.totalObservedError_le exactAffineReplayBatch_is_accepted

/-- The same affine map with observed output `15` is valid under an exact unit
local-error budget.  This exercises nonzero error transport rather than only
exact arithmetic. -/
def boundedAffineReplay : Float32AffineReplay 1 2 where
  input := ![positiveOne, positiveTwo]
  weight := ![positiveThree, positiveFour]
  bias := ![positiveFive]
  output := ![positiveFifteen]
  localError := 1

theorem boundedAffineReplay_is_accepted : boundedAffineReplay.check = true := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, boundedAffineReplay,
    positiveOne, positiveTwo, positiveThree, positiveFour, positiveFive,
    positiveFifteen, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa, rowMajorIndex]

theorem boundedAffineReplay_has_unit_local_error :
    ‖boundedAffineReplay.decodedOutput -
      boundedAffineReplay.idealAffine boundedAffineReplay.decodedInput‖ ≤ 1 :=
  by
    simpa [boundedAffineReplay] using
      boundedAffineReplay.sound boundedAffineReplay_is_accepted

/-- Substituting `15` for the exact output `16` while retaining a zero budget
is rejected. -/
def corruptAffineReplay : Float32AffineReplay 1 2 where
  input := ![positiveOne, positiveTwo]
  weight := ![positiveThree, positiveFour]
  bias := ![positiveFive]
  output := ![positiveFifteen]
  localError := 0

theorem corruptAffineReplay_is_rejected : corruptAffineReplay.check = false := by
  norm_num [Float32AffineReplay.check, Float32AffineReplay.Valid,
    Float32AffineReplay.totalAbsoluteErrorRat,
    Float32AffineReplay.idealOutputRat, corruptAffineReplay,
    positiveOne, positiveTwo, positiveThree, positiveFour, positiveFive,
    positiveFifteen, FiniteFloat32Word.toRat, float32Exponent,
    float32Mantissa, rowMajorIndex]

def corruptAffineReplayBatch : Float32AffineReplayBatch 1 2 where
  expectedCount := 2
  entries := [exactAffineReplay, corruptAffineReplay]

theorem corruptAffineReplayBatch_is_rejected :
    corruptAffineReplayBatch.check = false := by
  simp [corruptAffineReplayBatch, Float32AffineReplayBatch.check,
    exactAffineReplay_is_accepted, corruptAffineReplay_is_rejected]

#print axioms Float32AffineReplay.check_eq_true_iff
#print axioms Float32AffineReplay.check_of_coordinate_bounds
#print axioms Float32AffineReplay.coordinateAbsoluteErrorRat_le_localError
#print axioms Float32AffineReplay.idealOutputRat_abs_le_output_abs_add_localError
#print axioms Float32AffineReplay.ofRows_idealOutputRat
#print axioms Float32AffineReplay.ofRows_coordinate_bound
#print axioms Float32AffineReplay.sound
#print axioms Float32AffineReplay.toLocalEvaluationErrorCertificate
#print axioms Float32AffineReplayBatch.check_eq_true_iff
#print axioms Float32AffineReplayBatch.totalObservedError_le
#print axioms exactAffineReplay_is_accepted
#print axioms boundedAffineReplay_is_accepted
#print axioms corruptAffineReplay_is_rejected

end

end Float32AffineReplayCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
