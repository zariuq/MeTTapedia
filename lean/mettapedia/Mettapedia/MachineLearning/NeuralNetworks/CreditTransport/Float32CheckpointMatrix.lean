import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteMatrixOperatorBounds
import Mathlib.Tactic

/-!
# Exact finite-float checkpoint matrices

Checkpoint tensors store IEEE-754 binary32 words.  This file decodes every
finite word exactly into `ℝ`, fixes the row-major layout used by a linear layer
with shape `[output, input]`, and connects the decoded matrix to the auditable
entrywise operator-norm bound.

The bridge deliberately excludes exponent field `255`: infinities and NaNs
cannot inhabit `FiniteFloat32Word`.  No decimal rendering or floating-point
spectral routine enters the certificate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32CheckpointMatrix

noncomputable section

open scoped Matrix.Norms.L2Operator
open FiniteMatrixOperatorBounds

/-- Binary32 exponent field extracted from an unsigned 32-bit word. -/
def float32Exponent (word : ℕ) : ℕ :=
  word / 8388608 % 256

/-- Binary32 fraction field extracted from an unsigned 32-bit word. -/
def float32Mantissa (word : ℕ) : ℕ :=
  word % 8388608

/-- A raw binary32 word known to denote a finite value. -/
structure FiniteFloat32Word where
  word : ℕ
  word_lt_two_pow_32 : word < 4294967296
  exponent_lt_255 : float32Exponent word < 255
  deriving Repr

/-- Exact rational value of a finite IEEE-754 binary32 word.  Every finite
binary32 number is dyadic, so this canonical decoder loses no information.
Normal significands carry the implicit leading bit; subnormals use exponent
`-149`. -/
def FiniteFloat32Word.toRat (value : FiniteFloat32Word) : ℚ :=
  let exponent := float32Exponent value.word
  let mantissa := float32Mantissa value.word
  let significand := if exponent = 0 then mantissa else 8388608 + mantissa
  let magnitude : ℚ :=
    if exponent = 0 then
      significand / (2 : ℚ) ^ 149
    else if exponent < 150 then
      significand / (2 : ℚ) ^ (150 - exponent)
    else
      significand * (2 : ℚ) ^ (exponent - 150)
  if value.word < 2147483648 then magnitude else -magnitude

/-- Exact real value of a finite IEEE-754 binary32 word. -/
def FiniteFloat32Word.toReal (value : FiniteFloat32Word) : ℝ :=
  value.toRat

/-- The real decoder is exactly the cast of the canonical dyadic rational. -/
theorem FiniteFloat32Word.cast_toRat (value : FiniteFloat32Word) :
    (value.toRat : ℝ) = value.toReal := rfl

/-- Flat row-major index for a tensor with shape `[rows, columns]`. -/
def rowMajorIndex (rows columns : ℕ)
    (row : Fin rows) (column : Fin columns) : Fin (rows * columns) :=
  ⟨row.val * columns + column.val, by
    have hcolumn : row.val * columns + column.val <
        row.val * columns + columns :=
      Nat.add_lt_add_left column.isLt _
    have hrow : (row.val + 1) * columns ≤ rows * columns :=
      Nat.mul_le_mul_right columns (Nat.succ_le_iff.mpr row.isLt)
    rw [Nat.add_mul, one_mul] at hrow
    exact hcolumn.trans_le hrow⟩

/-- Flatten a matrix-shaped family using the same `[row, column]` convention
as `rowMajorIndex`.  Keeping this conversion abstract lets generated replay
proofs reason about one matrix row without unfolding every other row. -/
def rowMajorFlatten {rows columns : ℕ} {α : Type*}
    (entries : Fin rows → Fin columns → α) : Fin (rows * columns) → α :=
  fun index ↦
    let coordinate := finProdFinEquiv.symm index
    entries coordinate.1 coordinate.2

@[simp]
theorem rowMajorFlatten_rowMajorIndex
    {rows columns : ℕ} {α : Type*}
    (entries : Fin rows → Fin columns → α)
    (row : Fin rows) (column : Fin columns) :
    rowMajorFlatten entries (rowMajorIndex rows columns row column) =
      entries row column := by
  have hindex : rowMajorIndex rows columns row column =
      finProdFinEquiv (row, column) := by
    apply Fin.ext
    simp [rowMajorIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [hindex]
  simp [rowMajorFlatten]

/-- Matrix view of a flat row-major tensor. -/
def rowMajorMatrix {rows columns : ℕ}
    (entries : Fin (rows * columns) → ℝ) : Matrix (Fin rows) (Fin columns) ℝ :=
  fun row column ↦ entries (rowMajorIndex rows columns row column)

/-- Exact real matrix decoded from a flat binary32 tensor. -/
def decodedRowMajorMatrix {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    Matrix (Fin rows) (Fin columns) ℝ :=
  rowMajorMatrix fun index ↦ (entries index).toReal

/-- The decoded checkpoint matrix inherits the finite entrywise Euclidean
operator-norm certificate. -/
theorem decodedRowMajorMatrix_operatorNorm_le_entrywiseL1
    {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    ‖decodedRowMajorMatrix entries‖ ≤
      entrywiseL1Bound (decodedRowMajorMatrix entries) :=
  l2OperatorNorm_le_entrywiseL1 _

/-! ## Positive and negative fixtures -/

def positiveOne : FiniteFloat32Word where
  word := 1065353216
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def negativeHalf : FiniteFloat32Word where
  word := 3204448256
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

def minimumPositiveSubnormal : FiniteFloat32Word where
  word := 1
  word_lt_two_pow_32 := by norm_num
  exponent_lt_255 := by norm_num [float32Exponent]

theorem positiveOne_toReal : positiveOne.toReal = 1 := by
  norm_num [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat, positiveOne,
    float32Exponent, float32Mantissa]

theorem negativeHalf_toReal : negativeHalf.toReal = -(1 / 2 : ℝ) := by
  norm_num [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat, negativeHalf,
    float32Exponent, float32Mantissa]

theorem minimumPositiveSubnormal_toReal :
    minimumPositiveSubnormal.toReal = 1 / (2 : ℝ) ^ 149 := by
  norm_num [FiniteFloat32Word.toReal, FiniteFloat32Word.toRat,
    minimumPositiveSubnormal, float32Exponent, float32Mantissa]

theorem positiveOne_toRat : positiveOne.toRat = 1 := by
  norm_num [FiniteFloat32Word.toRat, positiveOne, float32Exponent,
    float32Mantissa]

theorem negativeHalf_toRat : negativeHalf.toRat = -(1 / 2 : ℚ) := by
  norm_num [FiniteFloat32Word.toRat, negativeHalf, float32Exponent,
    float32Mantissa]

/-- The positive-infinity word is rejected by the finite-word boundary. -/
theorem positiveInfinity_is_not_finite :
    ¬ float32Exponent 2139095040 < 255 := by
  norm_num [float32Exponent]

/-- Row-major and column-major interpretations differ on an asymmetric
`2 × 2` payload, so layout cannot be inferred from shape alone. -/
theorem rowMajor_transpose_layouts_differ :
    rowMajorMatrix (rows := 2) (columns := 2)
        (fun index ↦ (index.val + 1 : ℕ)) 0 1 ≠
      rowMajorMatrix (rows := 2) (columns := 2)
        (fun index ↦ (index.val + 1 : ℕ)) 1 0 := by
  norm_num [rowMajorMatrix, rowMajorIndex]

#print axioms decodedRowMajorMatrix_operatorNorm_le_entrywiseL1
#print axioms rowMajorFlatten_rowMajorIndex
#print axioms FiniteFloat32Word.cast_toRat
#print axioms positiveInfinity_is_not_finite
#print axioms rowMajor_transpose_layouts_differ

end

end Float32CheckpointMatrix

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
