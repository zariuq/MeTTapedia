import Mathlib

/-!
# Hadamard Lie-group continual updates

Cao and Wu, *Orthogonal Low-rank Adaptation in Lie Groups for Continual
Learning of Large Language Models* (arXiv:2509.06100), model a parameter
tensor with no zero entries as an Abelian Lie group under the Hadamard
product.  A Lie-algebra increment `δ` acts by the entrywise update

`w ↦ w * exp δ`.

This file isolates the finite algebra of that construction:

* exact updates preserve nonzero entries and their sign component;
* composing increments is addition in the Lie algebra;
* negating an increment gives an exact inverse update;
* the first-order multiplier `1 + δ` can leave the group at `δ = -1`;
* the second-order multiplier `1 + δ + δ²/2` is always positive.

The source's orthogonality loss is written on the uncentered factors
`exp(Δᵢ) exp(Δⱼ)ᵀ`.  Every entry of this product is strictly positive when
the shared dimension is nonempty, so its Frobenius-square cannot be zero.
This is a structural boundary, not an optimization failure.  Orthogonality
can instead be imposed on the Lie-algebra increments themselves (as the
explicit two-coordinate fixture demonstrates) or on centered factors such as
`exp δ - 1`.

These results concern exact real arithmetic and finite tensors.  They do not
establish benchmark retention, low-rank expressivity, or floating-point
stability.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace HadamardLieGroupUpdate

noncomputable section

/-- A finite or infinite tensor whose every coordinate is invertible under
real multiplication. -/
structure HadamardParameter (Index : Type*) where
  value : Index → ℝ
  nonzero : ∀ index, value index ≠ 0

namespace HadamardParameter

variable {Index : Type*}

@[ext]
theorem ext
    {first second : HadamardParameter Index}
    (equal : ∀ index, first.value index = second.value index) :
    first = second := by
  cases first with
  | mk firstValue firstNonzero =>
      cases second with
      | mk secondValue secondNonzero =>
          congr
          exact funext equal

/-- Entrywise exponential action of a Lie-algebra increment. -/
def update
    (parameter : HadamardParameter Index)
    (increment : Index → ℝ) :
    HadamardParameter Index where
  value index :=
    parameter.value index * Real.exp (increment index)
  nonzero index :=
    mul_ne_zero
      (parameter.nonzero index)
      (Real.exp_ne_zero _)

@[simp]
theorem update_value
    (parameter : HadamardParameter Index)
    (increment : Index → ℝ) (index : Index) :
    (update parameter increment).value index =
      parameter.value index * Real.exp (increment index) := rfl

/-- Zero in the Lie algebra acts as the identity. -/
@[simp]
theorem update_zero (parameter : HadamardParameter Index) :
    update parameter 0 = parameter := by
  ext index
  simp

/-- Successive exact updates add their Lie-algebra increments. -/
@[simp]
theorem update_add
    (parameter : HadamardParameter Index)
    (first second : Index → ℝ) :
    update (update parameter first) second =
      update parameter (first + second) := by
  ext index
  simp [Real.exp_add]
  ring

/-- The negated increment exactly reverses an update. -/
@[simp]
theorem update_neg
    (parameter : HadamardParameter Index)
    (increment : Index → ℝ) :
    update (update parameter increment) (-increment) =
      parameter := by
  rw [update_add]
  simp

/-- Exact exponential updates stay in the same positive sign component. -/
theorem update_pos_iff
    (parameter : HadamardParameter Index)
    (increment : Index → ℝ) (index : Index) :
    0 < (update parameter increment).value index ↔
      0 < parameter.value index := by
  simp only [update_value]
  exact mul_pos_iff_of_pos_right (Real.exp_pos _)

/-- Exact exponential updates stay in the same negative sign component. -/
theorem update_neg_iff
    (parameter : HadamardParameter Index)
    (increment : Index → ℝ) (index : Index) :
    (update parameter increment).value index < 0 ↔
      parameter.value index < 0 := by
  simp only [update_value]
  constructor
  · intro product_negative
    by_contra parameter_not_negative
    have parameter_nonnegative :
        0 ≤ parameter.value index :=
      le_of_not_gt parameter_not_negative
    exact
      (not_lt_of_ge
        (mul_nonneg parameter_nonnegative
          (le_of_lt (Real.exp_pos _))))
        product_negative
  · intro parameter_negative
    exact
      mul_neg_of_neg_of_pos
        parameter_negative (Real.exp_pos _)

end HadamardParameter

/-- First-order Taylor multiplier used in the source approximation. -/
def firstOrderMultiplier (increment : ℝ) : ℝ :=
  1 + increment

/-- Second-order Taylor multiplier used in the source approximation. -/
def secondOrderMultiplier (increment : ℝ) : ℝ :=
  1 + increment + increment ^ 2 / 2

/-- Raw entrywise first-order update, which is not intrinsically group-valued. -/
def firstOrderValue (parameter increment : ℝ) : ℝ :=
  parameter * firstOrderMultiplier increment

/-- The first-order truncation can hit zero and leave the Hadamard group. -/
theorem firstOrderMultiplier_neg_one :
    firstOrderMultiplier (-1) = 0 := by
  norm_num [firstOrderMultiplier]

/-- Consequently every nonzero scalar parameter is destroyed at increment
`-1` by the first-order approximation. -/
theorem firstOrderValue_neg_one
    (parameter : ℝ) :
    firstOrderValue parameter (-1) = 0 := by
  simp [firstOrderValue, firstOrderMultiplier]

/-- The scalar second-order Taylor multiplier is globally positive. -/
theorem secondOrderMultiplier_pos (increment : ℝ) :
    0 < secondOrderMultiplier increment := by
  have square_nonnegative :
      0 ≤ (increment + 1) ^ 2 :=
    sq_nonneg _
  unfold secondOrderMultiplier
  nlinarith

/-- Therefore the second-order truncation preserves every nonzero scalar
entry. -/
theorem mul_secondOrderMultiplier_ne_zero
    {parameter increment : ℝ}
    (parameter_ne : parameter ≠ 0) :
    parameter * secondOrderMultiplier increment ≠ 0 :=
  mul_ne_zero
    parameter_ne
    (ne_of_gt (secondOrderMultiplier_pos increment))

section OrthogonalityBoundary

variable {Row Column : Type*}
variable [Fintype Column] [Nonempty Column]

/-- Entrywise exponential of a matrix-valued Lie-algebra increment. -/
def expMatrix
    (matrix : Matrix Row Column ℝ) :
    Matrix Row Column ℝ :=
  fun row column => Real.exp (matrix row column)

/-- Every entry of `exp(Δ₁) exp(Δ₂)ᵀ` is strictly positive. -/
theorem expMatrix_mul_transpose_entry_pos
    (first second : Matrix Row Column ℝ)
    (firstRow secondRow : Row) :
    0 <
      (expMatrix first * (expMatrix second).transpose)
        firstRow secondRow := by
  rw [Matrix.mul_apply]
  apply Finset.sum_pos
  · intro column _
    exact
      mul_pos
        (Real.exp_pos _)
        (Real.exp_pos _)
  · exact Finset.univ_nonempty

/-- In particular, the product in the source orthogonality term is never the
zero matrix when a row and a shared column exist. -/
theorem expMatrix_mul_transpose_ne_zero
    (first second : Matrix Row Column ℝ)
    (row : Row) :
    expMatrix first * (expMatrix second).transpose ≠ 0 := by
  intro equal
  have entry := congr_fun (congr_fun equal row) row
  have positive :=
    expMatrix_mul_transpose_entry_pos
      first second row row
  simp at entry
  linarith

variable [Fintype Row] [Nonempty Row]

/-- Frobenius norm squared, kept explicit to avoid changing the ambient
matrix norm instance. -/
def frobeniusSquared
    (matrix : Matrix Row Row ℝ) : ℝ :=
  ∑ firstRow, ∑ secondRow, matrix firstRow secondRow ^ 2

/-- The source's exact uncentered exponentiated cross-task product has
strictly positive Frobenius square. -/
theorem frobeniusSquared_expMatrix_mul_transpose_pos
    (first second : Matrix Row Column ℝ) :
    0 <
      frobeniusSquared
        (expMatrix first * (expMatrix second).transpose) := by
  unfold frobeniusSquared
  apply Finset.sum_pos
  · intro firstRow _
    apply Finset.sum_pos
    · intro secondRow _
      exact
        sq_pos_of_pos
          (expMatrix_mul_transpose_entry_pos
            first second firstRow secondRow)
    · exact Finset.univ_nonempty
  · exact Finset.univ_nonempty

/-- Hence exact zero orthogonality of the uncentered exponentiated factors is
unattainable. -/
theorem expMatrix_frobeniusSquared_ne_zero
    (first second : Matrix Row Column ℝ) :
    frobeniusSquared
        (expMatrix first * (expMatrix second).transpose) ≠
      0 :=
  ne_of_gt
    (frobeniusSquared_expMatrix_mul_transpose_pos
      first second)

end OrthogonalityBoundary

section LieAlgebraFixture

/-- Euclidean inner product of two finite Lie-algebra increments. -/
def incrementInner
    {Index : Type*} [Fintype Index]
    (first second : Index → ℝ) : ℝ :=
  ∑ index, first index * second index

def firstCoordinate : Fin 2 → ℝ
  | 0 => 1
  | 1 => 0

def secondCoordinate : Fin 2 → ℝ
  | 0 => 0
  | 1 => 1

/-- Positive fixture: distinct coordinate increments are exactly orthogonal
in the Lie algebra. -/
theorem coordinateIncrements_are_orthogonal :
    incrementInner firstCoordinate secondCoordinate = 0 := by
  norm_num [incrementInner, firstCoordinate, secondCoordinate,
    Fin.sum_univ_two]

/-- Negative counterpart: exponentiating those same increments produces
strictly positive, hence nonorthogonal, factors. -/
theorem exponentiatedCoordinateIncrements_not_orthogonal :
    0 <
      ∑ index : Fin 2,
        Real.exp (firstCoordinate index) *
          Real.exp (secondCoordinate index) := by
  apply Finset.sum_pos
  · intro index _
    exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
  · exact Finset.univ_nonempty

end LieAlgebraFixture

end

end HadamardLieGroupUpdate

end Mettapedia.MachineLearning.ContinualLearning

#print axioms
  Mettapedia.MachineLearning.ContinualLearning.HadamardLieGroupUpdate.HadamardParameter.update_add
#print axioms
  Mettapedia.MachineLearning.ContinualLearning.HadamardLieGroupUpdate.frobeniusSquared_expMatrix_mul_transpose_pos
#print axioms
  Mettapedia.MachineLearning.ContinualLearning.HadamardLieGroupUpdate.coordinateIncrements_are_orthogonal
