import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Auditable finite-matrix operator bounds

Neural checkpoints store affine weights entrywise, while the compositional
credit-transport theory consumes operator norms.  This file supplies a
conservative bridge for finite real matrices: the Euclidean operator norm is
bounded by the sum of the absolute values of all entries.  The bound is not
tight, but every premise is reducible to finite arithmetic and therefore
suited to independently checked checkpoint certificates.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FiniteMatrixOperatorBounds

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

variable {Rows Cols : Type*}
  [Fintype Rows] [Fintype Cols]
  [DecidableEq Rows] [DecidableEq Cols]

/-- Sum of entry magnitudes, used as a conservative Euclidean operator-norm
certificate. -/
def entrywiseL1Bound (matrix : Matrix Rows Cols ℝ) : ℝ :=
  ∑ row, ∑ column, |matrix row column|

omit [DecidableEq Rows] [DecidableEq Cols] in
theorem entrywiseL1Bound_nonneg (matrix : Matrix Rows Cols ℝ) :
    0 ≤ entrywiseL1Bound matrix := by
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The Euclidean norm of a finite vector is at most its entrywise one-norm. -/
theorem euclidean_norm_le_entrywiseL1 (vector : EuclideanSpace ℝ Rows) :
    ‖vector‖ ≤ ∑ row, |vector row| := by
  let singleVector (row : Rows) : EuclideanSpace ℝ Rows :=
    PiLp.single 2 row (vector row)
  have hrepresentation : vector = ∑ row, singleVector row := by
    ext row
    simp [singleVector]
  calc
    ‖vector‖ = ‖∑ row, singleVector row‖ := congrArg norm hrepresentation
    _ ≤ ∑ row, ‖singleVector row‖ := by
      exact norm_sum_le Finset.univ singleVector
    _ = ∑ row, |vector row| := by
      simp [singleVector, Real.norm_eq_abs]

/-- A finite matrix's Euclidean operator norm is bounded by its entrywise
one-norm. -/
theorem l2OperatorNorm_le_entrywiseL1 (matrix : Matrix Rows Cols ℝ) :
    ‖matrix‖ ≤ entrywiseL1Bound matrix := by
  apply ContinuousLinearMap.opNorm_le_bound _ (entrywiseL1Bound_nonneg matrix)
  intro vector
  change
    ‖(EuclideanSpace.equiv Rows ℝ).symm (Matrix.mulVec matrix vector)‖ ≤
      entrywiseL1Bound matrix * ‖vector‖
  calc
    ‖(EuclideanSpace.equiv Rows ℝ).symm (Matrix.mulVec matrix vector)‖ ≤
        ∑ row, |Matrix.mulVec matrix vector row| :=
      euclidean_norm_le_entrywiseL1 _
    _ ≤ ∑ row, ∑ column,
        |matrix row column| * ‖vector‖ := by
      gcongr with row
      rw [Matrix.mulVec, dotProduct]
      calc
        |∑ column, matrix row column * vector column| ≤
            ∑ column, |matrix row column * vector column| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ column, |matrix row column| * |vector column| := by
          simp only [abs_mul]
        _ ≤ ∑ column, |matrix row column| * ‖vector‖ := by
          gcongr with column
          exact PiLp.norm_apply_le vector column
    _ = entrywiseL1Bound matrix * ‖vector‖ := by
      simp only [entrywiseL1Bound, Finset.sum_mul]

/-! ## Positive and negative fixtures -/

/-- The bound is exact for a one-dimensional nonnegative weight. -/
theorem singleton_entrywiseL1Bound
    (weight : ℝ) (hweight : 0 ≤ weight) :
    entrywiseL1Bound (fun _ : Unit ↦ fun _ : Unit ↦ weight) = weight := by
  simp [entrywiseL1Bound, abs_of_nonneg hweight]

/-- Taking only the largest entry is unsound even for a `2 × 2` layer: the
all-ones matrix has operator norm two while every entry has magnitude one. -/
theorem maximumEntry_alone_fails :
    ¬ ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (fun _ _ ↦ (1 : ℝ)))‖ ≤ 1 := by
  intro h
  let vector : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 fun _ : Fin 2 ↦ (1 : ℝ)
  have happly := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
    (fun _ _ ↦ (1 : ℝ))).le_opNorm vector
  have hbound :
      ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (fun _ _ ↦ (1 : ℝ))) vector‖ ≤ ‖vector‖ := by
    calc
      ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
          (fun _ _ ↦ (1 : ℝ))) vector‖ ≤
          ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            (fun _ _ ↦ (1 : ℝ)))‖ * ‖vector‖ := happly
      _ ≤ 1 * ‖vector‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg vector)
      _ = ‖vector‖ := one_mul _
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hbound
  norm_num [vector, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct,
    EuclideanSpace.real_norm_sq_eq] at hsquare

#print axioms l2OperatorNorm_le_entrywiseL1
#print axioms maximumEntry_alone_fails

end

end FiniteMatrixOperatorBounds

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
