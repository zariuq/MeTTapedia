import Mettapedia.MachineLearning.ContinualLearning.FeatureCovarianceRetention
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Quantitative retention from approximate covariance residuals

Exact feature-covariance null-space methods preserve stored outputs when
`XᵀX Δ = 0`.  Practical algorithms instead use truncated singular spaces and
finite-precision projections, so their residual is only approximately zero.
This file supplies the missing finite certificate.

For one update column `d`, the exact identity

`‖X d‖₂² = d · ((XᵀX) d)`

turns an observable covariance residual into an output-drift budget.  If
every residual coordinate is bounded by `epsilon`, then

`‖X d‖₂² ≤ ‖d‖₁ epsilon`.

The theorem is extended columnwise to a complete weight update.  It requires
both the residual and update magnitude: a scalar family attains equality
with arbitrarily small covariance residual and unit output drift by scaling
the update reciprocally.  This closes the exact/approximate gap without
assuming an unmeasured spectral condition.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ApproximateCovarianceRetention

open FeatureCovarianceRetention

noncomputable section

variable {Sample Feature Output : Type*}
  [Fintype Sample] [Fintype Feature] [Fintype Output]

/-- Squared Euclidean length in finite real coordinates. -/
def squaredL2 {Index : Type*} [Fintype Index]
    (vector : Index → ℝ) : ℝ :=
  vector ⬝ᵥ vector

/-- Entrywise one-norm used by the observable residual certificate. -/
def l1Norm {Index : Type*} [Fintype Index]
    (vector : Index → ℝ) : ℝ :=
  ∑ index, |vector index|

/-- A coordinatewise infinity-norm upper certificate. -/
def HasLInfBound {Index : Type*}
    (bound : ℝ) (vector : Index → ℝ) : Prop :=
  ∀ index, |vector index| ≤ bound

/-- Exact covariance energy identity: output drift squared equals the update
paired with its covariance residual. -/
theorem featureDriftSq_eq_update_dot_covarianceResidual
    (features : Matrix Sample Feature ℝ)
    (direction : Feature → ℝ) :
    squaredL2 (features.mulVec direction) =
      direction ⬝ᵥ
        (uncenteredCovariance features).mulVec direction := by
  have vecMulEq :
      Matrix.vecMul (features.mulVec direction) features =
        features.transpose.mulVec (features.mulVec direction) := by
    simpa using
      (Matrix.vecMul_transpose features.transpose
        (features.mulVec direction))
  unfold squaredL2 uncenteredCovariance
  rw [Matrix.dotProduct_mulVec, vecMulEq, dotProduct_comm,
    Matrix.mulVec_mulVec]

/-- Elementary `l1`/coordinatewise bound for a finite dot product. -/
theorem abs_dotProduct_le_l1Norm_mul_of_linf
    (left right : Feature → ℝ) (bound : ℝ)
    (rightBound : HasLInfBound bound right) :
    |left ⬝ᵥ right| ≤ l1Norm left * bound := by
  unfold dotProduct l1Norm
  calc
    |∑ index, left index * right index| ≤
        ∑ index, |left index * right index| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ index, |left index| * |right index| := by
      apply Finset.sum_congr rfl
      intro index _
      rw [abs_mul]
    _ ≤ ∑ index, |left index| * bound := by
      apply Finset.sum_le_sum
      intro index _
      exact mul_le_mul_of_nonneg_left
        (rightBound index) (abs_nonneg _)
    _ = (∑ index, |left index|) * bound := by
      rw [Finset.sum_mul]

/-- Quantitative single-column retention theorem.  Both terms on the right
are directly observable in an executable projection trace. -/
theorem featureDriftSq_le_l1Norm_mul_linfResidual
    (features : Matrix Sample Feature ℝ)
    (direction : Feature → ℝ)
    (residualBound : ℝ)
    (bounded :
      HasLInfBound residualBound
        ((uncenteredCovariance features).mulVec direction)) :
    squaredL2 (features.mulVec direction) ≤
      l1Norm direction * residualBound := by
  rw [featureDriftSq_eq_update_dot_covarianceResidual]
  exact le_trans (le_abs_self _)
    (abs_dotProduct_le_l1Norm_mul_of_linf
      direction
      ((uncenteredCovariance features).mulVec direction)
      residualBound bounded)

/-- One column of a multi-output weight update. -/
def updateColumn
    (update : Matrix Feature Output ℝ)
    (output : Output) : Feature → ℝ :=
  fun feature => update feature output

/-- Total stored-output drift squared across every update column. -/
def totalFeatureDriftSq
    (features : Matrix Sample Feature ℝ)
    (update : Matrix Feature Output ℝ) : ℝ :=
  ∑ output,
    squaredL2 (features.mulVec (updateColumn update output))

/-- Sum of the observable per-column certificate budgets. -/
def totalCovarianceResidualBudget
    (update : Matrix Feature Output ℝ)
    (residualBound : Output → ℝ) : ℝ :=
  ∑ output, l1Norm (updateColumn update output) * residualBound output

/-- Multi-output certificate: per-column covariance-residual bounds add to a
complete stored-output drift budget. -/
theorem totalFeatureDriftSq_le_totalCovarianceResidualBudget
    (features : Matrix Sample Feature ℝ)
    (update : Matrix Feature Output ℝ)
    (residualBound : Output → ℝ)
    (bounded : ∀ output,
      HasLInfBound (residualBound output)
        ((uncenteredCovariance features).mulVec
          (updateColumn update output))) :
    totalFeatureDriftSq features update ≤
      totalCovarianceResidualBudget update residualBound := by
  unfold totalFeatureDriftSq totalCovarianceResidualBudget
  apply Finset.sum_le_sum
  intro output _
  exact featureDriftSq_le_l1Norm_mul_linfResidual
    features (updateColumn update output) (residualBound output)
      (bounded output)

/-- Exact covariance-nullity is recovered as the zero-budget endpoint of the
quantitative theorem. -/
theorem featureDriftSq_eq_zero_of_covarianceResidual_zero
    (features : Matrix Sample Feature ℝ)
    (direction : Feature → ℝ)
    (covarianceNull :
      (uncenteredCovariance features).mulVec direction = 0) :
    squaredL2 (features.mulVec direction) = 0 := by
  rw [featureDriftSq_eq_update_dot_covarianceResidual,
    covarianceNull]
  simp

/-! ## Executable tightness boundary -/

/-- The certificate can be tight: residual `1/100` and update one-norm `100`
produce unit stored-output drift.  Residual magnitude alone is therefore not
a retention budget. -/
theorem scalar_hundredfold_certificate_is_tight :
    let features : Matrix Unit Unit ℝ := fun _ _ => 1 / 100
    let direction : Unit → ℝ := fun _ => 100
    let residual :=
      (uncenteredCovariance features).mulVec direction
    residual = (fun _ => 1 / 100) ∧
      squaredL2 (features.mulVec direction) = 1 ∧
      l1Norm direction * (1 / 100) = 1 := by
  dsimp
  constructor
  · funext coordinate
    cases coordinate
    norm_num [uncenteredCovariance, Matrix.mulVec,
      Matrix.mul_apply, dotProduct]
  · constructor
    · norm_num [squaredL2, Matrix.mulVec, dotProduct]
    · norm_num [l1Norm]

/-- A zero residual budget with a nonzero residual is rejected rather than
silently interpreted as approximate retention. -/
theorem nonzeroResidual_has_no_zero_linf_certificate :
    let residual : Unit → ℝ := fun _ => 1 / 100
    ¬ HasLInfBound 0 residual := by
  dsimp [HasLInfBound]
  intro bound
  have := bound ()
  norm_num at this

#print axioms featureDriftSq_eq_update_dot_covarianceResidual
#print axioms totalFeatureDriftSq_le_totalCovarianceResidualBudget
#print axioms scalar_hundredfold_certificate_is_tight
#print axioms nonzeroResidual_has_no_zero_linf_certificate

end

end ApproximateCovarianceRetention

end Mettapedia.MachineLearning.ContinualLearning
