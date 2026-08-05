import Mettapedia.MachineLearning.ContinualLearning.StreamingLDACovariance

/-!
# Streaming regularized discriminant covariance

Khawand, Hanappe, and Steels, *Continual Learning with Deep Streaming
Regularized Discriminant Analysis* (arXiv:2309.08353), Equation (11),
interpolate a class-specific streaming QDA covariance with the pooled
streaming LDA covariance:

`Σ̄ₖ = α Σₖ + (1 - α) Σpool`, with `α ∈ [0, 1]`.

This file extends `StreamingLDACovariance` with the exact matrix geometry of
that interpolation:

* positive semidefiniteness is preserved throughout the closed coefficient
  interval;
* positive definiteness follows when either endpoint is positive definite
  and receives positive weight;
* `α = 0` recovers pooled SLDA and `α = 1` recovers class-specific SQDA;
* the subsequent identity ridge from Equation (9) makes every valid
  interpolation invertible;
* coefficients outside `[0, 1]` can destroy positive semidefiniteness;
* a positive-definite endpoint with zero coefficient cannot repair a
  singular other endpoint.

The results concern covariance validity and invertibility.  They do not
establish statistical consistency, optimal shrinkage selection, feature
quality, or source-reported accuracy and runtime.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace StreamingRegularizedDiscriminant

noncomputable section

open Matrix
open scoped Matrix

variable {Feature : Type*}

/-- Equation (11): interpolate a class covariance toward the pooled
covariance. -/
def regularizedClassCovariance
    (classWeight : ℝ)
    (classCovariance pooledCovariance :
      Matrix Feature Feature ℝ) :
    Matrix Feature Feature ℝ :=
  classWeight • classCovariance +
    (1 - classWeight) • pooledCovariance

/-- `α = 0` is the shared-covariance SLDA endpoint. -/
@[simp]
theorem regularizedClassCovariance_zero
    (classCovariance pooledCovariance :
      Matrix Feature Feature ℝ) :
    regularizedClassCovariance 0
        classCovariance pooledCovariance =
      pooledCovariance := by
  simp [regularizedClassCovariance]

/-- `α = 1` is the class-specific SQDA endpoint. -/
@[simp]
theorem regularizedClassCovariance_one
    (classCovariance pooledCovariance :
      Matrix Feature Feature ℝ) :
    regularizedClassCovariance 1
        classCovariance pooledCovariance =
      classCovariance := by
  simp [regularizedClassCovariance]

/-- Convex interpolation preserves positive semidefiniteness. -/
theorem regularizedClassCovariance_posSemidef
    (classWeight : ℝ)
    (classCovariance pooledCovariance :
      Matrix Feature Feature ℝ)
    (weight_nonnegative : 0 ≤ classWeight)
    (weight_le_one : classWeight ≤ 1)
    (class_posSemidef : classCovariance.PosSemidef)
    (pooled_posSemidef : pooledCovariance.PosSemidef) :
    (regularizedClassCovariance classWeight
      classCovariance pooledCovariance).PosSemidef := by
  unfold regularizedClassCovariance
  exact
    (class_posSemidef.smul weight_nonnegative).add
      (pooled_posSemidef.smul
        (sub_nonneg.mpr weight_le_one))

/-- A positive-definite class covariance makes every interpolation with
positive class weight positive definite. -/
theorem regularizedClassCovariance_posDef_of_class
    (classWeight : ℝ)
    (classCovariance pooledCovariance :
      Matrix Feature Feature ℝ)
    (weight_positive : 0 < classWeight)
    (weight_le_one : classWeight ≤ 1)
    (class_posDef : classCovariance.PosDef)
    (pooled_posSemidef : pooledCovariance.PosSemidef) :
    (regularizedClassCovariance classWeight
      classCovariance pooledCovariance).PosDef := by
  have class_part :
      (classWeight • classCovariance).PosDef :=
    class_posDef.smul weight_positive
  have pooled_part :
      ((1 - classWeight) • pooledCovariance).PosSemidef :=
    pooled_posSemidef.smul
      (sub_nonneg.mpr weight_le_one)
  unfold regularizedClassCovariance
  exact class_part.add_posSemidef pooled_part

/-- A positive-definite pooled covariance makes every interpolation with
positive pooled weight positive definite. -/
theorem regularizedClassCovariance_posDef_of_pooled
    (classWeight : ℝ)
    (classCovariance pooledCovariance :
      Matrix Feature Feature ℝ)
    (weight_nonnegative : 0 ≤ classWeight)
    (weight_lt_one : classWeight < 1)
    (class_posSemidef : classCovariance.PosSemidef)
    (pooled_posDef : pooledCovariance.PosDef) :
    (regularizedClassCovariance classWeight
      classCovariance pooledCovariance).PosDef := by
  have class_part :
      (classWeight • classCovariance).PosSemidef :=
    class_posSemidef.smul weight_nonnegative
  have pooled_part :
      ((1 - classWeight) • pooledCovariance).PosDef :=
    pooled_posDef.smul (sub_pos.mpr weight_lt_one)
  unfold regularizedClassCovariance
  exact PosDef.posSemidef_add class_part pooled_part

variable [Fintype Feature] [DecidableEq Feature]

/-- Either positive-definite endpoint yields an invertible interpolated
covariance when it receives positive weight. -/
theorem regularizedClassCovariance_isUnit_of_class
    (classWeight : ℝ)
    (classCovariance pooledCovariance :
      Matrix Feature Feature ℝ)
    (weight_positive : 0 < classWeight)
    (weight_le_one : classWeight ≤ 1)
    (class_posDef : classCovariance.PosDef)
    (pooled_posSemidef : pooledCovariance.PosSemidef) :
    IsUnit
      (regularizedClassCovariance classWeight
        classCovariance pooledCovariance) :=
  (regularizedClassCovariance_posDef_of_class
    classWeight classCovariance pooledCovariance
    weight_positive weight_le_one
    class_posDef pooled_posSemidef).isUnit

omit [Fintype Feature] in
/-- Equation (9) makes every valid regularized covariance positive definite,
even when both input covariances are singular. -/
theorem ridge_regularizedClassCovariance_posDef
    (classWeight ridgeWeight : ℝ)
    (classCovariance pooledCovariance :
      Matrix Feature Feature ℝ)
    (classWeight_nonnegative : 0 ≤ classWeight)
    (classWeight_le_one : classWeight ≤ 1)
    (ridgeWeight_positive : 0 < ridgeWeight)
    (ridgeWeight_le_one : ridgeWeight ≤ 1)
    (class_posSemidef : classCovariance.PosSemidef)
    (pooled_posSemidef : pooledCovariance.PosSemidef) :
    (StreamingLDACovariance.shrinkCovariance
      ridgeWeight
      (regularizedClassCovariance classWeight
        classCovariance pooledCovariance)).PosDef := by
  exact
    StreamingLDACovariance.shrinkCovariance_posDef
      ridgeWeight
      (regularizedClassCovariance classWeight
        classCovariance pooledCovariance)
      (regularizedClassCovariance_posSemidef
        classWeight classCovariance pooledCovariance
        classWeight_nonnegative classWeight_le_one
        class_posSemidef pooled_posSemidef)
      ridgeWeight_positive ridgeWeight_le_one

/-- The same ridge corridor gives a well-defined inverse. -/
theorem ridge_regularizedClassCovariance_isUnit
    (classWeight ridgeWeight : ℝ)
    (classCovariance pooledCovariance :
      Matrix Feature Feature ℝ)
    (classWeight_nonnegative : 0 ≤ classWeight)
    (classWeight_le_one : classWeight ≤ 1)
    (ridgeWeight_positive : 0 < ridgeWeight)
    (ridgeWeight_le_one : ridgeWeight ≤ 1)
    (class_posSemidef : classCovariance.PosSemidef)
    (pooled_posSemidef : pooledCovariance.PosSemidef) :
    IsUnit
      (StreamingLDACovariance.shrinkCovariance
        ridgeWeight
        (regularizedClassCovariance classWeight
          classCovariance pooledCovariance)) :=
  (ridge_regularizedClassCovariance_posDef
    classWeight ridgeWeight
    classCovariance pooledCovariance
    classWeight_nonnegative classWeight_le_one
    ridgeWeight_positive ridgeWeight_le_one
    class_posSemidef pooled_posSemidef).isUnit

section Fixtures

/-- Positive scalar fixture: equal interpolation of covariance one and three
is covariance two. -/
theorem halfWeight_scalar :
    regularizedClassCovariance (Feature := Fin 1)
        (1 / 2)
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        ((3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
      (2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext row column
  fin_cases row
  fin_cases column
  norm_num [regularizedClassCovariance, Matrix.one_apply]

/-- Negative coefficient boundary: `α = 2` turns two positive-semidefinite
inputs, zero and identity, into negative identity. -/
theorem weight_above_one_can_destroy_posSemidef :
    (0 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef ∧
      (1 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef ∧
      ¬
        (regularizedClassCovariance 2
          (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef := by
  constructor
  · exact PosSemidef.zero
  constructor
  · exact PosSemidef.one
  · intro supposedly_posSemidef
    have diagonal_nonnegative :=
      supposedly_posSemidef.diag_nonneg
        (i := (0 : Fin 1))
    norm_num [regularizedClassCovariance, Matrix.one_apply]
      at diagonal_nonnegative

/-- Endpoint boundary: a positive-definite class covariance contributes
nothing at `α = 0`, so a singular pooled covariance stays singular. -/
theorem zero_classWeight_does_not_use_posDef_class :
    ¬ IsUnit
      (regularizedClassCovariance 0
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  simp

end Fixtures

end

end StreamingRegularizedDiscriminant

end Mettapedia.MachineLearning.ContinualLearning

#print axioms
  Mettapedia.MachineLearning.ContinualLearning.StreamingRegularizedDiscriminant.regularizedClassCovariance_posSemidef
#print axioms
  Mettapedia.MachineLearning.ContinualLearning.StreamingRegularizedDiscriminant.ridge_regularizedClassCovariance_isUnit
#print axioms
  Mettapedia.MachineLearning.ContinualLearning.StreamingRegularizedDiscriminant.weight_above_one_can_destroy_posSemidef
