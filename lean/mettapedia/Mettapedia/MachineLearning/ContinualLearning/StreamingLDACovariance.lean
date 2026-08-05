import Mathlib

/-!
# Streaming LDA covariance and shrinkage

Hayes and Kanan,
*Lifelong Machine Learning with Deep Streaming Linear Discriminant Analysis*
(CVPR Workshops 2020, arXiv:1909.01520), Equations (2)--(7), keep a frozen
feature extractor, update class means and one shared covariance online, and
form a precision matrix by shrinkage.

This file isolates the covariance geometry of that mechanism:

* the rank-one innovation in Equation (5) is positive semidefinite;
* the streaming covariance update in Equation (4) preserves positive
  semidefiniteness;
* if the incoming covariance is positive semidefinite and the shrinkage
  coefficient lies in `(0, 1]`, adding the identity ridge makes the shrunk
  covariance positive definite and hence invertible.

Both coefficient boundaries are explicit. Zero shrinkage cannot repair a
singular zero covariance, and a coefficient above one can turn a positive
semidefinite covariance into a matrix that is not positive semidefinite.

The development does not prove feature quality, statistical consistency of
the covariance estimate, calibration, classification accuracy, or any
source-reported speed or memory comparison.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace StreamingLDACovariance

noncomputable section

open Matrix
open scoped Matrix

variable {Feature : Type*} [Fintype Feature] [DecidableEq Feature]

/-- Rank-one covariance contribution in Equation (5). -/
def scatterIncrement
    (count : ℕ)
    (mean sample : Feature → ℝ) :
    Matrix Feature Feature ℝ :=
  ((count : ℝ) / ((count + 1 : ℕ) : ℝ)) •
    Matrix.vecMulVec (sample - mean) (sample - mean)

/-- Shared streaming covariance update in Equation (4). -/
def covarianceUpdate
    (count : ℕ)
    (covariance : Matrix Feature Feature ℝ)
    (classMean sample : Feature → ℝ) :
    Matrix Feature Feature ℝ :=
  (1 / ((count + 1 : ℕ) : ℝ)) •
    ((count : ℝ) • covariance +
      scatterIncrement count classMean sample)

omit [DecidableEq Feature] in
/-- The unscaled rank-one outer product of an innovation is positive
semidefinite. -/
theorem innovationOuter_posSemidef
    (classMean sample : Feature → ℝ) :
    (Matrix.vecMulVec (sample - classMean)
      (sample - classMean)).PosSemidef := by
  simpa using
    Matrix.posSemidef_vecMulVec_self_star (sample - classMean)

omit [DecidableEq Feature] in
/-- The source's count-scaled rank-one innovation is positive semidefinite. -/
theorem scatterIncrement_posSemidef
    (count : ℕ)
    (classMean sample : Feature → ℝ) :
    (scatterIncrement count classMean sample).PosSemidef := by
  apply (innovationOuter_posSemidef classMean sample).smul
  positivity

omit [DecidableEq Feature] in
/-- Every streaming update preserves positive semidefiniteness of the shared
covariance. -/
theorem covarianceUpdate_posSemidef
    (count : ℕ)
    (covariance : Matrix Feature Feature ℝ)
    (classMean sample : Feature → ℝ)
    (covariance_posSemidef : covariance.PosSemidef) :
    (covarianceUpdate count covariance classMean sample).PosSemidef := by
  unfold covarianceUpdate
  apply PosSemidef.smul
  · exact (covariance_posSemidef.smul (by positivity)).add
      (scatterIncrement_posSemidef count classMean sample)
  · positivity

/-- Shrink a covariance toward the identity before inversion. -/
def shrinkCovariance
    (shrinkage : ℝ)
    (covariance : Matrix Feature Feature ℝ) :
    Matrix Feature Feature ℝ :=
  (1 - shrinkage) • covariance +
    shrinkage • (1 : Matrix Feature Feature ℝ)

omit [Fintype Feature] in
/-- Positive shrinkage of a positive-semidefinite covariance is strictly
positive definite when the covariance coefficient remains nonnegative. -/
theorem shrinkCovariance_posDef
    (shrinkage : ℝ)
    (covariance : Matrix Feature Feature ℝ)
    (covariance_posSemidef : covariance.PosSemidef)
    (shrinkage_pos : 0 < shrinkage)
    (shrinkage_le_one : shrinkage ≤ 1) :
    (shrinkCovariance shrinkage covariance).PosDef := by
  have covariance_part :
      ((1 - shrinkage) • covariance).PosSemidef :=
    covariance_posSemidef.smul (sub_nonneg.mpr shrinkage_le_one)
  have identity_posDef :
      (1 : Matrix Feature Feature ℝ).PosDef :=
    PosDef.one
  have ridge_part :
      (shrinkage • (1 : Matrix Feature Feature ℝ)).PosDef :=
    identity_posDef.smul shrinkage_pos
  unfold shrinkCovariance
  exact PosDef.posSemidef_add covariance_part ridge_part

/-- Under the same coefficient domain, the shrunk covariance is a unit and
therefore has a well-defined matrix inverse. -/
theorem shrinkCovariance_isUnit
    (shrinkage : ℝ)
    (covariance : Matrix Feature Feature ℝ)
    (covariance_posSemidef : covariance.PosSemidef)
    (shrinkage_pos : 0 < shrinkage)
    (shrinkage_le_one : shrinkage ≤ 1) :
    IsUnit (shrinkCovariance shrinkage covariance) :=
  (shrinkCovariance_posDef shrinkage covariance covariance_posSemidef
    shrinkage_pos shrinkage_le_one).isUnit

/-- A concrete one-dimensional update: count one, covariance two, mean zero,
and sample two leave the covariance equal to two. -/
theorem scalar_covarianceUpdate :
    covarianceUpdate (Feature := Fin 1) 1
      (fun _ _ => 2) (fun _ => 0) (fun _ => 2) =
      (fun _ _ => 2) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [covarianceUpdate, scatterIncrement, Matrix.vecMulVec]

/-- Negative boundary: zero shrinkage cannot make the zero covariance
invertible. -/
theorem zero_shrinkage_zeroCovariance_not_isUnit :
    ¬ IsUnit
      (shrinkCovariance 0
        (0 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  simp [shrinkCovariance]

/-- Negative boundary: extending the coefficient beyond one can destroy
positive semidefiniteness even when the input covariance is positive
semidefinite. -/
theorem excessive_shrinkage_can_destroy_posSemidef :
    ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef ∧
      ¬ (shrinkCovariance 3
        ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))).PosSemidef := by
  constructor
  · exact PosSemidef.one.smul (by norm_num)
  · intro supposedly_posSemidef
    have diagonal_nonnegative :=
      supposedly_posSemidef.diag_nonneg (i := (0 : Fin 1))
    norm_num [shrinkCovariance, Matrix.one_apply] at diagonal_nonnegative

#print axioms innovationOuter_posSemidef
#print axioms covarianceUpdate_posSemidef
#print axioms shrinkCovariance_posDef
#print axioms shrinkCovariance_isUnit
#print axioms scalar_covarianceUpdate
#print axioms zero_shrinkage_zeroCovariance_not_isUnit
#print axioms excessive_shrinkage_can_destroy_posSemidef

end

end StreamingLDACovariance

end Mettapedia.MachineLearning.ContinualLearning
