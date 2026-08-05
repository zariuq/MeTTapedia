import Mettapedia.MachineLearning.ContinualLearning.RetentionSafeUpdate

/-!
# Low-rank forgetting: the angle/curvature boundary

Steele et al. (2026), *Subspace Geometry Governs Catastrophic Forgetting in
Low-Rank Adaptation*, report an empirically fitted relationship between
forgetting and the minimum principal angle of consecutive task-gradient
subspaces.  The deductive part of the source is the smooth-loss Taylor
upper model: first-order alignment and second-order curvature are separate
terms.

This file isolates that rigorous core.  An alignment certificate gives a
finite forgetting bound for every smooth retention loss, and exact
orthogonality removes only the first-order term.  A two-dimensional quadratic
family then proves a strict boundary: two old losses can have the same
initial gradient, the same orthogonal unit update, and the same unit quadratic
upper model, while their finite forgetting differs.  Consequently,
first-order angle data alone cannot determine exact finite forgetting.

The source's fitted separation law, effective-rank saturation, and
rank-invariance observation remain empirical claims.  They are not promoted
to deductive consequences of smoothness or principal-angle geometry here.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

open scoped InnerProductSpace

namespace LowRankForgettingGeometry

noncomputable section

/-! ## Smooth finite forgetting -/

variable {Adapter : Type*} [NormedAddCommGroup Adapter]
  [InnerProductSpace ℝ Adapter] [CompleteSpace Adapter]

/-- Finite old-task loss change caused by an adapter update. -/
def finiteForgetting
    (loss : Adapter → ℝ) (parameter update : Adapter) : ℝ :=
  loss (parameter + update) - loss parameter

/-- A checkable upper bound on first-order gradient/update alignment.
For task subspaces, `cosineBound` can be supplied by a separately verified
principal-angle certificate. -/
def AlignmentUpperBound
    (gradient update : Adapter) (cosineBound : ℝ) : Prop :=
  ⟪gradient, update⟫_ℝ ≤
    ‖gradient‖ * ‖update‖ * cosineBound

/-- The rigorous Taylor content: finite forgetting is bounded by the
first-order alignment term plus the complete smoothness remainder. -/
theorem smooth_finiteForgetting_le_alignment_add_curvature
    {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
    (parameter update : Adapter) :
    finiteForgetting model.loss parameter update ≤
      ⟪model.gradient parameter, update⟫_ℝ +
        beta / 2 * ‖update‖ ^ 2 := by
  have bound := smoothRetention_descentLemma model parameter update
  unfold finiteForgetting
  linarith

/-- A verified alignment coefficient can replace the inner product in the
finite forgetting budget. -/
theorem smooth_finiteForgetting_le_of_alignmentUpperBound
    {beta cosineBound : ℝ} (model : SmoothRetentionLoss Adapter beta)
    (parameter update : Adapter)
    (alignment : AlignmentUpperBound
      (model.gradient parameter) update cosineBound) :
    finiteForgetting model.loss parameter update ≤
      ‖model.gradient parameter‖ * ‖update‖ * cosineBound +
        beta / 2 * ‖update‖ ^ 2 := by
  have smooth :=
    smooth_finiteForgetting_le_alignment_add_curvature
      model parameter update
  unfold AlignmentUpperBound at alignment
  linarith

/-- Orthogonality eliminates the first-order term, not the curvature term. -/
theorem smooth_finiteForgetting_le_curvature_of_orthogonal
    {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
    (parameter update : Adapter)
    (orthogonal : ⟪model.gradient parameter, update⟫_ℝ = 0) :
    finiteForgetting model.loss parameter update ≤
      beta / 2 * ‖update‖ ^ 2 := by
  have smooth :=
    smooth_finiteForgetting_le_alignment_add_curvature
      model parameter update
  rw [orthogonal] at smooth
  linarith

/-! ## Exact two-dimensional boundary -/

abbrev ForgettingPlane := Fin 2 → ℝ

/-- A family of old-task losses with a shared initial gradient.  The second
coordinate's curvature is deliberately visible. -/
def axisQuadraticLoss
    (secondCurvature : ℝ) (parameter : ForgettingPlane) : ℝ :=
  parameter 0 + ((parameter 0) ^ 2 +
    secondCurvature * (parameter 1) ^ 2) / 2

/-- Exact gradient of `axisQuadraticLoss`. -/
def axisQuadraticGradient
    (secondCurvature : ℝ) (parameter : ForgettingPlane) :
    ForgettingPlane :=
  ![1 + parameter 0, secondCurvature * parameter 1]

/-- Algebraic Euclidean pairing used by the executable fixture. -/
def planePairing
    (first second : ForgettingPlane) : ℝ :=
  dotProduct first second

/-- Squared Euclidean norm, kept algebraic so exact dyadic fixtures remain
kernel-computable. -/
def planeSquaredNorm (vector : ForgettingPlane) : ℝ :=
  planePairing vector vector

/-- The first-order geometry visible to an angle-based diagnostic. -/
structure FirstOrderSignature where
  pairing : ℝ
  gradientSquaredNorm : ℝ
  updateSquaredNorm : ℝ
deriving DecidableEq

def firstOrderSignature
    (secondCurvature : ℝ)
    (parameter update : ForgettingPlane) : FirstOrderSignature where
  pairing :=
    planePairing (axisQuadraticGradient secondCurvature parameter) update
  gradientSquaredNorm :=
    planeSquaredNorm (axisQuadraticGradient secondCurvature parameter)
  updateSquaredNorm := planeSquaredNorm update

def zeroParameter : ForgettingPlane := ![0, 0]

def orthogonalUnitUpdate : ForgettingPlane := ![0, 1]

/-- Exact second-order Taylor identity for the quadratic family. -/
theorem axisQuadraticLoss_update_exact
    (secondCurvature : ℝ)
    (parameter update : ForgettingPlane) :
    finiteForgetting (axisQuadraticLoss secondCurvature)
        parameter update =
      planePairing (axisQuadraticGradient secondCurvature parameter) update +
        ((update 0) ^ 2 +
          secondCurvature * (update 1) ^ 2) / 2 := by
  simp [finiteForgetting, axisQuadraticLoss, axisQuadraticGradient,
    planePairing, dotProduct, Fin.sum_univ_two]
  ring

/-- Every second-coordinate curvature at most one satisfies the same unit
quadratic upper model. -/
theorem axisQuadraticLoss_common_unitUpperModel_bound
    (secondCurvature : ℝ)
    (curvatureAtMostOne : secondCurvature ≤ 1)
    (parameter update : ForgettingPlane) :
    finiteForgetting (axisQuadraticLoss secondCurvature)
        parameter update ≤
      planePairing (axisQuadraticGradient secondCurvature parameter) update +
        planeSquaredNorm update / 2 := by
  rw [axisQuadraticLoss_update_exact]
  simp only [planeSquaredNorm, planePairing, dotProduct,
    Fin.sum_univ_two]
  nlinarith [sq_nonneg (update 0), sq_nonneg (update 1)]

/-- The two endpoint losses have identical first-order angle data at the
origin for the same orthogonal unit update. -/
theorem endpoint_firstOrderSignatures_equal :
    firstOrderSignature 0 zeroParameter orthogonalUnitUpdate =
      firstOrderSignature 1 zeroParameter orthogonalUnitUpdate := by
  norm_num [firstOrderSignature, zeroParameter, orthogonalUnitUpdate,
    axisQuadraticGradient, planeSquaredNorm, planePairing,
    dotProduct, Fin.sum_univ_two]

/-- Positive endpoint: orthogonality plus zero curvature gives exact
retention. -/
theorem zeroCurvature_orthogonalUpdate_has_zero_forgetting :
    finiteForgetting (axisQuadraticLoss 0)
      zeroParameter orthogonalUnitUpdate = 0 := by
  norm_num [finiteForgetting, axisQuadraticLoss, zeroParameter,
    orthogonalUnitUpdate]

/-- Negative endpoint: the same first-order geometry with unit curvature
incurs positive finite forgetting. -/
theorem unitCurvature_orthogonalUpdate_has_positive_forgetting :
    finiteForgetting (axisQuadraticLoss 1)
      zeroParameter orthogonalUnitUpdate = 1 / 2 := by
  norm_num [finiteForgetting, axisQuadraticLoss, zeroParameter,
    orthogonalUnitUpdate]

/-- Even with a common unit quadratic upper model, no predictor using only the
first-order angle signature can equal exact forgetting on both endpoint
losses. -/
theorem no_firstOrderSignature_predictor_fits_both_endpoints :
    ¬ ∃ predictor : FirstOrderSignature → ℝ,
      finiteForgetting (axisQuadraticLoss 0)
          zeroParameter orthogonalUnitUpdate =
        predictor
          (firstOrderSignature 0 zeroParameter orthogonalUnitUpdate) ∧
      finiteForgetting (axisQuadraticLoss 1)
          zeroParameter orthogonalUnitUpdate =
        predictor
          (firstOrderSignature 1 zeroParameter orthogonalUnitUpdate) := by
  rintro ⟨predictor, zeroPrediction, unitPrediction⟩
  rw [endpoint_firstOrderSignatures_equal] at zeroPrediction
  rw [zeroCurvature_orthogonalUpdate_has_zero_forgetting] at zeroPrediction
  rw [unitCurvature_orthogonalUpdate_has_positive_forgetting] at unitPrediction
  linarith

/-- The complete boundary in one executable statement: the endpoint models
share angle data and a unit quadratic upper model, but disagree on
forgetting. -/
theorem same_angle_same_norm_same_upperModel_different_forgetting :
    firstOrderSignature 0 zeroParameter orthogonalUnitUpdate =
        firstOrderSignature 1 zeroParameter orthogonalUnitUpdate ∧
      (∀ parameter update,
        finiteForgetting (axisQuadraticLoss 0) parameter update ≤
          planePairing (axisQuadraticGradient 0 parameter) update +
            planeSquaredNorm update / 2) ∧
      (∀ parameter update,
        finiteForgetting (axisQuadraticLoss 1) parameter update ≤
          planePairing (axisQuadraticGradient 1 parameter) update +
            planeSquaredNorm update / 2) ∧
      finiteForgetting (axisQuadraticLoss 0)
          zeroParameter orthogonalUnitUpdate = 0 ∧
      finiteForgetting (axisQuadraticLoss 1)
          zeroParameter orthogonalUnitUpdate = 1 / 2 := by
  exact ⟨endpoint_firstOrderSignatures_equal,
    fun parameter update =>
      axisQuadraticLoss_common_unitUpperModel_bound
        0 (by norm_num) parameter update,
    fun parameter update =>
      axisQuadraticLoss_common_unitUpperModel_bound
        1 (by norm_num) parameter update,
    zeroCurvature_orthogonalUpdate_has_zero_forgetting,
    unitCurvature_orthogonalUpdate_has_positive_forgetting⟩

#print axioms smooth_finiteForgetting_le_of_alignmentUpperBound
#print axioms smooth_finiteForgetting_le_curvature_of_orthogonal
#print axioms axisQuadraticLoss_update_exact
#print axioms axisQuadraticLoss_common_unitUpperModel_bound
#print axioms no_firstOrderSignature_predictor_fits_both_endpoints
#print axioms same_angle_same_norm_same_upperModel_different_forgetting

end

end LowRankForgettingGeometry

end Mettapedia.MachineLearning.ContinualLearning
