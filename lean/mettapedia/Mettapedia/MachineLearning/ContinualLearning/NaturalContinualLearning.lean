import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FisherGeometry
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Natural continual learning as prior-metric flow

Kao, Jensen, van de Ven, Bernacchia, and Hennequin,
*Natural continual learning: success is a journey, not (just) a destination*
(NeurIPS 2021, arXiv:2106.08085), derive their update from a trust-region
subproblem in the previous posterior's precision metric.

This file formalizes the source's exact first-order core for an arbitrary
invertible symmetric positive-definite metric.  Applying the inverse prior
precision to the gradient of the Laplace objective gives

`Λ⁻¹ taskGradient - (parameter - priorMean)`.

The direction is the unique minimizer of the corresponding positive-metric
Lagrangian and maximizes the linearized posterior gain over the metric ball
whose boundary it reaches.  Preconditioned NCL and raw Laplace-gradient
updates have exactly the same fixed points when their rates are nonzero, but
an anisotropic fixture proves that their paths need not be scalar
reparameterizations of one another.

The theorem is a local trust-region result.  It does not certify a Fisher
estimator, a Kronecker approximation, a finite nonlinear loss decrease, or
the paper's empirical continual-learning results.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace NaturalContinualLearning

open scoped InnerProductSpace
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

section GeneralMetric

variable {Parameter : Type*} [NormedAddCommGroup Parameter]
  [InnerProductSpace ℝ Parameter]

/-- Gradient of the local Laplace log-posterior: current-task log-likelihood
gradient minus the previous posterior's quadratic restoring gradient. -/
noncomputable def posteriorGradient
    (priorPrecision : InvertibleSPDMetric Parameter)
    (taskGradient current priorMean : Parameter) : Parameter :=
  taskGradient - priorPrecision.operator (current - priorMean)

/-- Natural continual-learning direction, obtained by applying the previous
posterior covariance to the complete local posterior gradient. -/
noncomputable def naturalContinualDirection
    (priorPrecision : InvertibleSPDMetric Parameter)
    (taskGradient current priorMean : Parameter) : Parameter :=
  priorPrecision.operator.symm
    (posteriorGradient priorPrecision taskGradient current priorMean)

/-- Source Equation (8): inverse-prior preconditioning acts only on the task
gradient; the quadratic restoring term becomes an ordinary displacement. -/
theorem naturalContinualDirection_eq
    (priorPrecision : InvertibleSPDMetric Parameter)
    (taskGradient current priorMean : Parameter) :
    naturalContinualDirection priorPrecision taskGradient current priorMean =
      priorPrecision.operator.symm taskGradient - (current - priorMean) := by
  simp [naturalContinualDirection, posteriorGradient, map_sub]

/-- One finite NCL update.  Its nonlinear task gradient is supplied at the
current point; the theorem does not assume that it stays fixed afterwards. -/
noncomputable def nclUpdate
    (priorPrecision : InvertibleSPDMetric Parameter)
    (rate : ℝ) (taskGradient current priorMean : Parameter) : Parameter :=
  current +
    rate • naturalContinualDirection priorPrecision taskGradient current priorMean

/-- Ordinary gradient ascent on the same local Laplace objective. -/
noncomputable def rawLaplaceUpdate
    (priorPrecision : InvertibleSPDMetric Parameter)
    (rate : ℝ) (taskGradient current priorMean : Parameter) : Parameter :=
  current + rate •
    posteriorGradient priorPrecision taskGradient current priorMean

/-- Inverse-prior preconditioning introduces or removes no stationary points. -/
theorem naturalContinualDirection_eq_zero_iff
    (priorPrecision : InvertibleSPDMetric Parameter)
    (taskGradient current priorMean : Parameter) :
    naturalContinualDirection priorPrecision taskGradient current priorMean = 0 ↔
      posteriorGradient priorPrecision taskGradient current priorMean = 0 := by
  constructor
  · intro directionZero
    apply priorPrecision.operator.symm.injective
    simpa [naturalContinualDirection] using directionZero
  · intro gradientZero
    simp [naturalContinualDirection, gradientZero]

/-- Every nonzero-rate NCL update has exactly the local Laplace stationary
points as fixed points. -/
theorem nclUpdate_eq_current_iff
    (priorPrecision : InvertibleSPDMetric Parameter)
    (rate : ℝ) (taskGradient current priorMean : Parameter)
    (rate_ne : rate ≠ 0) :
    nclUpdate priorPrecision rate taskGradient current priorMean = current ↔
      posteriorGradient priorPrecision taskGradient current priorMean = 0 := by
  constructor
  · intro updateFixed
    have scaledDirectionZero :
        rate • naturalContinualDirection priorPrecision taskGradient current
          priorMean = 0 := by
      apply add_left_cancel (a := current)
      simpa [nclUpdate] using updateFixed
    have directionZero :
        naturalContinualDirection priorPrecision taskGradient current
          priorMean = 0 :=
      (smul_eq_zero.mp scaledDirectionZero).resolve_left rate_ne
    exact (naturalContinualDirection_eq_zero_iff priorPrecision taskGradient
      current priorMean).mp directionZero
  · intro gradientZero
    have directionZero :
        naturalContinualDirection priorPrecision taskGradient current
          priorMean = 0 :=
      (naturalContinualDirection_eq_zero_iff priorPrecision taskGradient
        current priorMean).mpr gradientZero
    simp [nclUpdate, directionZero]

/-- The raw local-Laplace step has the same nonzero-rate fixed points. -/
theorem rawLaplaceUpdate_eq_current_iff
    (priorPrecision : InvertibleSPDMetric Parameter)
    (rate : ℝ) (taskGradient current priorMean : Parameter)
    (rate_ne : rate ≠ 0) :
    rawLaplaceUpdate priorPrecision rate taskGradient current priorMean = current ↔
      posteriorGradient priorPrecision taskGradient current priorMean = 0 := by
  constructor
  · intro updateFixed
    have scaledGradientZero :
        rate • posteriorGradient priorPrecision taskGradient current
          priorMean = 0 := by
      apply add_left_cancel (a := current)
      simpa [rawLaplaceUpdate] using updateFixed
    exact (smul_eq_zero.mp scaledGradientZero).resolve_left rate_ne
  · intro gradientZero
    simp [rawLaplaceUpdate, gradientZero]

/-- NCL and raw Laplace-gradient optimization share fixed points without
sharing their finite trajectories. -/
theorem ncl_rawLaplace_same_fixed_points
    (priorPrecision : InvertibleSPDMetric Parameter)
    (nclRate rawRate : ℝ) (taskGradient current priorMean : Parameter)
    (nclRate_ne : nclRate ≠ 0) (rawRate_ne : rawRate ≠ 0) :
    nclUpdate priorPrecision nclRate taskGradient current priorMean = current ↔
      rawLaplaceUpdate priorPrecision rawRate taskGradient current priorMean =
        current := by
  rw [nclUpdate_eq_current_iff priorPrecision nclRate taskGradient current
      priorMean nclRate_ne,
    rawLaplaceUpdate_eq_current_iff priorPrecision rawRate taskGradient current
      priorMean rawRate_ne]

/-! ## Exact trust-region/Lagrangian solution -/

/-- Squared displacement in the previous posterior's precision metric. -/
noncomputable def priorMetricSq
    (priorPrecision : InvertibleSPDMetric Parameter)
    (displacement : Parameter) : ℝ :=
  priorPrecision.toAdapterMetric.pair displacement displacement

/-- Linearized local-posterior gain. -/
noncomputable def linearizedPosteriorGain
    (gradient displacement : Parameter) : ℝ :=
  ⟪gradient, displacement⟫_ℝ

/-- Penalized trust-region Lagrangian, with positive multiplier `multiplier`.
Minimizing it is equivalent to maximizing linearized gain while charging
quadratic prior-metric displacement. -/
noncomputable def trustLagrangian
    (priorPrecision : InvertibleSPDMetric Parameter)
    (gradient : Parameter) (multiplier : ℝ)
    (displacement : Parameter) : ℝ :=
  -linearizedPosteriorGain gradient displacement +
    multiplier / 2 * priorMetricSq priorPrecision displacement

/-- Candidate selected by the trust-region Lagrange multiplier. -/
noncomputable def lagrangeDirection
    (priorPrecision : InvertibleSPDMetric Parameter)
    (gradient : Parameter) (multiplier : ℝ) : Parameter :=
  (1 / multiplier) • priorPrecision.operator.symm gradient

private theorem metricPair_smul_left
    (metric : AdapterMetric Parameter) (scalar : ℝ)
    (left right : Parameter) :
    metric.pair (scalar • left) right =
      scalar * metric.pair left right := by
  rw [metric.pair_symmetric, metric.pair_smul_right,
    metric.pair_symmetric]

private theorem metricPair_sub_left
    (metric : AdapterMetric Parameter) (left middle right : Parameter) :
    metric.pair (left - middle) right =
      metric.pair left right - metric.pair middle right := by
  simp [AdapterMetric.pair, inner_sub_left]

private theorem metricPair_sub_right
    (metric : AdapterMetric Parameter) (left middle right : Parameter) :
    metric.pair left (middle - right) =
      metric.pair left middle - metric.pair left right := by
  simp [AdapterMetric.pair, inner_sub_right]

/-- Pairing an inverse-precision gradient through the precision metric
recovers the original Euclidean gradient functional. -/
theorem covariance_metricPair
    (priorPrecision : InvertibleSPDMetric Parameter)
    (gradient displacement : Parameter) :
    priorPrecision.toAdapterMetric.pair
        (priorPrecision.operator.symm gradient) displacement =
      ⟪gradient, displacement⟫_ℝ := by
  simp [InvertibleSPDMetric.toAdapterMetric, AdapterMetric.pair]

/-- Source stationarity equation: the selected displacement solves
`gradient - multiplier * precision * displacement = 0`. -/
theorem lagrangeDirection_stationary
    (priorPrecision : InvertibleSPDMetric Parameter)
    (gradient : Parameter) (multiplier : ℝ)
    (multiplier_ne : multiplier ≠ 0) :
    gradient -
        multiplier • priorPrecision.operator
          (lagrangeDirection priorPrecision gradient multiplier) = 0 := by
  simp [lagrangeDirection, smul_smul, multiplier_ne]

private theorem gradient_inner_eq_multiplier_pair
    (priorPrecision : InvertibleSPDMetric Parameter)
    (gradient displacement : Parameter) (multiplier : ℝ)
    (multiplier_ne : multiplier ≠ 0) :
    ⟪gradient, displacement⟫_ℝ =
      multiplier *
        priorPrecision.toAdapterMetric.pair
          (lagrangeDirection priorPrecision gradient multiplier)
          displacement := by
  rw [← covariance_metricPair priorPrecision gradient displacement]
  simp [lagrangeDirection, metricPair_smul_left, multiplier_ne]

private theorem metricPair_sub_self_expansion
    (metric : AdapterMetric Parameter) (candidate chosen : Parameter) :
    metric.pair (candidate - chosen) (candidate - chosen) =
      metric.pair candidate candidate -
        2 * metric.pair chosen candidate +
        metric.pair chosen chosen := by
  rw [metricPair_sub_left, metricPair_sub_right, metricPair_sub_right,
    metric.pair_symmetric candidate chosen]
  ring

/-- Exact completion-of-squares identity for the source trust-region
Lagrangian. -/
theorem trustLagrangian_sub_at_lagrangeDirection
    (priorPrecision : InvertibleSPDMetric Parameter)
    (gradient candidate : Parameter) (multiplier : ℝ)
    (multiplier_ne : multiplier ≠ 0) :
    trustLagrangian priorPrecision gradient multiplier candidate -
        trustLagrangian priorPrecision gradient multiplier
          (lagrangeDirection priorPrecision gradient multiplier) =
      multiplier / 2 *
        priorPrecision.toAdapterMetric.pair
          (candidate - lagrangeDirection priorPrecision gradient multiplier)
          (candidate - lagrangeDirection priorPrecision gradient multiplier) := by
  let chosen := lagrangeDirection priorPrecision gradient multiplier
  have candidatePair :=
    gradient_inner_eq_multiplier_pair priorPrecision gradient candidate
      multiplier multiplier_ne
  have chosenPair :=
    gradient_inner_eq_multiplier_pair priorPrecision gradient chosen
      multiplier multiplier_ne
  have differenceExpansion :=
    metricPair_sub_self_expansion priorPrecision.toAdapterMetric candidate chosen
  change trustLagrangian priorPrecision gradient multiplier candidate -
      trustLagrangian priorPrecision gradient multiplier chosen =
    multiplier / 2 *
      priorPrecision.toAdapterMetric.pair (candidate - chosen)
        (candidate - chosen)
  rw [trustLagrangian, trustLagrangian, linearizedPosteriorGain,
    linearizedPosteriorGain, priorMetricSq, priorMetricSq,
    candidatePair, chosenPair, differenceExpansion]
  ring

/-- A positive multiplier makes the selected direction a global minimizer of
the penalized local trust-region problem. -/
theorem lagrangeDirection_minimizes
    (priorPrecision : InvertibleSPDMetric Parameter)
    (gradient candidate : Parameter) (multiplier : ℝ)
    (multiplier_pos : 0 < multiplier) :
    trustLagrangian priorPrecision gradient multiplier
        (lagrangeDirection priorPrecision gradient multiplier) ≤
      trustLagrangian priorPrecision gradient multiplier candidate := by
  have differenceIdentity :=
    trustLagrangian_sub_at_lagrangeDirection priorPrecision gradient candidate
      multiplier (ne_of_gt multiplier_pos)
  have metricNonnegative :=
    priorPrecision.toAdapterMetric.nonnegative
      (candidate - lagrangeDirection priorPrecision gradient multiplier)
  have multiplierHalfNonnegative : 0 ≤ multiplier / 2 := by
    positivity
  have differenceNonnegative :
      0 ≤ multiplier / 2 *
        priorPrecision.toAdapterMetric.pair
          (candidate - lagrangeDirection priorPrecision gradient multiplier)
          (candidate - lagrangeDirection priorPrecision gradient multiplier) :=
    mul_nonneg multiplierHalfNonnegative metricNonnegative
  rw [← differenceIdentity] at differenceNonnegative
  linarith

/-- Positive definiteness makes the Lagrangian minimizer unique. -/
theorem lagrangeDirection_strictly_minimizes
    (priorPrecision : InvertibleSPDMetric Parameter)
    (gradient candidate : Parameter) (multiplier : ℝ)
    (multiplier_pos : 0 < multiplier)
    (candidate_ne :
      candidate ≠ lagrangeDirection priorPrecision gradient multiplier) :
    trustLagrangian priorPrecision gradient multiplier
        (lagrangeDirection priorPrecision gradient multiplier) <
      trustLagrangian priorPrecision gradient multiplier candidate := by
  have differenceIdentity :=
    trustLagrangian_sub_at_lagrangeDirection priorPrecision gradient candidate
      multiplier (ne_of_gt multiplier_pos)
  have difference_ne :
      candidate -
          lagrangeDirection priorPrecision gradient multiplier ≠ 0 :=
    sub_ne_zero.mpr candidate_ne
  have metricPositive :=
    priorPrecision.positive
      (candidate - lagrangeDirection priorPrecision gradient multiplier)
      difference_ne
  have multiplierHalfPositive : 0 < multiplier / 2 := by
    positivity
  have differencePositive :
      0 < multiplier / 2 *
        priorPrecision.toAdapterMetric.pair
          (candidate - lagrangeDirection priorPrecision gradient multiplier)
          (candidate - lagrangeDirection priorPrecision gradient multiplier) :=
    mul_pos multiplierHalfPositive metricPositive
  rw [← differenceIdentity] at differencePositive
  linarith

/-- The Lagrange direction maximizes linearized posterior gain over its own
closed prior-metric ball.  This is the constrained source subproblem with the
radius chosen implicitly by the positive multiplier. -/
theorem lagrangeDirection_maximizes_on_own_metricBall
    (priorPrecision : InvertibleSPDMetric Parameter)
    (gradient candidate : Parameter) (multiplier : ℝ)
    (multiplier_pos : 0 < multiplier)
    (candidate_in_ball :
      priorMetricSq priorPrecision candidate ≤
        priorMetricSq priorPrecision
          (lagrangeDirection priorPrecision gradient multiplier)) :
    linearizedPosteriorGain gradient candidate ≤
      linearizedPosteriorGain gradient
        (lagrangeDirection priorPrecision gradient multiplier) := by
  have minimum :=
    lagrangeDirection_minimizes priorPrecision gradient candidate multiplier
      multiplier_pos
  have multiplierHalfNonnegative : 0 ≤ multiplier / 2 := by
    positivity
  have scaledCostLe :
      multiplier / 2 * priorMetricSq priorPrecision candidate ≤
        multiplier / 2 *
          priorMetricSq priorPrecision
            (lagrangeDirection priorPrecision gradient multiplier) :=
    mul_le_mul_of_nonneg_left candidate_in_ball multiplierHalfNonnegative
  unfold trustLagrangian at minimum
  linarith

/-- NCL is the unit-multiplier trust-region direction for the complete local
posterior gradient. -/
theorem naturalContinualDirection_eq_lagrangeDirection_one
    (priorPrecision : InvertibleSPDMetric Parameter)
    (taskGradient current priorMean : Parameter) :
    naturalContinualDirection priorPrecision taskGradient current priorMean =
      lagrangeDirection priorPrecision
        (posteriorGradient priorPrecision taskGradient current priorMean) 1 := by
  simp [naturalContinualDirection, lagrangeDirection]

end GeneralMetric

/-! ## Recovery and strict path-separation fixtures -/

section Fixtures

variable {Parameter : Type*} [NormedAddCommGroup Parameter]
  [InnerProductSpace ℝ Parameter]

/-- Unit prior precision. -/
noncomputable def identityPriorPrecision :
    InvertibleSPDMetric Parameter where
  operator := ContinuousLinearEquiv.refl ℝ Parameter
  symmetric := by
    intro left right
    simp only [ContinuousLinearEquiv.refl_apply]
    exact (real_inner_comm left right).symm
  positive := by
    intro value value_ne
    rw [ContinuousLinearEquiv.refl_apply, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr value_ne)

/-- With unit prior precision, NCL recovers the raw local-posterior gradient. -/
@[simp] theorem identityPriorPrecision_recovers_raw
    (taskGradient current priorMean : Parameter) :
    naturalContinualDirection
        (identityPriorPrecision : InvertibleSPDMetric Parameter)
        taskGradient current priorMean =
      posteriorGradient identityPriorPrecision taskGradient current priorMean := by
  simp [naturalContinualDirection, identityPriorPrecision]

end Fixtures

abbrev NCLPlane := WithLp 2 (ℝ × ℝ)

noncomputable def nclAxis0 : NCLPlane :=
  WithLp.toLp 2 (1, 0)

noncomputable def nclAxis1 : NCLPlane :=
  WithLp.toLp 2 (0, 1)

/-- A posterior gradient in two coordinates. -/
noncomputable def anisotropicRawDirection : NCLPlane :=
  WithLp.toLp 2 (2, 1)

/-- Applying inverse precision `diag(1/2,1)` to the raw direction. -/
noncomputable def anisotropicNaturalDirection : NCLPlane :=
  WithLp.toLp 2 (1, 1)

private noncomputable def scaleTwoReal : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
    (Units.mk0 (2 : ℝ) (by norm_num))

/-- The diagonal precision operator `diag(2,1)` on the concrete plane. -/
noncomputable def anisotropicPrecisionOperator : NCLPlane ≃L[ℝ] NCLPlane :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).trans <|
    (scaleTwoReal.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans <|
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm

@[simp] theorem anisotropicPrecisionOperator_apply (x : ℝ × ℝ) :
    anisotropicPrecisionOperator (WithLp.toLp 2 x) =
      WithLp.toLp 2 (2 * x.1, x.2) := by
  rcases x with ⟨x, y⟩
  norm_num [anisotropicPrecisionOperator, scaleTwoReal,
    ContinuousLinearEquiv.prodCongr_apply]

/-- A concrete anisotropic symmetric positive-definite prior precision. -/
noncomputable def anisotropicPriorPrecision :
    InvertibleSPDMetric NCLPlane where
  operator := anisotropicPrecisionOperator
  symmetric := by
    intro x y
    rw [← WithLp.toLp_ofLp 2 x, ← WithLp.toLp_ofLp 2 y,
      anisotropicPrecisionOperator_apply,
      anisotropicPrecisionOperator_apply,
      WithLp.prod_inner_apply, WithLp.prod_inner_apply]
    simp
    ring
  positive := by
    intro x hx
    rw [← WithLp.toLp_ofLp 2 x, anisotropicPrecisionOperator_apply,
      WithLp.prod_inner_apply]
    by_cases hx₁ : (WithLp.ofLp x).1 = 0
    · have hx₂ : (WithLp.ofLp x).2 ≠ 0 := by
        intro hx₂
        apply hx
        apply (WithLp.ofLp_eq_zero 2).mp
        exact Prod.ext hx₁ hx₂
      rw [RCLike.inner_apply, RCLike.inner_apply]
      simp only [map_mul, map_ofNat, starRingEnd_apply, star_trivial]
      nlinarith [sq_nonneg (WithLp.ofLp x).1, sq_pos_of_ne_zero hx₂]
    · rw [RCLike.inner_apply, RCLike.inner_apply]
      simp only [map_mul, map_ofNat, starRingEnd_apply, star_trivial]
      nlinarith [sq_pos_of_ne_zero hx₁, sq_nonneg (WithLp.ofLp x).2]

private theorem scaleTwoReal_symm_two : scaleTwoReal.symm 2 = 1 := by
  apply scaleTwoReal.injective
  norm_num [scaleTwoReal]

/-- The concrete posterior gradient is the displayed raw direction. -/
@[simp] theorem anisotropicRawPosteriorGradient_eq :
    posteriorGradient anisotropicPriorPrecision anisotropicRawDirection 0 0 =
      anisotropicRawDirection := by
  simp [posteriorGradient]

/-- The actual NCL definition sends the concrete raw posterior gradient
through inverse prior precision to the displayed natural direction. -/
@[simp] theorem anisotropicNaturalDirection_eq :
    naturalContinualDirection anisotropicPriorPrecision
        anisotropicRawDirection 0 0 =
      anisotropicNaturalDirection := by
  norm_num [naturalContinualDirection, posteriorGradient,
    anisotropicRawDirection, anisotropicNaturalDirection,
    anisotropicPriorPrecision, anisotropicPrecisionOperator,
    ContinuousLinearEquiv.prodCongr_symm, scaleTwoReal_symm_two]

private theorem anisotropicDirections_not_collinear (scale : ℝ) :
    scale • anisotropicRawDirection ≠ anisotropicNaturalDirection := by
  intro equalDirections
  have coordinateZero := congrArg
    (fun vector : NCLPlane => (WithLp.ofLp vector).1) equalDirections
  have coordinateOne := congrArg
    (fun vector : NCLPlane => (WithLp.ofLp vector).2) equalDirections
  norm_num [anisotropicRawDirection, anisotropicNaturalDirection] at coordinateZero coordinateOne
  linarith

/-- An anisotropic prior metric changes the actual NCL direction, not merely
its step size.  Thus shared fixed points do not imply
scalar-reparameterized trajectories. -/
theorem anisotropic_ncl_not_scalar_raw (scale : ℝ) :
    scale •
        posteriorGradient anisotropicPriorPrecision anisotropicRawDirection 0 0 ≠
      naturalContinualDirection anisotropicPriorPrecision
        anisotropicRawDirection 0 0 := by
  rw [anisotropicRawPosteriorGradient_eq, anisotropicNaturalDirection_eq]
  exact anisotropicDirections_not_collinear scale

end NaturalContinualLearning

end Mettapedia.MachineLearning.ContinualLearning
