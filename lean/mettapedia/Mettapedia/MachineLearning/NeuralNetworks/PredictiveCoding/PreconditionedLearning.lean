import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.BacktrackingDescent
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Preconditioned predictive-coding weight updates

This file gives an exact scalar control model for one trainable link in a
linear chain.  The fixed upstream activation and the product of downstream
gains collapse the rest of the chain into one effective gain.  The local
half-squared output loss is therefore quadratic in the selected weight.

The predictive-coding update is modeled as a scalar preconditioner applied to
the curvature-normalized backpropagation direction.  Identity preconditioning
reaches the quadratic optimum in one step.  Departing from identity leaves an
exact squared residual factor, giving a precise loss-descent degradation law.
This is a controlled statement; it does not assert that arbitrary matrix
preconditioners or nonlinear networks are ordered solely by distance from the
identity.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## One selected link in a collapsed scalar chain -/

/-- Output prediction after collapsing all fixed downstream gains. -/
noncomputable def chainLinkPrediction
    (sourceActivation downstreamGain weight : ℝ) : ℝ :=
  downstreamGain * weight * sourceActivation

/-- Output residual as a function of the selected link weight. -/
noncomputable def chainLinkResidual
    (sourceActivation downstreamGain target weight : ℝ) : ℝ :=
  chainLinkPrediction sourceActivation downstreamGain weight - target

/-- Half-squared output loss for the selected scalar chain link. -/
noncomputable def chainLinkHalfSquaredLoss
    (sourceActivation downstreamGain target weight : ℝ) : ℝ :=
  (chainLinkResidual sourceActivation downstreamGain target weight) ^ 2 / 2

/-- Ordinary backpropagation gradient for the selected weight. -/
noncomputable def chainLinkBackpropGradient
    (sourceActivation downstreamGain target weight : ℝ) : ℝ :=
  (downstreamGain * sourceActivation) *
    chainLinkResidual sourceActivation downstreamGain target weight

/-- Exact scalar curvature of the selected-weight quadratic. -/
noncomputable def chainLinkCurvature
    (sourceActivation downstreamGain : ℝ) : ℝ :=
  (downstreamGain * sourceActivation) ^ 2

/-- Backpropagation direction normalized by the exact scalar curvature. -/
noncomputable def chainLinkNormalizedBackpropDirection
    (sourceActivation downstreamGain target weight : ℝ) : ℝ :=
  chainLinkBackpropGradient sourceActivation downstreamGain target weight /
    chainLinkCurvature sourceActivation downstreamGain

/-- Predictive-coding control update: a scalar preconditioner multiplies the
curvature-normalized backpropagation direction. -/
noncomputable def chainLinkPreconditionedPCUpdate
    (preconditioner sourceActivation downstreamGain target weight : ℝ) : ℝ :=
  weight - preconditioner *
    chainLinkNormalizedBackpropDirection sourceActivation downstreamGain target weight

/-- Loss removed by one preconditioned update. -/
noncomputable def chainLinkLossDecrease
    (preconditioner sourceActivation downstreamGain target weight : ℝ) : ℝ :=
  chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight -
    chainLinkHalfSquaredLoss sourceActivation downstreamGain target
      (chainLinkPreconditionedPCUpdate preconditioner sourceActivation downstreamGain
        target weight)

theorem chainLinkNormalizedBackpropDirection_eq_residual_div_effectiveGain
    (sourceActivation downstreamGain target weight : ℝ) :
    chainLinkNormalizedBackpropDirection sourceActivation downstreamGain target weight =
      chainLinkResidual sourceActivation downstreamGain target weight /
        (downstreamGain * sourceActivation) := by
  unfold chainLinkNormalizedBackpropDirection chainLinkBackpropGradient
    chainLinkCurvature
  field_simp

theorem chainLinkResidual_preconditionedUpdate_exact
    (preconditioner sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0) :
    chainLinkResidual sourceActivation downstreamGain target
        (chainLinkPreconditionedPCUpdate preconditioner sourceActivation downstreamGain
          target weight) =
      (1 - preconditioner) *
        chainLinkResidual sourceActivation downstreamGain target weight := by
  unfold chainLinkPreconditionedPCUpdate
  rw [chainLinkNormalizedBackpropDirection_eq_residual_div_effectiveGain]
  unfold chainLinkResidual chainLinkPrediction
  have hdownstream : downstreamGain ≠ 0 := left_ne_zero_of_mul heffective
  have hsource : sourceActivation ≠ 0 := right_ne_zero_of_mul heffective
  field_simp [hdownstream, hsource]
  ring

/-- Exact post-update loss: the squared distance of the preconditioner from
identity is the loss contraction factor. -/
theorem chainLinkLoss_preconditionedUpdate_exact
    (preconditioner sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0) :
    chainLinkHalfSquaredLoss sourceActivation downstreamGain target
        (chainLinkPreconditionedPCUpdate preconditioner sourceActivation downstreamGain
          target weight) =
      (preconditioner - 1) ^ 2 *
        chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight := by
  unfold chainLinkHalfSquaredLoss
  rw [chainLinkResidual_preconditionedUpdate_exact preconditioner sourceActivation
    downstreamGain target weight heffective]
  ring

theorem chainLink_identityPreconditioner_reaches_zeroLoss
    (sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0) :
    chainLinkHalfSquaredLoss sourceActivation downstreamGain target
        (chainLinkPreconditionedPCUpdate 1 sourceActivation downstreamGain target weight) =
      0 := by
  rw [chainLinkLoss_preconditionedUpdate_exact 1 sourceActivation downstreamGain
    target weight heffective]
  ring

/-- Exact degradation relative to the identity-preconditioned BP step. -/
theorem chainLink_lossDecrease_gap_from_identity_exact
    (preconditioner sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0) :
    chainLinkLossDecrease 1 sourceActivation downstreamGain target weight -
        chainLinkLossDecrease preconditioner sourceActivation downstreamGain target weight =
      (preconditioner - 1) ^ 2 *
        chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight := by
  unfold chainLinkLossDecrease
  rw [chainLinkLoss_preconditionedUpdate_exact 1 sourceActivation downstreamGain
      target weight heffective,
    chainLinkLoss_preconditionedUpdate_exact preconditioner sourceActivation downstreamGain
      target weight heffective]
  ring

theorem chainLink_loss_pos_of_residual_ne_zero
    (sourceActivation downstreamGain target weight : ℝ)
    (hresidual :
      chainLinkResidual sourceActivation downstreamGain target weight ≠ 0) :
    0 < chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight := by
  unfold chainLinkHalfSquaredLoss
  positivity

/-- Among two scalar preconditioners, the one with larger squared departure
from identity removes strictly less loss whenever the initial residual is
nonzero. -/
theorem chainLink_lossDescent_strictly_degrades_with_squaredDeparture
    (near far sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0)
    (hresidual :
      chainLinkResidual sourceActivation downstreamGain target weight ≠ 0)
    (hdeparture : (near - 1) ^ 2 < (far - 1) ^ 2) :
    chainLinkLossDecrease far sourceActivation downstreamGain target weight <
      chainLinkLossDecrease near sourceActivation downstreamGain target weight := by
  have hnear := chainLink_lossDecrease_gap_from_identity_exact near sourceActivation
    downstreamGain target weight heffective
  have hfar := chainLink_lossDecrease_gap_from_identity_exact far sourceActivation
    downstreamGain target weight heffective
  have hloss := chainLink_loss_pos_of_residual_ne_zero sourceActivation downstreamGain
    target weight hresidual
  have hmul := mul_lt_mul_of_pos_right hdeparture hloss
  linarith

/-- Exact safe range for strict loss descent in the nontrivial scalar chain. -/
theorem chainLink_preconditionedUpdate_strictDescent_iff
    (preconditioner sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0)
    (hresidual :
      chainLinkResidual sourceActivation downstreamGain target weight ≠ 0) :
    chainLinkHalfSquaredLoss sourceActivation downstreamGain target
        (chainLinkPreconditionedPCUpdate preconditioner sourceActivation downstreamGain
          target weight) <
      chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight ↔
        0 < preconditioner ∧ preconditioner < 2 := by
  rw [chainLinkLoss_preconditionedUpdate_exact preconditioner sourceActivation
    downstreamGain target weight heffective]
  have hloss := chainLink_loss_pos_of_residual_ne_zero sourceActivation downstreamGain
    target weight hresidual
  constructor
  · intro h
    have hfactor : (preconditioner - 1) ^ 2 < 1 := by
      by_contra hnot
      have hge : 1 ≤ (preconditioner - 1) ^ 2 := le_of_not_gt hnot
      have hmul := mul_le_mul_of_nonneg_right hge (le_of_lt hloss)
      nlinarith
    constructor <;> nlinarith [sq_nonneg preconditioner]
  · intro hp
    have hfactor : (preconditioner - 1) ^ 2 < 1 := by
      nlinarith [sq_nonneg preconditioner]
    have hmul := mul_lt_mul_of_pos_right hfactor hloss
    nlinarith

/-- With a nonzero initial residual, one-step zero loss occurs exactly at the
identity-preconditioned BP update. -/
theorem chainLink_zeroLoss_afterUpdate_iff_identity
    (preconditioner sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0)
    (hresidual :
      chainLinkResidual sourceActivation downstreamGain target weight ≠ 0) :
    chainLinkHalfSquaredLoss sourceActivation downstreamGain target
        (chainLinkPreconditionedPCUpdate preconditioner sourceActivation downstreamGain
          target weight) = 0 ↔
      preconditioner = 1 := by
  rw [chainLinkLoss_preconditionedUpdate_exact preconditioner sourceActivation
    downstreamGain target weight heffective]
  have hlossne :
      chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight ≠ 0 :=
    ne_of_gt (chainLink_loss_pos_of_residual_ne_zero sourceActivation downstreamGain
      target weight hresidual)
  constructor
  · intro h
    have hsquare : (preconditioner - 1) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_right hlossne
    nlinarith [sq_eq_zero_iff.mp hsquare]
  · intro h
    subst preconditioner
    norm_num

/-! ## Exact positive and negative fixtures -/

theorem unitChain_identity_preconditioner_positive_example :
    chainLinkPreconditionedPCUpdate 1 1 1 2 0 = 2 ∧
      chainLinkHalfSquaredLoss 1 1 2
        (chainLinkPreconditionedPCUpdate 1 1 1 2 0) = 0 := by
  norm_num [chainLinkPreconditionedPCUpdate, chainLinkNormalizedBackpropDirection,
    chainLinkBackpropGradient, chainLinkCurvature, chainLinkHalfSquaredLoss,
    chainLinkResidual, chainLinkPrediction]

theorem unitChain_half_preconditioner_exact :
    chainLinkPreconditionedPCUpdate (1 / 2) 1 1 2 0 = 1 ∧
      chainLinkHalfSquaredLoss 1 1 2
        (chainLinkPreconditionedPCUpdate (1 / 2) 1 1 2 0) = 1 / 2 ∧
      chainLinkLossDecrease 1 1 1 2 0 -
        chainLinkLossDecrease (1 / 2) 1 1 2 0 = 1 / 2 := by
  norm_num [chainLinkPreconditionedPCUpdate, chainLinkNormalizedBackpropDirection,
    chainLinkBackpropGradient, chainLinkCurvature, chainLinkHalfSquaredLoss,
    chainLinkResidual, chainLinkPrediction, chainLinkLossDecrease]

/-- A scalar preconditioner outside the exact safe interval can increase the
loss, so preconditioning is not unconditionally beneficial. -/
theorem unitChain_large_preconditioner_increases_loss_negative_example :
    chainLinkHalfSquaredLoss 1 1 2
        (chainLinkPreconditionedPCUpdate 3 1 1 2 0) >
      chainLinkHalfSquaredLoss 1 1 2 0 := by
  norm_num [chainLinkPreconditionedPCUpdate, chainLinkNormalizedBackpropDirection,
    chainLinkBackpropGradient, chainLinkCurvature, chainLinkHalfSquaredLoss,
    chainLinkResidual, chainLinkPrediction]

/-! ## Matrix preconditioning of a genuine multiweight chain -/

/-- Euclidean residual/weight space for a chain with finitely many trainable
normal modes. -/
abbrev MultiweightChainSpace (width : ℕ) := EuclideanSpace ℝ (Fin width)

/-- The continuous Euclidean operator represented by a square real matrix. -/
noncomputable def matrixPreconditionerCLM {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ) :
    MultiweightChainSpace width →L[ℝ] MultiweightChainSpace width :=
  (Matrix.toEuclideanCLM (n := Fin width) (𝕜 := ℝ)) preconditioner

/-- The departure of a matrix preconditioner from the identity, acting on
whitened residual coordinates. -/
noncomputable def matrixPreconditionerDeparture {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ) :
    MultiweightChainSpace width →L[ℝ] MultiweightChainSpace width :=
  1 - matrixPreconditionerCLM preconditioner

/-- Residual remaining after one curvature-normalized, matrix-preconditioned
BP step. -/
noncomputable def matrixPreconditionedResidual {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ)
    (residual : MultiweightChainSpace width) : MultiweightChainSpace width :=
  matrixPreconditionerDeparture preconditioner residual

/-- Half-squared Euclidean loss carried by a vector residual. -/
noncomputable def multiweightResidualHalfSquaredLoss {width : ℕ}
    (residual : MultiweightChainSpace width) : ℝ :=
  ‖residual‖ ^ 2 / 2

/-- Residuals of a finite family of linear-chain modes.  Each coordinate has
its own effective gain, the product of the fixed upstream activation and
fixed downstream gains surrounding that trainable weight. -/
noncomputable def multiweightChainResidual {width : ℕ}
    (effectiveGain : Fin width → ℝ)
    (target weight : MultiweightChainSpace width) : MultiweightChainSpace width :=
  WithLp.toLp 2 fun i => effectiveGain i * weight i - target i

/-- Curvature-normalized BP direction before cross-mode preconditioning. -/
noncomputable def multiweightChainNormalizedBPDirection {width : ℕ}
    (effectiveGain : Fin width → ℝ)
    (target weight : MultiweightChainSpace width) : MultiweightChainSpace width :=
  WithLp.toLp 2 fun i => multiweightChainResidual effectiveGain target weight i /
    effectiveGain i

/-- Matrix-preconditioned PC control update in whitened residual coordinates.
The matrix first mixes the residual modes; division by each nonzero effective
gain transports that step back to its weight coordinate. -/
noncomputable def multiweightChainMatrixPCUpdate {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ)
    (effectiveGain : Fin width → ℝ)
    (target weight : MultiweightChainSpace width) : MultiweightChainSpace width :=
  let residual := multiweightChainResidual effectiveGain target weight
  let mixed := matrixPreconditionerCLM preconditioner residual
  WithLp.toLp 2 fun i => weight i - mixed i / effectiveGain i

noncomputable def multiweightChainHalfSquaredLoss {width : ℕ}
    (effectiveGain : Fin width → ℝ)
    (target weight : MultiweightChainSpace width) : ℝ :=
  multiweightResidualHalfSquaredLoss
    (multiweightChainResidual effectiveGain target weight)

/-- The multiweight chain's post-update residual is exactly `(I - P)r`.
This is the matrix analogue of the scalar factor `(1 - p)r`. -/
theorem multiweightChainResidual_matrixPCUpdate_exact {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ)
    (effectiveGain : Fin width → ℝ)
    (target weight : MultiweightChainSpace width)
    (hgain : ∀ i, effectiveGain i ≠ 0) :
    multiweightChainResidual effectiveGain target
        (multiweightChainMatrixPCUpdate preconditioner effectiveGain target weight) =
      matrixPreconditionedResidual preconditioner
        (multiweightChainResidual effectiveGain target weight) := by
  apply PiLp.ext
  intro i
  simp only [multiweightChainResidual, multiweightChainMatrixPCUpdate,
    matrixPreconditionedResidual, matrixPreconditionerDeparture,
    sub_apply, one_apply_eq_self, WithLp.ofLp_toLp, PiLp.sub_apply]
  field_simp [hgain i]
  ring

theorem multiweightChainLoss_matrixPCUpdate_exact {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ)
    (effectiveGain : Fin width → ℝ)
    (target weight : MultiweightChainSpace width)
    (hgain : ∀ i, effectiveGain i ≠ 0) :
    multiweightChainHalfSquaredLoss effectiveGain target
        (multiweightChainMatrixPCUpdate preconditioner effectiveGain target weight) =
      multiweightResidualHalfSquaredLoss
        (matrixPreconditionedResidual preconditioner
          (multiweightChainResidual effectiveGain target weight)) := by
  unfold multiweightChainHalfSquaredLoss
  rw [multiweightChainResidual_matrixPCUpdate_exact preconditioner effectiveGain
    target weight hgain]

/-- Operator-norm spectral bound: loss after the matrix-preconditioned step is
at most `‖I - P‖²` times the initial loss. -/
theorem matrixPreconditionedResidual_loss_operatorNorm_bound {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ)
    (residual : MultiweightChainSpace width) :
    multiweightResidualHalfSquaredLoss
        (matrixPreconditionedResidual preconditioner residual) ≤
      ‖matrixPreconditionerDeparture preconditioner‖ ^ 2 *
        multiweightResidualHalfSquaredLoss residual := by
  have hnorm := (matrixPreconditionerDeparture preconditioner).le_opNorm residual
  have hsq :
      ‖matrixPreconditionedResidual preconditioner residual‖ ^ 2 ≤
        (‖matrixPreconditionerDeparture preconditioner‖ * ‖residual‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
  unfold multiweightResidualHalfSquaredLoss
  nlinarith

theorem multiweightChainLoss_matrixPCUpdate_operatorNorm_bound {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ)
    (effectiveGain : Fin width → ℝ)
    (target weight : MultiweightChainSpace width)
    (hgain : ∀ i, effectiveGain i ≠ 0) :
    multiweightChainHalfSquaredLoss effectiveGain target
        (multiweightChainMatrixPCUpdate preconditioner effectiveGain target weight) ≤
      ‖matrixPreconditionerDeparture preconditioner‖ ^ 2 *
        multiweightChainHalfSquaredLoss effectiveGain target weight := by
  rw [multiweightChainLoss_matrixPCUpdate_exact preconditioner effectiveGain
    target weight hgain]
  exact matrixPreconditionedResidual_loss_operatorNorm_bound preconditioner
    (multiweightChainResidual effectiveGain target weight)

/-- Per-mode spectral law: an eigenmode of `P` with eigenvalue `λ` retains
exactly the squared loss factor `(λ - 1)²`. -/
theorem matrixPreconditionedResidual_loss_perMode_exact {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ)
    (residual : MultiweightChainSpace width) (eigenvalue : ℝ)
    (heigen : matrixPreconditionerCLM preconditioner residual =
      eigenvalue • residual) :
    multiweightResidualHalfSquaredLoss
        (matrixPreconditionedResidual preconditioner residual) =
      (eigenvalue - 1) ^ 2 * multiweightResidualHalfSquaredLoss residual := by
  have hdeparture : matrixPreconditionedResidual preconditioner residual =
      (1 - eigenvalue) • residual := by
    simp [matrixPreconditionedResidual, matrixPreconditionerDeparture, heigen,
      sub_smul]
  rw [hdeparture]
  unfold multiweightResidualHalfSquaredLoss
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Every realized eigenvalue departure is bounded by the departure
operator norm. -/
theorem matrixEigenvalue_departure_le_operatorNorm {width : ℕ}
    (preconditioner : Matrix (Fin width) (Fin width) ℝ)
    (residual : MultiweightChainSpace width) (eigenvalue : ℝ)
    (hresidual : residual ≠ 0)
    (heigen : matrixPreconditionerCLM preconditioner residual =
      eigenvalue • residual) :
    |1 - eigenvalue| ≤ ‖matrixPreconditionerDeparture preconditioner‖ := by
  have hdeparture : matrixPreconditionerDeparture preconditioner residual =
      (1 - eigenvalue) • residual := by
    simp [matrixPreconditionerDeparture, heigen, sub_smul]
  have hnorm := (matrixPreconditionerDeparture preconditioner).le_opNorm residual
  rw [hdeparture, norm_smul, Real.norm_eq_abs] at hnorm
  exact le_of_mul_le_mul_right hnorm (norm_pos_iff.mpr hresidual)

/-! ### Scalar recovery from the matrix theorem -/

noncomputable def scalarMatrixPreconditioner (p : ℝ) :
    Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => p

noncomputable def oneModeResidual (r : ℝ) : MultiweightChainSpace 1 :=
  WithLp.toLp 2 fun _ => r

theorem scalarMatrixPreconditioner_eigenpair (p r : ℝ) :
    matrixPreconditionerCLM (scalarMatrixPreconditioner p) (oneModeResidual r) =
      p • oneModeResidual r := by
  apply PiLp.ext
  intro i
  fin_cases i
  simp [matrixPreconditionerCLM, scalarMatrixPreconditioner, oneModeResidual,
    Matrix.mulVec, dotProduct]

theorem oneModeResidual_halfSquaredLoss_eq (r : ℝ) :
    multiweightResidualHalfSquaredLoss (oneModeResidual r) = r ^ 2 / 2 := by
  unfold multiweightResidualHalfSquaredLoss
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num [oneModeResidual, Fin.sum_univ_succ]

theorem oneMode_matrixPreconditionedResidual_eq (p r : ℝ) :
    matrixPreconditionedResidual (scalarMatrixPreconditioner p) (oneModeResidual r) =
      oneModeResidual ((1 - p) * r) := by
  unfold matrixPreconditionedResidual matrixPreconditionerDeparture
  rw [sub_apply, one_apply_eq_self, scalarMatrixPreconditioner_eigenpair]
  apply PiLp.ext
  intro i
  fin_cases i
  simp [oneModeResidual]
  ring

/-- The one-dimensional matrix theorem is exactly the scalar `(p - 1)²`
loss factor, rather than a separate analogue. -/
theorem oneMode_matrixLoss_recovers_scalarFactor (p r : ℝ) :
    multiweightResidualHalfSquaredLoss
        (matrixPreconditionedResidual (scalarMatrixPreconditioner p)
          (oneModeResidual r)) =
      (p - 1) ^ 2 * multiweightResidualHalfSquaredLoss (oneModeResidual r) := by
  exact matrixPreconditionedResidual_loss_perMode_exact
    (scalarMatrixPreconditioner p) (oneModeResidual r) p
    (scalarMatrixPreconditioner_eigenpair p r)

/-- The original collapsed-chain theorem follows by embedding its scalar
residual as the sole mode of the matrix theorem. -/
theorem chainLinkLoss_preconditionedUpdate_exact_matrixCorollary
    (preconditioner sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0) :
    chainLinkHalfSquaredLoss sourceActivation downstreamGain target
        (chainLinkPreconditionedPCUpdate preconditioner sourceActivation downstreamGain
          target weight) =
      (preconditioner - 1) ^ 2 *
        chainLinkHalfSquaredLoss sourceActivation downstreamGain target weight := by
  let residual := chainLinkResidual sourceActivation downstreamGain target weight
  have hpost := chainLinkResidual_preconditionedUpdate_exact preconditioner
    sourceActivation downstreamGain target weight heffective
  have hmatrix := oneMode_matrixLoss_recovers_scalarFactor preconditioner residual
  rw [oneMode_matrixPreconditionedResidual_eq,
    oneModeResidual_halfSquaredLoss_eq, oneModeResidual_halfSquaredLoss_eq] at hmatrix
  unfold chainLinkHalfSquaredLoss
  rw [hpost]
  exact hmatrix

/-! ### A matrix that helps one mode while hurting another -/

noncomputable def mixedModePreconditioner : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = j then if i.val = 0 then 1 / 2 else 3 else 0

noncomputable def twoModeUnitGain : Fin 2 → ℝ := fun _ => 1

noncomputable def twoModeZeroWeight : MultiweightChainSpace 2 :=
  WithLp.toLp 2 fun _ => 0

noncomputable def twoModeFirstTarget : MultiweightChainSpace 2 :=
  WithLp.toLp 2 fun i => if i.val = 0 then 1 else 0

noncomputable def twoModeSecondTarget : MultiweightChainSpace 2 :=
  WithLp.toLp 2 fun i => if i.val = 1 then 1 else 0

theorem mixedMode_firstResidual_eigenpair :
    matrixPreconditionerCLM mixedModePreconditioner
        (multiweightChainResidual twoModeUnitGain twoModeFirstTarget
          twoModeZeroWeight) =
      (1 / 2 : ℝ) •
        multiweightChainResidual twoModeUnitGain twoModeFirstTarget
          twoModeZeroWeight := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    norm_num [matrixPreconditionerCLM, mixedModePreconditioner,
      multiweightChainResidual, twoModeUnitGain, twoModeFirstTarget,
      twoModeZeroWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem mixedMode_secondResidual_eigenpair :
    matrixPreconditionerCLM mixedModePreconditioner
        (multiweightChainResidual twoModeUnitGain twoModeSecondTarget
          twoModeZeroWeight) =
      (3 : ℝ) •
        multiweightChainResidual twoModeUnitGain twoModeSecondTarget
          twoModeZeroWeight := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    norm_num [matrixPreconditionerCLM, mixedModePreconditioner,
      multiweightChainResidual, twoModeUnitGain, twoModeSecondTarget,
      twoModeZeroWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem twoMode_first_initialLoss :
    multiweightChainHalfSquaredLoss twoModeUnitGain twoModeFirstTarget
      twoModeZeroWeight = 1 / 2 := by
  unfold multiweightChainHalfSquaredLoss multiweightResidualHalfSquaredLoss
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  norm_num [multiweightChainResidual, twoModeUnitGain, twoModeFirstTarget,
    twoModeZeroWeight]

theorem twoMode_second_initialLoss :
    multiweightChainHalfSquaredLoss twoModeUnitGain twoModeSecondTarget
      twoModeZeroWeight = 1 / 2 := by
  unfold multiweightChainHalfSquaredLoss multiweightResidualHalfSquaredLoss
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  norm_num [multiweightChainResidual, twoModeUnitGain, twoModeSecondTarget,
    twoModeZeroWeight]

/-- One matrix improves its first eigenmode from loss `1/2` to `1/8`, but
overshoots its second eigenmode from `1/2` to `2`. -/
theorem mixedModePreconditioner_helps_one_hurts_another :
    multiweightChainHalfSquaredLoss twoModeUnitGain twoModeFirstTarget
        (multiweightChainMatrixPCUpdate mixedModePreconditioner twoModeUnitGain
          twoModeFirstTarget twoModeZeroWeight) = 1 / 8 ∧
      multiweightChainHalfSquaredLoss twoModeUnitGain twoModeSecondTarget
        (multiweightChainMatrixPCUpdate mixedModePreconditioner twoModeUnitGain
          twoModeSecondTarget twoModeZeroWeight) = 2 ∧
      multiweightChainHalfSquaredLoss twoModeUnitGain twoModeFirstTarget
          (multiweightChainMatrixPCUpdate mixedModePreconditioner twoModeUnitGain
            twoModeFirstTarget twoModeZeroWeight) <
        multiweightChainHalfSquaredLoss twoModeUnitGain twoModeFirstTarget
          twoModeZeroWeight ∧
      multiweightChainHalfSquaredLoss twoModeUnitGain twoModeSecondTarget
          twoModeZeroWeight <
        multiweightChainHalfSquaredLoss twoModeUnitGain twoModeSecondTarget
          (multiweightChainMatrixPCUpdate mixedModePreconditioner twoModeUnitGain
            twoModeSecondTarget twoModeZeroWeight) := by
  have hgain : ∀ i, twoModeUnitGain i ≠ 0 := by
    intro i
    norm_num [twoModeUnitGain]
  have hfirst := multiweightChainLoss_matrixPCUpdate_exact mixedModePreconditioner
    twoModeUnitGain twoModeFirstTarget twoModeZeroWeight hgain
  have hsecond := multiweightChainLoss_matrixPCUpdate_exact mixedModePreconditioner
    twoModeUnitGain twoModeSecondTarget twoModeZeroWeight hgain
  have hfirstInitial :
      multiweightResidualHalfSquaredLoss
        (multiweightChainResidual twoModeUnitGain twoModeFirstTarget
          twoModeZeroWeight) = 1 / 2 := by
    simpa [multiweightChainHalfSquaredLoss] using twoMode_first_initialLoss
  have hsecondInitial :
      multiweightResidualHalfSquaredLoss
        (multiweightChainResidual twoModeUnitGain twoModeSecondTarget
          twoModeZeroWeight) = 1 / 2 := by
    simpa [multiweightChainHalfSquaredLoss] using twoMode_second_initialLoss
  rw [matrixPreconditionedResidual_loss_perMode_exact mixedModePreconditioner
      _ (1 / 2) mixedMode_firstResidual_eigenpair,
    hfirstInitial] at hfirst
  rw [matrixPreconditionedResidual_loss_perMode_exact mixedModePreconditioner
      _ 3 mixedMode_secondResidual_eigenpair,
    hsecondInitial] at hsecond
  norm_num at hfirst hsecond
  rw [hfirst, hsecond, twoMode_first_initialLoss, twoMode_second_initialLoss]
  norm_num

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
