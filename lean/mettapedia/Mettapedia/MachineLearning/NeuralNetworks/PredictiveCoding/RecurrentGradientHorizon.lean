import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.TemporalRTRLInfluence
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OptimizerTransport
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

/-!
# Recurrent-gradient horizon bounds

Pascanu, Mikolov, and Bengio, *On the difficulty of training Recurrent
Neural Networks* (2012), Equations (5)--(7), identify a long-range temporal
gradient contribution with an ordered product of recurrent Jacobians.  If
every Jacobian norm is uniformly bounded by `eta < 1`, the contribution
vanishes at least as fast as `eta ^ horizon`.

This file connects that source result to the arbitrary-horizon RTRL
formalization:

* nonuniform transport bounds multiply along a recurrent trace;
* a uniform subunit bound gives the source's exponential horizon bound;
* every family of length-`n` traces satisfying that bound converges to zero;
* failure to vanish rules out such a uniform contraction certificate;
* scalar fixtures separate vanishing, exploding, and a large local Jacobian
  followed by a zero transport.

The last fixture records the source's logical boundary: a large Jacobian norm
is necessary for some forms of explosion but is not by itself sufficient for
a particular temporal contribution to explode.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

namespace RecurrentGradientHorizon

open Filter
open scoped Topology
open scoped InnerProductSpace
open TemporalRTRLInfluence

noncomputable section

/-! ## Nonuniform products of Jacobian bounds -/

/-- Product of the declared recurrent-transport bounds along a chronological
trace. -/
def transportBoundProduct
    {Influence : Type*} [NormedAddCommGroup Influence]
    (steps : List (ApproximateInfluenceStep Influence)) : ℝ :=
  (steps.map ApproximateInfluenceStep.transportBound).prod

theorem transportBoundProduct_nonnegative
    {Influence : Type*} [NormedAddCommGroup Influence]
    (steps : List (ApproximateInfluenceStep Influence)) :
    0 ≤ transportBoundProduct steps := by
  induction steps with
  | nil =>
      simp [transportBoundProduct]
  | cons step rest inductionHypothesis =>
      simpa [transportBoundProduct] using
        mul_nonneg step.transportBound_nonneg inductionHypothesis

/-- The norm of the ordered recurrent-Jacobian product is bounded by the
product of its nonuniform local bounds. -/
theorem chronologicalTransport_norm_le
    {Influence : Type*} [NormedAddCommGroup Influence]
    (steps : List (ApproximateInfluenceStep Influence))
    (initial : Influence) :
    ‖chronologicalTransport (exactInfluenceSteps steps) initial‖ ≤
      transportBoundProduct steps * ‖initial‖ := by
  induction steps generalizing initial with
  | nil =>
      simp [chronologicalTransport, exactInfluenceSteps,
        transportBoundProduct]
  | cons step rest inductionHypothesis =>
      simp only [exactInfluenceSteps, List.map_cons,
        chronologicalTransport, AddMonoidHom.comp_apply,
        transportBoundProduct, List.prod_cons]
      calc
        ‖chronologicalTransport (exactInfluenceSteps rest)
            (step.exact.transport initial)‖ ≤
            transportBoundProduct rest *
              ‖step.exact.transport initial‖ :=
          inductionHypothesis _
        _ ≤ transportBoundProduct rest *
              (step.transportBound * ‖initial‖) :=
          mul_le_mul_of_nonneg_left
            (step.transport_norm_le initial)
            (transportBoundProduct_nonnegative rest)
        _ = step.transportBound *
              transportBoundProduct rest * ‖initial‖ := by
          ring

/-- A uniform per-step bound controls the complete nonuniform product. -/
theorem transportBoundProduct_le_pow
    {Influence : Type*} [NormedAddCommGroup Influence]
    (steps : List (ApproximateInfluenceStep Influence))
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (uniform :
      ∀ step ∈ steps, step.transportBound ≤ bound) :
    transportBoundProduct steps ≤ bound ^ steps.length := by
  induction steps with
  | nil =>
      simp [transportBoundProduct]
  | cons step rest inductionHypothesis =>
      have step_le : step.transportBound ≤ bound :=
        uniform step (by simp)
      have rest_uniform :
          ∀ later ∈ rest, later.transportBound ≤ bound := by
        intro later later_mem
        exact uniform later (by simp [later_mem])
      calc
        transportBoundProduct (step :: rest) =
            step.transportBound * transportBoundProduct rest := by
          simp [transportBoundProduct]
        _ ≤ bound * transportBoundProduct rest :=
          mul_le_mul_of_nonneg_right step_le
            (transportBoundProduct_nonnegative rest)
        _ ≤ bound * bound ^ rest.length :=
          mul_le_mul_of_nonneg_left
            (inductionHypothesis rest_uniform) bound_nonneg
        _ = bound ^ (step :: rest).length := by
          simp [pow_succ']

/-- Source Equation (7), generalized to nonuniform certified transports:
every length-`n` trace whose local bounds are at most `eta` contracts a
temporal influence by at most `eta ^ n`. -/
theorem uniform_chronologicalTransport_norm_le
    {Influence : Type*} [NormedAddCommGroup Influence]
    (steps : List (ApproximateInfluenceStep Influence))
    (eta : ℝ) (eta_nonneg : 0 ≤ eta)
    (uniform :
      ∀ step ∈ steps, step.transportBound ≤ eta)
    (initial : Influence) :
    ‖chronologicalTransport (exactInfluenceSteps steps) initial‖ ≤
      eta ^ steps.length * ‖initial‖ := by
  calc
    ‖chronologicalTransport (exactInfluenceSteps steps) initial‖ ≤
        transportBoundProduct steps * ‖initial‖ :=
      chronologicalTransport_norm_le steps initial
    _ ≤ eta ^ steps.length * ‖initial‖ :=
      mul_le_mul_of_nonneg_right
        (transportBoundProduct_le_pow steps eta eta_nonneg uniform)
        (norm_nonneg initial)

/-! ## Exponential vanishing and its contrapositive -/

/-- Any family of chronological traces whose length is the horizon and whose
transport bounds share a strict subunit upper bound has vanishing long-range
influence. -/
theorem chronologicalTransport_tendsto_zero
    {Influence : Type*} [NormedAddCommGroup Influence]
    (stepsAt : ℕ → List (ApproximateInfluenceStep Influence))
    (eta : ℝ) (eta_nonneg : 0 ≤ eta) (eta_lt_one : eta < 1)
    (length_eq : ∀ horizon, (stepsAt horizon).length = horizon)
    (uniform :
      ∀ horizon step, step ∈ stepsAt horizon →
        step.transportBound ≤ eta)
    (initial : Influence) :
    Tendsto
      (fun horizon =>
        chronologicalTransport
          (exactInfluenceSteps (stepsAt horizon)) initial)
      atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
  · intro horizon
    exact norm_nonneg _
  · intro horizon
    simpa [length_eq horizon] using
      uniform_chronologicalTransport_norm_le
        (stepsAt horizon) eta eta_nonneg
        (fun step step_mem => uniform horizon step step_mem)
        initial
  · have eta_abs_lt_one : |eta| < 1 := by
      rw [abs_of_nonneg eta_nonneg]
      exact eta_lt_one
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        eta_abs_lt_one).mul_const ‖initial‖

/-- Contrapositive boundary: a nonvanishing long-horizon contribution rules
out every uniform strict-contraction certificate for the declared trace
family. -/
theorem nonvanishing_forces_no_uniform_contraction
    {Influence : Type*} [NormedAddCommGroup Influence]
    (stepsAt : ℕ → List (ApproximateInfluenceStep Influence))
    (length_eq : ∀ horizon, (stepsAt horizon).length = horizon)
    (initial : Influence)
    (nonvanishing :
      ¬Tendsto
        (fun horizon =>
          chronologicalTransport
            (exactInfluenceSteps (stepsAt horizon)) initial)
        atTop (𝓝 0)) :
    ¬∃ eta : ℝ,
      0 ≤ eta ∧ eta < 1 ∧
        ∀ horizon step, step ∈ stepsAt horizon →
          step.transportBound ≤ eta := by
  rintro ⟨eta, eta_nonneg, eta_lt_one, uniform⟩
  exact nonvanishing
    (chronologicalTransport_tendsto_zero stepsAt eta eta_nonneg
      eta_lt_one length_eq uniform initial)

/-! ## Scalar positive and negative fixtures -/

/-- A zero-immediate scalar Jacobian with its exact norm certificate. -/
def scalarJacobianStep (jacobian : ℝ) :
    ApproximateInfluenceStep ℝ :=
  scalarApproximateInfluenceStep jacobian 0 0

theorem scalar_replicate_chronologicalTransport
    (jacobian initial : ℝ) (horizon : ℕ) :
    chronologicalTransport
        (exactInfluenceSteps
          (List.replicate horizon (scalarJacobianStep jacobian)))
        initial =
      jacobian ^ horizon * initial := by
  induction horizon generalizing initial with
  | zero =>
      simp [chronologicalTransport, exactInfluenceSteps]
  | succ horizon inductionHypothesis =>
      simp only [List.replicate_succ, exactInfluenceSteps, List.map_cons,
        chronologicalTransport, AddMonoidHom.comp_apply]
      change
        chronologicalTransport
            (exactInfluenceSteps
              (List.replicate horizon (scalarJacobianStep jacobian)))
            ((scalarJacobianStep jacobian).exact.transport initial) =
          jacobian ^ (horizon + 1) * initial
      rw [inductionHypothesis]
      simp [scalarJacobianStep, scalarApproximateInfluenceStep,
        scalarInfluenceStep, pow_succ']
      ring

/-- A half-Jacobian trace exhibits the source's exponential vanishing
mechanism exactly. -/
theorem half_jacobian_temporal_influence_tendsto_zero :
    Tendsto
      (fun horizon =>
        chronologicalTransport
          (exactInfluenceSteps
            (List.replicate horizon (scalarJacobianStep (1 / 2))))
          1)
      atTop (𝓝 0) := by
  have half_abs_lt_one : |(1 / 2 : ℝ)| < 1 := by
    norm_num
  simpa [scalar_replicate_chronologicalTransport] using
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one half_abs_lt_one

/-- A doubled scalar Jacobian exhibits exponential explosion. -/
theorem two_jacobian_temporal_influence_tendsto_atTop :
    Tendsto
      (fun horizon =>
        chronologicalTransport
          (exactInfluenceSteps
            (List.replicate horizon (scalarJacobianStep 2)))
          1)
      atTop atTop := by
  simpa [scalar_replicate_chronologicalTransport] using
    tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)

/-- A large local Jacobian does not by itself make a particular long-range
contribution explode: a later zero Jacobian erases it. -/
theorem large_then_zero_transport :
    chronologicalTransport
        (exactInfluenceSteps
          [scalarJacobianStep 2, scalarJacobianStep 0])
        1 = 0 ∧
      chronologicalTransport
        (exactInfluenceSteps [scalarJacobianStep 2])
        1 = 2 := by
  norm_num [chronologicalTransport, exactInfluenceSteps,
    scalarJacobianStep, scalarApproximateInfluenceStep,
    scalarInfluenceStep]

/-! ## Source Algorithm 1: positive global norm clipping -/

/-- Global norm clipping.  Below the threshold it is the identity; above the
threshold it rescales the complete gradient uniformly. -/
noncomputable def normClip
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    [NormedSpace ℝ Gradient]
    (threshold : ℝ) (gradient : Gradient) : Gradient :=
  if ‖gradient‖ ≤ threshold then
    gradient
  else
    (threshold / ‖gradient‖) • gradient

@[simp]
theorem normClip_eq_self_of_norm_le
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    [NormedSpace ℝ Gradient]
    (threshold : ℝ) (gradient : Gradient)
    (norm_le : ‖gradient‖ ≤ threshold) :
    normClip threshold gradient = gradient := by
  simp [normClip, norm_le]

/-- Above a positive threshold, clipping attains that threshold exactly. -/
theorem norm_normClip_eq_of_threshold_lt
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    [NormedSpace ℝ Gradient]
    (threshold : ℝ) (gradient : Gradient)
    (threshold_pos : 0 < threshold)
    (threshold_lt : threshold < ‖gradient‖) :
    ‖normClip threshold gradient‖ = threshold := by
  have gradientNorm_pos : 0 < ‖gradient‖ :=
    threshold_pos.trans threshold_lt
  unfold normClip
  rw [if_neg (not_le.mpr threshold_lt), norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos threshold_pos gradientNorm_pos),
    div_mul_cancel₀ threshold gradientNorm_pos.ne']

/-- The source's positive global clipping rule preserves every strictly
aligned gradient direction. -/
theorem normClip_preserves_positiveAlignment
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    [InnerProductSpace ℝ Gradient]
    (exact raw : Gradient) (threshold : ℝ)
    (threshold_pos : 0 < threshold)
    (alignment : 0 < ⟪exact, raw⟫_ℝ) :
    0 < ⟪exact, normClip threshold raw⟫_ℝ := by
  by_cases norm_le : ‖raw‖ ≤ threshold
  · simpa [normClip, norm_le] using alignment
  · rw [normClip, if_neg norm_le]
    apply Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OptimizerTransport.uniformClip_preserves_positiveAlignment
    · exact div_pos threshold_pos
        (threshold_pos.trans (lt_of_not_ge norm_le))
    · exact alignment

/-- Executable clipping routines commonly add a positive denominator
regularizer and clamp the resulting uniform scale at one.  This has the same
direction-preservation property as the source algorithm, but it need not
attain the threshold exactly. -/
noncomputable def epsilonNormClip
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    [NormedSpace ℝ Gradient]
    (threshold epsilon : ℝ) (gradient : Gradient) : Gradient :=
  min (threshold / (‖gradient‖ + epsilon)) 1 • gradient

theorem epsilonNormClip_scale_pos
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    (threshold epsilon : ℝ) (gradient : Gradient)
    (threshold_pos : 0 < threshold) (epsilon_pos : 0 < epsilon) :
    0 < min (threshold / (‖gradient‖ + epsilon)) 1 := by
  apply lt_min
  · exact div_pos threshold_pos
      (add_pos_of_nonneg_of_pos (norm_nonneg gradient) epsilon_pos)
  · norm_num

/-- A positive denominator regularizer still produces one strictly positive
uniform scale, so it cannot reverse a strictly aligned raw gradient. -/
theorem epsilonNormClip_preserves_positiveAlignment
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    [InnerProductSpace ℝ Gradient]
    (exact raw : Gradient) (threshold epsilon : ℝ)
    (threshold_pos : 0 < threshold) (epsilon_pos : 0 < epsilon)
    (alignment : 0 < ⟪exact, raw⟫_ℝ) :
    0 < ⟪exact, epsilonNormClip threshold epsilon raw⟫_ℝ := by
  apply
    Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.OptimizerTransport.uniformClip_preserves_positiveAlignment
      exact raw
  · exact epsilonNormClip_scale_pos threshold epsilon raw
      threshold_pos epsilon_pos
  · exact alignment

/-- The regularized executable form never exceeds its declared norm
threshold.  Unlike `normClip`, it can land strictly below the threshold. -/
theorem norm_epsilonNormClip_le
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    [NormedSpace ℝ Gradient]
    (threshold epsilon : ℝ) (gradient : Gradient)
    (threshold_pos : 0 < threshold) (epsilon_pos : 0 < epsilon) :
    ‖epsilonNormClip threshold epsilon gradient‖ ≤ threshold := by
  have denominator_pos : 0 < ‖gradient‖ + epsilon :=
    add_pos_of_nonneg_of_pos (norm_nonneg gradient) epsilon_pos
  have scale_pos :
      0 < min (threshold / (‖gradient‖ + epsilon)) 1 :=
    epsilonNormClip_scale_pos threshold epsilon gradient
      threshold_pos epsilon_pos
  calc
    ‖epsilonNormClip threshold epsilon gradient‖ =
        min (threshold / (‖gradient‖ + epsilon)) 1 * ‖gradient‖ := by
      rw [epsilonNormClip, norm_smul, Real.norm_eq_abs,
        abs_of_pos scale_pos]
    _ ≤ (threshold / (‖gradient‖ + epsilon)) * ‖gradient‖ :=
      mul_le_mul_of_nonneg_right
        (min_le_left _ _) (norm_nonneg gradient)
    _ ≤ threshold := by
      rw [div_mul_eq_mul_div, div_le_iff₀ denominator_pos]
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right epsilon_pos.le) threshold_pos.le

@[simp]
theorem epsilonNormClip_eq_self_of_norm_add_epsilon_le
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    [NormedSpace ℝ Gradient]
    (threshold epsilon : ℝ) (gradient : Gradient)
    (epsilon_pos : 0 < epsilon)
    (inactive : ‖gradient‖ + epsilon ≤ threshold) :
    epsilonNormClip threshold epsilon gradient = gradient := by
  have denominator_pos : 0 < ‖gradient‖ + epsilon :=
    add_pos_of_nonneg_of_pos (norm_nonneg gradient) epsilon_pos
  have one_le_scale :
      1 ≤ threshold / (‖gradient‖ + epsilon) := by
    rw [le_div_iff₀ denominator_pos]
    simpa using inactive
  simp [epsilonNormClip, min_eq_right one_le_scale]

/-- The denominator regularizer is semantically observable at the exact
threshold, so it must not be identified with the source's idealized clip. -/
theorem epsilonNormClip_boundary :
    epsilonNormClip 1 1 (1 : ℝ) = 1 / 2 ∧
      normClip 1 (1 : ℝ) = 1 := by
  norm_num [epsilonNormClip, normClip]

/-- Threshold zero is the sharp boundary: every gradient is collapsed to
zero, so strict alignment cannot survive. -/
theorem normClip_zero
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    [NormedSpace ℝ Gradient]
    (gradient : Gradient) :
    normClip 0 gradient = 0 := by
  by_cases norm_le : ‖gradient‖ ≤ 0
  · have gradientNorm_zero : ‖gradient‖ = 0 :=
      le_antisymm norm_le (norm_nonneg gradient)
    have gradient_zero : gradient = 0 :=
      norm_eq_zero.mp gradientNorm_zero
    simp [normClip, gradient_zero]
  · simp [normClip, norm_le]

theorem zero_threshold_destroys_strict_alignment :
    ¬0 < ⟪(1 : ℝ), normClip 0 (1 : ℝ)⟫_ℝ := by
  rw [normClip_zero]
  norm_num

#print axioms chronologicalTransport_norm_le
#print axioms transportBoundProduct_le_pow
#print axioms chronologicalTransport_tendsto_zero
#print axioms nonvanishing_forces_no_uniform_contraction
#print axioms half_jacobian_temporal_influence_tendsto_zero
#print axioms two_jacobian_temporal_influence_tendsto_atTop
#print axioms norm_normClip_eq_of_threshold_lt
#print axioms normClip_preserves_positiveAlignment
#print axioms epsilonNormClip_preserves_positiveAlignment
#print axioms norm_epsilonNormClip_le
#print axioms epsilonNormClip_boundary
#print axioms normClip_zero

end

end RecurrentGradientHorizon

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
