import Mettapedia.MachineLearning.ContinualLearning.QuadraticTwoTask
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Retention-safe finite updates

A first-order retention direction does not by itself certify that a finite
adapter update preserves an old task.  This file derives the Hilbert-space
descent lemma from a Lipschitz gradient, turns it into a finite trust-region
certificate, proves geometric backtracking termination, and records the
mandatory counterexample at a stationary point.  The scalar quadratic model
at the end is an exact fixture, not the scope of the main result.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

open scoped InnerProductSpace Interval NNReal
open MeasureTheory

/-! ## Smooth retention losses on an adapter space -/

/-- A differentiable replay/retention loss whose gradient is globally
`beta`-Lipschitz.  This is the usual analytic meaning of `beta`-smoothness;
the quadratic upper bound is derived below rather than stored as a field. -/
structure SmoothRetentionLoss
    (Adapter : Type*) [NormedAddCommGroup Adapter]
    [InnerProductSpace ℝ Adapter] [CompleteSpace Adapter]
    (beta : ℝ) where
  loss : Adapter → ℝ
  gradient : Adapter → Adapter
  beta_nonneg : 0 ≤ beta
  hasGradient : ∀ parameter,
    HasGradientAt loss (gradient parameter) parameter
  gradientLipschitz : ∀ x y,
    ‖gradient x - gradient y‖ ≤ beta * ‖x - y‖

variable {Adapter : Type*} [NormedAddCommGroup Adapter]
  [InnerProductSpace ℝ Adapter] [CompleteSpace Adapter]

theorem SmoothRetentionLoss.gradientContinuous
    {beta : ℝ} (model : SmoothRetentionLoss Adapter beta) :
    Continuous model.gradient := by
  apply (LipschitzWith.of_dist_le_mul (K := Real.toNNReal beta) ?_).continuous
  intro x y
  rw [Real.coe_toNNReal beta model.beta_nonneg]
  simpa [dist_eq_norm] using model.gradientLipschitz x y

/-- Along a finite adapter update, the loss difference is the integral of
the gradient paired with the update direction. -/
theorem smoothRetention_lineIntegral
    {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
    (parameter update : Adapter) :
    (∫ t : ℝ in (0 : ℝ)..1,
        ⟪model.gradient (parameter + t • update), update⟫_ℝ) =
      model.loss (parameter + update) - model.loss parameter := by
  let line : ℝ → Adapter := fun t => parameter + t • update
  have hline : ∀ t : ℝ, HasDerivAt line update t := by
    intro t
    simpa [line] using ((hasDerivAt_id t).smul_const update).const_add parameter
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s => model.loss (line s))
        ⟪model.gradient (line t), update⟫_ℝ t := by
    intro t
    simpa [Function.comp_def, line] using
      (model.hasGradient (line t)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hcontinuous : Continuous (fun t : ℝ =>
      ⟪model.gradient (line t), update⟫_ℝ) := by
    apply Continuous.inner
    · exact model.gradientContinuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))
    · exact continuous_const
  have hintegrable : IntervalIntegrable (fun t : ℝ =>
      ⟪model.gradient (line t), update⟫_ℝ) volume 0 1 :=
    hcontinuous.intervalIntegrable 0 1
  have hfundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun t => model.loss (line t))
    (f' := fun t => ⟪model.gradient (line t), update⟫_ℝ)
    (fun t _ => hderiv t) hintegrable
  simpa [line] using hfundamental

/-- Descent lemma for a genuinely `beta`-smooth replay/retention loss. -/
theorem smoothRetention_descentLemma
    {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
    (parameter update : Adapter) :
    model.loss (parameter + update) ≤ model.loss parameter +
      ⟪model.gradient parameter, update⟫_ℝ +
      beta / 2 * ‖update‖ ^ 2 := by
  have hactualIntegrable : IntervalIntegrable (fun t : ℝ =>
      ⟪model.gradient (parameter + t • update), update⟫_ℝ) volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.inner
    · exact model.gradientContinuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))
    · exact continuous_const
  have hupperIntegrable : IntervalIntegrable (fun t : ℝ =>
      ⟪model.gradient parameter, update⟫_ℝ +
        beta * t * ‖update‖ ^ 2) volume 0 1 := by
    exact (continuous_const.add
      ((continuous_const.mul continuous_id).mul continuous_const)).intervalIntegrable 0 1
  have hpointwise : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ⟪model.gradient (parameter + t • update), update⟫_ℝ ≤
        ⟪model.gradient parameter, update⟫_ℝ +
          beta * t * ‖update‖ ^ 2 := by
    intro t ht
    have hgradient := model.gradientLipschitz
      (parameter + t • update) parameter
    have hgradientNorm :
        ‖model.gradient (parameter + t • update) -
            model.gradient parameter‖ ≤ beta * ‖t • update‖ := by
      simpa using hgradient
    calc
      ⟪model.gradient (parameter + t • update), update⟫_ℝ =
          ⟪model.gradient parameter, update⟫_ℝ +
            ⟪model.gradient (parameter + t • update) -
              model.gradient parameter, update⟫_ℝ := by
                rw [← inner_add_left]
                congr 1
                abel
      _ ≤ ⟪model.gradient parameter, update⟫_ℝ +
            ‖model.gradient (parameter + t • update) -
              model.gradient parameter‖ * ‖update‖ :=
        add_le_add_right (real_inner_le_norm _ _) _
      _ ≤ ⟪model.gradient parameter, update⟫_ℝ +
            (beta * ‖t • update‖) * ‖update‖ :=
        add_le_add_right
          (mul_le_mul_of_nonneg_right hgradientNorm (norm_nonneg _)) _
      _ = ⟪model.gradient parameter, update⟫_ℝ +
            beta * t * ‖update‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        ring
  have hintegral := intervalIntegral.integral_mono_on
    (show (0 : ℝ) ≤ 1 by norm_num) hactualIntegrable hupperIntegrable hpointwise
  have hupper :
      (∫ t : ℝ in (0 : ℝ)..1,
          (⟪model.gradient parameter, update⟫_ℝ +
            beta * t * ‖update‖ ^ 2)) =
        ⟪model.gradient parameter, update⟫_ℝ +
          beta / 2 * ‖update‖ ^ 2 := by
    have hconstIntegrable : IntervalIntegrable
        (fun _ : ℝ => ⟪model.gradient parameter, update⟫_ℝ) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hlinearIntegrable : IntervalIntegrable
        (fun t : ℝ => beta * t * ‖update‖ ^ 2) volume 0 1 :=
      ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add hconstIntegrable hlinearIntegrable]
    simp only [intervalIntegral.integral_const, one_smul, sub_zero]
    rw [show (fun t : ℝ => beta * t * ‖update‖ ^ 2) =
        fun t => (beta * ‖update‖ ^ 2) * t by funext t; ring]
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
    ring
  rw [hupper] at hintegral
  rw [smoothRetention_lineIntegral model parameter update] at hintegral
  linarith

/-- A finite vector update is retention-safe when its first-order decrease
pays for the complete smoothness remainder. -/
def RetentionTrustRegionSafeVector
    (gradient : Adapter) (beta : ℝ) (update : Adapter) : Prop :=
  ⟪gradient, update⟫_ℝ + beta / 2 * ‖update‖ ^ 2 ≤ 0

theorem smoothRetention_nonincrease_of_trustRegion
    {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
    (parameter update : Adapter)
    (hsafe : RetentionTrustRegionSafeVector
      (model.gradient parameter) beta update) :
    model.loss (parameter + update) ≤ model.loss parameter := by
  have hdescent := smoothRetention_descentLemma model parameter update
  unfold RetentionTrustRegionSafeVector at hsafe
  linarith

omit [CompleteSpace Adapter] in
/- A checkable scale condition turns any proposed descent direction into a
finite retention-safe update. -/
theorem scaledDirection_retentionTrustRegionSafeVector
    (gradient direction : Adapter) (beta scale : ℝ)
    (hscale0 : 0 ≤ scale)
    (hbudget : scale * beta * ‖direction‖ ^ 2 ≤
      -2 * ⟪gradient, direction⟫_ℝ) :
    RetentionTrustRegionSafeVector gradient beta (scale • direction) := by
  unfold RetentionTrustRegionSafeVector
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale0]
  nlinarith [sq_nonneg scale]

theorem smoothRetention_scaledDirection_nonincrease
    {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
    (parameter direction : Adapter) (scale : ℝ)
    (hscale0 : 0 ≤ scale)
    (hbudget : scale * beta * ‖direction‖ ^ 2 ≤
      -2 * ⟪model.gradient parameter, direction⟫_ℝ) :
    model.loss (parameter + scale • direction) ≤ model.loss parameter := by
  apply smoothRetention_nonincrease_of_trustRegion model
  exact scaledDirection_retentionTrustRegionSafeVector _ _ _ _ hscale0 hbudget

/-- Geometric backtracking terminates for every strict retention descent
direction under positive smoothness. -/
theorem smoothRetention_backtracking_terminates
    {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
    (parameter direction : Adapter) (initial shrink : ℝ)
    (hbeta : 0 < beta)
    (hdescent : ⟪model.gradient parameter, direction⟫_ℝ < 0)
    (hinitial : 0 < initial)
    (hshrink0 : 0 < shrink) (hshrink1 : shrink < 1) :
    ∃ sweeps : ℕ,
      model.loss
          (parameter + (initial * shrink ^ sweeps) • direction) ≤
        model.loss parameter := by
  have hdirection : direction ≠ 0 := by
    intro hzero
    simp [hzero] at hdescent
  let threshold :=
    -2 * ⟪model.gradient parameter, direction⟫_ℝ /
      (beta * ‖direction‖ ^ 2)
  have hdenominator : 0 < beta * ‖direction‖ ^ 2 := by
    exact mul_pos hbeta (sq_pos_of_pos (norm_pos_iff.mpr hdirection))
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact div_pos (by linarith) hdenominator
  obtain ⟨sweeps, hsweeps⟩ :=
    exists_pow_lt_of_lt_one (div_pos hthreshold hinitial) hshrink1
  have hscaled : initial * shrink ^ sweeps < threshold := by
    have := (lt_div_iff₀ hinitial).mp hsweeps
    nlinarith
  refine ⟨sweeps, smoothRetention_scaledDirection_nonincrease
    model parameter direction (initial * shrink ^ sweeps) ?_ ?_⟩
  · exact mul_nonneg (le_of_lt hinitial) (le_of_lt (pow_pos hshrink0 sweeps))
  · change initial * shrink ^ sweeps <
      -2 * ⟪model.gradient parameter, direction⟫_ℝ /
        (beta * ‖direction‖ ^ 2) at hscaled
    have hmul := (lt_div_iff₀ hdenominator).mp hscaled
    linarith

/-! ## Exact scalar fixture -/

/-- Scalar quadratic replay/retention loss with curvature `beta`. -/
noncomputable def quadraticRetention
    (beta center parameter : ℝ) : ℝ :=
  beta / 2 * (parameter - center) ^ 2

/-- Gradient of `quadraticRetention`. -/
noncomputable def quadraticRetentionGradient
    (beta center parameter : ℝ) : ℝ :=
  beta * (parameter - center)

/-- Exact quadratic expansion.  This is the scalar `beta`-smooth descent
lemma with equality, rather than an assumed upper-bound certificate. -/
theorem quadraticRetention_update_exact
    (beta center parameter update : ℝ) :
    quadraticRetention beta center (parameter + update) =
      quadraticRetention beta center parameter +
        quadraticRetentionGradient beta center parameter * update +
        beta / 2 * update ^ 2 := by
  unfold quadraticRetention quadraticRetentionGradient
  ring

/-- The exact scalar model instantiates the usual smooth retention bound. -/
theorem quadraticRetention_descentLemma
    (beta center parameter update : ℝ) :
    quadraticRetention beta center (parameter + update) ≤
      quadraticRetention beta center parameter +
        quadraticRetentionGradient beta center parameter * update +
        beta / 2 * update ^ 2 := by
  rw [quadraticRetention_update_exact]

/-- A finite update is retention-safe when its first-order decrease pays for
the complete quadratic remainder. -/
def RetentionTrustRegionSafe
    (gradient beta update : ℝ) : Prop :=
  gradient * update + beta / 2 * update ^ 2 ≤ 0

theorem quadraticRetention_nonincrease_of_trustRegion
    (beta center parameter update : ℝ)
    (hsafe : RetentionTrustRegionSafe
      (quadraticRetentionGradient beta center parameter) beta update) :
    quadraticRetention beta center (parameter + update) ≤
      quadraticRetention beta center parameter := by
  rw [quadraticRetention_update_exact]
  unfold RetentionTrustRegionSafe at hsafe
  linarith

/-- A checkable radius condition for a scaled descent direction. -/
theorem scaledDirection_retentionTrustRegionSafe
    (gradient beta direction scale : ℝ)
    (hscale0 : 0 ≤ scale)
    (hbudget : scale * beta * direction ^ 2 ≤
      -2 * (gradient * direction)) :
    RetentionTrustRegionSafe gradient beta (scale * direction) := by
  unfold RetentionTrustRegionSafe
  nlinarith [sq_nonneg direction, sq_nonneg scale]

theorem quadraticRetention_scaledDirection_nonincrease
    (beta center parameter direction scale : ℝ)
    (hscale0 : 0 ≤ scale)
    (hbudget : scale * beta * direction ^ 2 ≤
      -2 * (quadraticRetentionGradient beta center parameter * direction)) :
    quadraticRetention beta center (parameter + scale * direction) ≤
      quadraticRetention beta center parameter := by
  apply quadraticRetention_nonincrease_of_trustRegion
  exact scaledDirection_retentionTrustRegionSafe _ _ _ _ hscale0 hbudget

/-! ## Geometric backtracking -/

/-- For a strict retention descent direction and positive curvature, geometric
backtracking eventually finds a finite update whose actual retention loss is
non-increasing. -/
theorem quadraticRetention_backtracking_terminates
    (beta center parameter direction initial shrink : ℝ)
    (hbeta : 0 < beta)
    (hdescent :
      quadraticRetentionGradient beta center parameter * direction < 0)
    (hinitial : 0 < initial)
    (hshrink0 : 0 < shrink) (hshrink1 : shrink < 1) :
    ∃ sweeps : ℕ,
      quadraticRetention beta center
          (parameter + (initial * shrink ^ sweeps) * direction) ≤
        quadraticRetention beta center parameter := by
  have hdirection : direction ≠ 0 := by
    intro hzero
    simp [hzero] at hdescent
  let threshold :=
    -2 * (quadraticRetentionGradient beta center parameter * direction) /
      (beta * direction ^ 2)
  have hdenominator : 0 < beta * direction ^ 2 := by
    exact mul_pos hbeta (sq_pos_of_ne_zero hdirection)
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact div_pos (by linarith) hdenominator
  obtain ⟨sweeps, hsweeps⟩ :=
    exists_pow_lt_of_lt_one (div_pos hthreshold hinitial) hshrink1
  have hscaled : initial * shrink ^ sweeps < threshold := by
    have := (lt_div_iff₀ hinitial).mp hsweeps
    nlinarith
  refine ⟨sweeps, quadraticRetention_scaledDirection_nonincrease
    beta center parameter direction (initial * shrink ^ sweeps) ?_ ?_⟩
  · exact mul_nonneg (le_of_lt hinitial) (le_of_lt (pow_pos hshrink0 sweeps))
  · change initial * shrink ^ sweeps <
      -2 * (quadraticRetentionGradient beta center parameter * direction) /
        (beta * direction ^ 2) at hscaled
    have hmul := (lt_div_iff₀ hdenominator).mp hscaled
    linarith

/-! ## Positive and negative fixtures -/

theorem quadraticRetention_descentStep_positive_example :
    quadraticRetention 1 0 (1 + (-1 : ℝ)) < quadraticRetention 1 0 1 := by
  norm_num [quadraticRetention]

/-- Directional safety at first order is insufficient at finite step size:
the old loss is stationary, so every direction has zero directional
derivative, yet a unit update strictly increases retention loss. -/
theorem directionalSafe_finiteStepIncrease_negative_example :
    quadraticRetentionGradient 1 0 0 * (1 : ℝ) ≤ 0 ∧
      quadraticRetention 1 0 (0 + 1) > quadraticRetention 1 0 0 := by
  norm_num [quadraticRetentionGradient, quadraticRetention]

/-- The counterexample fails the finite trust-region check, locating exactly
what the first-order test omitted. -/
theorem directionalSafe_counterexample_not_trustRegionSafe :
    ¬ RetentionTrustRegionSafe
      (quadraticRetentionGradient 1 0 0) 1 (1 : ℝ) := by
  norm_num [RetentionTrustRegionSafe, quadraticRetentionGradient]

end Mettapedia.MachineLearning.ContinualLearning
