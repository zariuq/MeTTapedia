import Mathlib

/-!
# Dual-timescale Lookahead updates

DualNet (Pham, Liu, and Hoi, arXiv:2110.00175, Equations (3)--(4))
trains a slow representation with `K` fast optimizer steps followed by a
Lookahead interpolation.  The update comes from Zhang, Lucas, Hinton, and Ba,
*Lookahead Optimizer: k steps forward, 1 step back*
(arXiv:1907.08610).

This file isolates the deterministic geometry shared by those updates.  A
fast endpoint is obtained by iterating an arbitrary step map.  The slow state
then moves a fraction `beta` toward that endpoint.  We prove:

* exact zero-, one-, and full-interpolation boundaries;
* preservation of every fixed point of the inner step;
* a `q ^ K` fast-endpoint error bound;
* the slow contraction factor `1 - beta + beta * q ^ K`;
* exact trajectories for affine contractions;
* strict improvement with additional inner steps under the load-bearing
  conditions `0 < beta` and `0 < q < 1`;
* an executable over-relaxation counterexample.

The results do not claim that a stochastic optimizer is contractive, that a
neural loss is convex, or that additional inner steps improve
work-normalized training.  Those premises must be established separately for
the concrete optimizer and cost model.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace DualTimescaleLookahead

noncomputable section

variable {State : Type*}

/-- Apply the fast optimizer step exactly `steps` times. -/
def fastIterate (step : State → State) : ℕ → State → State
  | 0, state => state
  | steps + 1, state => step (fastIterate step steps state)

@[simp]
theorem fastIterate_zero (step : State → State) (state : State) :
    fastIterate step 0 state = state := rfl

@[simp]
theorem fastIterate_succ (step : State → State) (steps : ℕ) (state : State) :
    fastIterate step (steps + 1) state =
      step (fastIterate step steps state) := rfl

section Module

variable [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- The slow update interpolates from its current state toward the endpoint
of `steps` fast updates. -/
def slowUpdate
    (beta : ℝ) (step : State → State) (steps : ℕ) (state : State) : State :=
  state + beta • (fastIterate step steps state - state)

/-- Zero fast steps leave the slow state unchanged. -/
@[simp]
theorem slowUpdate_zero_steps
    (beta : ℝ) (step : State → State) (state : State) :
    slowUpdate beta step 0 state = state := by
  simp [slowUpdate]

/-- Zero interpolation freezes the slow state even when the fast endpoint
differs. -/
@[simp]
theorem slowUpdate_zero_beta
    (step : State → State) (steps : ℕ) (state : State) :
    slowUpdate 0 step steps state = state := by
  simp [slowUpdate]

/-- Full interpolation selects the fast endpoint exactly. -/
@[simp]
theorem slowUpdate_one_beta
    (step : State → State) (steps : ℕ) (state : State) :
    slowUpdate 1 step steps state = fastIterate step steps state := by
  simp [slowUpdate]

/-- With one fast step, Lookahead is exactly a scaled version of that step's
displacement. -/
theorem slowUpdate_one_step
    (beta : ℝ) (step : State → State) (state : State) :
    slowUpdate beta step 1 state =
      state + beta • (step state - state) := by
  rfl

omit [NormedAddCommGroup State] [NormedSpace ℝ State] in
/-- An inner fixed point remains fixed after any number of fast steps. -/
theorem fastIterate_fixed
    (step : State → State) (fixed : State)
    (hfixed : step fixed = fixed) :
    ∀ steps, fastIterate step steps fixed = fixed
  | 0 => rfl
  | steps + 1 => by
      rw [fastIterate_succ, fastIterate_fixed step fixed hfixed steps, hfixed]

/-- Lookahead preserves every fixed point of the inner optimizer. -/
theorem slowUpdate_fixed
    (beta : ℝ) (step : State → State) (steps : ℕ) (fixed : State)
    (hfixed : step fixed = fixed) :
    slowUpdate beta step steps fixed = fixed := by
  rw [slowUpdate, fastIterate_fixed step fixed hfixed steps]
  simp

omit [NormedSpace ℝ State] in
/-- A pointwise contraction toward `fixed` compounds geometrically over the
fast trajectory. -/
theorem fastIterate_error_le
    (step : State → State) (fixed state : State) (q : ℝ)
    (q_nonneg : 0 ≤ q)
    (contracts : ∀ x, ‖step x - fixed‖ ≤ q * ‖x - fixed‖) :
    ∀ steps,
      ‖fastIterate step steps state - fixed‖ ≤
        q ^ steps * ‖state - fixed‖
  | 0 => by simp
  | steps + 1 => by
      calc
        ‖fastIterate step (steps + 1) state - fixed‖
            = ‖step (fastIterate step steps state) - fixed‖ := by
                rw [fastIterate_succ]
        _ ≤ q * ‖fastIterate step steps state - fixed‖ :=
          contracts _
        _ ≤ q * (q ^ steps * ‖state - fixed‖) :=
          mul_le_mul_of_nonneg_left
            (fastIterate_error_le step fixed state q q_nonneg contracts steps)
            q_nonneg
        _ = q ^ (steps + 1) * ‖state - fixed‖ := by
          rw [pow_succ]
          ring

/-- Scalar factor in the certified slow-state error bound. -/
def lookaheadRate (beta q : ℝ) (steps : ℕ) : ℝ :=
  1 - beta + beta * q ^ steps

/-- Exact displacement of the slow update from an arbitrary reference point. -/
theorem slowUpdate_sub_reference
    (beta : ℝ) (step : State → State) (steps : ℕ)
    (state reference : State) :
    slowUpdate beta step steps state - reference =
      (1 - beta) • (state - reference) +
        beta • (fastIterate step steps state - reference) := by
  unfold slowUpdate
  module

/-- Lookahead inherits a contraction certificate from the fast optimizer.
The interpolation must be a genuine convex interpolation. -/
theorem slowUpdate_error_le
    (beta q : ℝ) (step : State → State) (steps : ℕ)
    (fixed state : State)
    (beta_nonneg : 0 ≤ beta)
    (beta_le_one : beta ≤ 1)
    (q_nonneg : 0 ≤ q)
    (contracts : ∀ x, ‖step x - fixed‖ ≤ q * ‖x - fixed‖) :
    ‖slowUpdate beta step steps state - fixed‖ ≤
      lookaheadRate beta q steps * ‖state - fixed‖ := by
  rw [slowUpdate_sub_reference]
  calc
    ‖(1 - beta) • (state - fixed) +
        beta • (fastIterate step steps state - fixed)‖
        ≤ ‖(1 - beta) • (state - fixed)‖ +
            ‖beta • (fastIterate step steps state - fixed)‖ :=
      norm_add_le _ _
    _ = (1 - beta) * ‖state - fixed‖ +
          beta * ‖fastIterate step steps state - fixed‖ := by
      rw [norm_smul, norm_smul]
      simp only [Real.norm_eq_abs, abs_of_nonneg beta_nonneg,
        abs_of_nonneg (sub_nonneg.mpr beta_le_one)]
    _ ≤ (1 - beta) * ‖state - fixed‖ +
          beta * (q ^ steps * ‖state - fixed‖) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left
          (fastIterate_error_le step fixed state q q_nonneg contracts steps)
          beta_nonneg)
        _
    _ = lookaheadRate beta q steps * ‖state - fixed‖ := by
      unfold lookaheadRate
      ring

/-- The certified rate is nonnegative throughout the convex-interpolation,
nonexpansive-inner-step regime. -/
theorem lookaheadRate_nonneg
    (beta q : ℝ) (steps : ℕ)
    (beta_nonneg : 0 ≤ beta)
    (beta_le_one : beta ≤ 1)
    (q_nonneg : 0 ≤ q) :
    0 ≤ lookaheadRate beta q steps := by
  unfold lookaheadRate
  positivity

/-- A nonexpansive fast step yields a nonexpansive Lookahead rate. -/
theorem lookaheadRate_le_one
    (beta q : ℝ) (steps : ℕ)
    (beta_nonneg : 0 ≤ beta)
    (q_nonneg : 0 ≤ q)
    (q_le_one : q ≤ 1) :
    lookaheadRate beta q steps ≤ 1 := by
  have qpow_le_one : q ^ steps ≤ 1 := pow_le_one₀ q_nonneg q_le_one
  unfold lookaheadRate
  nlinarith

/-- A positive interpolation toward at least one genuinely contractive fast
step is itself genuinely contractive. -/
theorem lookaheadRate_lt_one
    (beta q : ℝ) (steps : ℕ)
    (beta_pos : 0 < beta)
    (q_nonneg : 0 ≤ q)
    (q_lt_one : q < 1)
    (steps_pos : 0 < steps) :
    lookaheadRate beta q steps < 1 := by
  have qpow_lt_one : q ^ steps < 1 :=
    pow_lt_one₀ q_nonneg q_lt_one (Nat.ne_of_gt steps_pos)
  unfold lookaheadRate
  nlinarith [mul_pos beta_pos (sub_pos.mpr qpow_lt_one)]

/-- Under a strictly positive inner contraction, each additional fast step
strictly improves the one-cycle certified rate. -/
theorem lookaheadRate_strictly_decreases
    (beta q : ℝ) (steps : ℕ)
    (beta_pos : 0 < beta)
    (q_pos : 0 < q)
    (q_lt_one : q < 1) :
    lookaheadRate beta q (steps + 1) <
      lookaheadRate beta q steps := by
  have qpow_pos : 0 < q ^ steps := pow_pos q_pos _
  have next_lt : q ^ steps * q < q ^ steps := by
    nlinarith
  unfold lookaheadRate
  rw [pow_succ]
  nlinarith

/-- The affine contraction toward `fixed` used for exact trajectory
fixtures. -/
def affineStep (fixed : State) (q : ℝ) (state : State) : State :=
  fixed + q • (state - fixed)

/-- Exact `K`-step endpoint for an affine contraction. -/
theorem fastIterate_affine
    (fixed state : State) (q : ℝ) :
    ∀ steps,
      fastIterate (affineStep fixed q) steps state =
        fixed + q ^ steps • (state - fixed)
  | 0 => by simp
  | steps + 1 => by
      rw [fastIterate_succ, fastIterate_affine fixed state q steps]
      unfold affineStep
      rw [pow_succ]
      module

/-- Exact slow update for an affine contraction. -/
theorem slowUpdate_affine
    (beta q : ℝ) (steps : ℕ) (fixed state : State) :
    slowUpdate beta (affineStep fixed q) steps state =
      fixed + lookaheadRate beta q steps • (state - fixed) := by
  rw [slowUpdate, fastIterate_affine]
  unfold lookaheadRate
  module

/-- Repeated slow cycles of an affine contraction compound the Lookahead
rate exactly. -/
theorem repeated_slowUpdate_affine
    (beta q : ℝ) (fastSteps slowCycles : ℕ) (fixed state : State) :
    fastIterate (slowUpdate beta (affineStep fixed q) fastSteps)
        slowCycles state =
      fixed +
        lookaheadRate beta q fastSteps ^ slowCycles • (state - fixed) := by
  have step_eq :
      slowUpdate beta (affineStep fixed q) fastSteps =
        affineStep fixed (lookaheadRate beta q fastSteps) := by
    funext x
    rw [slowUpdate_affine]
    rfl
  rw [step_eq, fastIterate_affine]

end Module

section Fixtures

/-- Two half-contraction fast steps followed by a half interpolation move
`1` exactly to `5/8`. -/
theorem half_contraction_two_step :
    slowUpdate (State := ℝ) (1 / 2)
        (affineStep 0 (1 / 2)) 2 1 = 5 / 8 := by
  norm_num [slowUpdate_affine, lookaheadRate]

/-- Positive inner work is wasted when the slow interpolation is zero. -/
theorem zero_interpolation_discards_fast_progress :
    fastIterate (fun _ : ℝ => 0) 1 1 = 0 ∧
      slowUpdate 0 (fun _ : ℝ => 0) 1 1 = 1 := by
  norm_num [fastIterate, slowUpdate]

/-- Convexity of the interpolation coefficient is load-bearing:
`beta = 3` turns the perfectly contractive map `x ↦ 0` into a factor-two
expansion. -/
theorem overrelaxation_can_expand :
    |slowUpdate (State := ℝ) 3 (fun _ => 0) 1 1| = 2 ∧
      |slowUpdate (State := ℝ) 3 (fun _ => 0) 1 1| > |(1 : ℝ)| := by
  norm_num [slowUpdate, fastIterate]

#print axioms slowUpdate_fixed
#print axioms fastIterate_error_le
#print axioms slowUpdate_error_le
#print axioms lookaheadRate_strictly_decreases
#print axioms repeated_slowUpdate_affine
#print axioms overrelaxation_can_expand

end Fixtures

end

end DualTimescaleLookahead

end Mettapedia.MachineLearning.ContinualLearning
