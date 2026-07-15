import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ZILExactness

/-!
# Backtracking descent for predictive-coding settling

This file proves termination and monotone energy descent for an Armijo
backtracking step, then instantiates the result for the existing scalar
depth-two predictive-coding energy.  The specialization is fully explicit:
its gradient has a positive Lipschitz constant, and its quadratic Taylor bound
is an equality.

The result also certifies the weaker fail-closed monotone acceptance rule used
by the running error-based predictive-coding experiment: every Armijo-accepted
step is non-increasing, and geometric shrinking eventually reaches one.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Scalar Armijo backtracking -/

/-- Armijo sufficient decrease for a scalar step along the negative gradient. -/
def armijoCondition (f : ℝ → ℝ) (x gradient c step : ℝ) : Prop :=
  f (x - step * gradient) ≤ f x - c * step * gradient ^ 2

/-- The standard smooth-gradient quadratic upper bound along one descent
direction. -/
def hasDescentUpperBoundAt
    (f : ℝ → ℝ) (x gradient L : ℝ) : Prop :=
  ∀ step, 0 ≤ step →
    f (x - step * gradient) ≤
      f x - step * gradient ^ 2 + (L / 2) * step ^ 2 * gradient ^ 2

theorem armijoCondition_of_descentUpperBound
    (f : ℝ → ℝ) (x gradient L c step : ℝ)
    (hL : 0 < L) (hstep0 : 0 ≤ step)
    (hstep : step ≤ 2 * (1 - c) / L)
    (hdescent : hasDescentUpperBoundAt f x gradient L) :
    armijoCondition f x gradient c step := by
  have hcoef : (L / 2) * step ≤ 1 - c := by
    rw [le_div_iff₀ hL] at hstep
    nlinarith
  have hnonneg : 0 ≤ step * gradient ^ 2 :=
    mul_nonneg hstep0 (sq_nonneg gradient)
  have hmul := mul_le_mul_of_nonneg_right hcoef hnonneg
  have hbound := hdescent step hstep0
  unfold armijoCondition
  nlinarith

/-- Repeated multiplication by a shrink factor below one eventually crosses
every positive threshold. -/
theorem geometric_backtracking_reaches_threshold
    (initial shrink threshold : ℝ)
    (hinitial : 0 < initial) (hshrink1 : shrink < 1)
    (hthreshold : 0 < threshold) :
    ∃ n : ℕ, initial * shrink ^ n < threshold := by
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one (div_pos hthreshold hinitial) hshrink1
  refine ⟨n, ?_⟩
  have hmul : shrink ^ n * initial < threshold :=
    (lt_div_iff₀ hinitial).mp hn
  nlinarith

/-- Geometric Armijo backtracking terminates under a smooth-gradient descent
bound. -/
theorem armijoBacktracking_terminates
    (f : ℝ → ℝ) (x gradient L c initial shrink : ℝ)
    (hL : 0 < L) (hc1 : c < 1)
    (hinitial : 0 < initial) (hshrink0 : 0 < shrink) (hshrink1 : shrink < 1)
    (hdescent : hasDescentUpperBoundAt f x gradient L) :
    ∃ n : ℕ, armijoCondition f x gradient c (initial * shrink ^ n) := by
  have hthreshold : 0 < 2 * (1 - c) / L := by positivity
  obtain ⟨n, hn⟩ := geometric_backtracking_reaches_threshold
    initial shrink (2 * (1 - c) / L) hinitial hshrink1 hthreshold
  refine ⟨n, armijoCondition_of_descentUpperBound f x gradient L c
    (initial * shrink ^ n) hL ?_ (le_of_lt hn) hdescent⟩
  exact mul_nonneg (le_of_lt hinitial) (le_of_lt (pow_pos hshrink0 n))

theorem armijoCondition_energy_nonincreasing
    (f : ℝ → ℝ) (x gradient c step : ℝ)
    (hc : 0 ≤ c) (hstep : 0 ≤ step)
    (haccept : armijoCondition f x gradient c step) :
    f (x - step * gradient) ≤ f x := by
  unfold armijoCondition at haccept
  have hnonneg : 0 ≤ c * step * gradient ^ 2 := by positivity
  linarith

/-! ## Exact smoothness of the depth-two PC energy -/

/-- Gradient of `pcDepth2Energy` with respect to its single free latent. -/
noncomputable def pcDepth2Gradient
    (x y gain₀ gain₁ precision₀ precision₁ z : ℝ) : ℝ :=
  2 * precision₀ * (z - gain₀ * x) -
    2 * precision₁ * gain₁ * (y - gain₁ * z)

/-- Exact Lipschitz constant of the depth-two latent gradient. -/
noncomputable def pcDepth2Smoothness
    (gain₁ precision₀ precision₁ : ℝ) : ℝ :=
  2 * (precision₀ + precision₁ * gain₁ ^ 2)

theorem pcDepth2Smoothness_pos
    (gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    0 < pcDepth2Smoothness gain₁ precision₀ precision₁ := by
  unfold pcDepth2Smoothness
  nlinarith [sq_nonneg gain₁]

theorem pcDepth2Gradient_sub
    (x y gain₀ gain₁ precision₀ precision₁ z w : ℝ) :
    pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z -
        pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ w =
      pcDepth2Smoothness gain₁ precision₀ precision₁ * (z - w) := by
  unfold pcDepth2Gradient pcDepth2Smoothness
  ring

/-- The depth-two PC gradient is exactly Lipschitz with the stated constant. -/
theorem pcDepth2Gradient_lipschitz_exact
    (x y gain₀ gain₁ precision₀ precision₁ z w : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    |pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z -
        pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ w| =
      pcDepth2Smoothness gain₁ precision₀ precision₁ * |z - w| := by
  rw [pcDepth2Gradient_sub]
  rw [abs_mul, abs_of_pos (pcDepth2Smoothness_pos gain₁ precision₀ precision₁
    hprecision₀ hprecision₁)]

/-- Exact quadratic expansion of one latent-gradient step. -/
theorem pcDepth2Energy_gradientStep_exact
    (x y gain₀ gain₁ precision₀ precision₁ z step : ℝ) :
    pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁
        (z - step * pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z) =
      pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁ z -
        step * (pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z) ^ 2 +
        (pcDepth2Smoothness gain₁ precision₀ precision₁ / 2) * step ^ 2 *
          (pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z) ^ 2 := by
  unfold pcDepth2Energy pcDepth2Gradient pcDepth2Smoothness
  ring

theorem pcDepth2_hasDescentUpperBoundAt
    (x y gain₀ gain₁ precision₀ precision₁ z : ℝ) :
    hasDescentUpperBoundAt
      (pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁)
      z (pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z)
      (pcDepth2Smoothness gain₁ precision₀ precision₁) := by
  intro step _hstep
  rw [pcDepth2Energy_gradientStep_exact]

/-- Every depth-two predictive-coding settle step finds an
Armijo-accepted geometric backtrack, and that accepted step cannot increase
the existing PC energy. -/
theorem pcEnergyDepth2_armijoBacktracking_terminates_with_descent
    (x y gain₀ gain₁ precision₀ precision₁ z c initial shrink : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hinitial : 0 < initial) (hshrink0 : 0 < shrink) (hshrink1 : shrink < 1) :
    ∃ n : ℕ,
      armijoCondition
        (pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁)
        z (pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z)
        c (initial * shrink ^ n) ∧
      pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁
          (z - (initial * shrink ^ n) *
            pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z) ≤
        pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁ z := by
  have hL := pcDepth2Smoothness_pos gain₁ precision₀ precision₁
    hprecision₀ hprecision₁
  obtain ⟨n, hn⟩ := armijoBacktracking_terminates
    (pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁) z
    (pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z)
    (pcDepth2Smoothness gain₁ precision₀ precision₁) c initial shrink
    hL hc1 hinitial hshrink0 hshrink1
    (pcDepth2_hasDescentUpperBoundAt x y gain₀ gain₁ precision₀ precision₁ z)
  refine ⟨n, hn, ?_⟩
  exact armijoCondition_energy_nonincreasing
    (pcDepth2Energy x y gain₀ gain₁ precision₀ precision₁) z
    (pcDepth2Gradient x y gain₀ gain₁ precision₀ precision₁ z) c
    (initial * shrink ^ n) hc0
    (mul_nonneg (le_of_lt hinitial) (le_of_lt (pow_pos hshrink0 n))) hn

/-! ## Accepted and rejected rate fixtures -/

theorem pcDepth2_unit_quarterStep_armijo_positive_example :
    armijoCondition (pcDepth2Energy 1 2 1 1 1 1) 0
      (pcDepth2Gradient 1 2 1 1 1 1 0) (1 / 2) (1 * (1 / 2) ^ 2) := by
  norm_num [armijoCondition, pcDepth2Energy, pcDepth2Gradient]

theorem pcDepth2_unit_quarterStep_strictly_decreases_energy :
    pcDepth2Energy 1 2 1 1 1 1
        (0 - (1 * (1 / 2) ^ 2) * pcDepth2Gradient 1 2 1 1 1 1 0) <
      pcDepth2Energy 1 2 1 1 1 1 0 := by
  norm_num [pcDepth2Energy, pcDepth2Gradient]

/-- The same fixture rejects the unshrunk initial rate, demonstrating that
backtracking performs real work rather than accepting every positive step. -/
theorem pcDepth2_unit_initialStep_rejected_negative_example :
    ¬ armijoCondition (pcDepth2Energy 1 2 1 1 1 1) 0
      (pcDepth2Gradient 1 2 1 1 1 1 0) (1 / 2) 1 := by
  norm_num [armijoCondition, pcDepth2Energy, pcDepth2Gradient]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
