import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.HolomorphicPhase
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Continuous holomorphic phase readout

This module separates two obligations in holomorphic equilibrium credit.
First, Cauchy's derivative formula shows that a normalized continuous contour
readout extracts the derivative of any response that is complex differentiable
on the disk and continuous on its closure.  Second, a nontrivial scalar nudged
equilibrium is solved and differentiated independently, identifying that
response derivative with its task gradient.

The finite root-of-unity estimator remains a different object: it can alias
higher coefficients, whereas the continuous contour readout below does not.
The general nonlinear implicit-fixed-point derivative theorem is not claimed
here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances

open Complex Metric

universe uResponse

variable {Response : Type uResponse} [NormedAddCommGroup Response]
  [NormedSpace ℂ Response] [CompleteSpace Response]

/-- The normalized first contour coefficient of a complex response on a circle.
The explicit Cauchy kernel makes the required continuous-path oracle visible. -/
noncomputable def continuousFirstPhaseReadout
    (response : ℂ → Response) (radius : ℝ) : Response :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    (∮ beta in C(0, radius), (1 / (beta - 0) ^ 2) • response beta)

/-- Cauchy's derivative formula: an admissible continuous circular response
extracts the first derivative exactly at every positive radius inside its
declared regularity disk. -/
theorem continuousFirstPhaseReadout_eq_deriv
    (response : ℂ → Response) (radius : ℝ) (radius_pos : 0 < radius)
    (regular : DiffContOnCl ℂ response (ball 0 radius)) :
    continuousFirstPhaseReadout response radius = deriv response 0 := by
  unfold continuousFirstPhaseReadout
  rw [regular.deriv_eq_smul_circleIntegral radius_pos]
  rw [← mul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]

/-! ## A solved implicit-equilibrium instance -/

/-- A scalar holomorphic nudging problem. -/
structure ComplexScalarEPProblem where
  theta : ℂ
  target : ℂ

/-- The stationarity residual whose zero defines the nudged equilibrium. -/
def complexEPResidual
    (problem : ComplexScalarEPProblem) (beta state : ℂ) : ℂ :=
  (1 + beta) * state - (problem.theta + beta * problem.target)

/-- The unique nudged equilibrium away from the singular nudge `beta = -1`. -/
noncomputable def complexNudgedEquilibrium
    (problem : ComplexScalarEPProblem) (beta : ℂ) : ℂ :=
  (problem.theta + beta * problem.target) / (1 + beta)

/-- The parameter partial of the internal energy, evaluated at the nudged
equilibrium. -/
noncomputable def complexEquilibriumResponse
    (problem : ComplexScalarEPProblem) (beta : ℂ) : ℂ :=
  problem.theta - complexNudgedEquilibrium problem beta

/-- The task gradient at the free equilibrium. -/
def complexEPTaskGradient (problem : ComplexScalarEPProblem) : ℂ :=
  problem.theta - problem.target

/-- The closed-form state genuinely solves the declared implicit residual. -/
theorem complexNudgedEquilibrium_residual_zero
    (problem : ComplexScalarEPProblem) (beta : ℂ)
    (denominator_ne : 1 + beta ≠ 0) :
    complexEPResidual problem beta
      (complexNudgedEquilibrium problem beta) = 0 := by
  unfold complexEPResidual complexNudgedEquilibrium
  field_simp [denominator_ne]
  ring

/-- Away from the singular nudge, the declared residual has no other scalar
equilibrium. -/
theorem complexNudgedEquilibrium_unique
    (problem : ComplexScalarEPProblem) (beta state : ℂ)
    (denominator_ne : 1 + beta ≠ 0)
    (residual_zero : complexEPResidual problem beta state = 0) :
    state = complexNudgedEquilibrium problem beta := by
  unfold complexEPResidual at residual_zero
  unfold complexNudgedEquilibrium
  apply (eq_div_iff denominator_ne).2
  rw [mul_comm]
  exact sub_eq_zero.mp residual_zero

/-- The derivative of the independently solved equilibrium response is the
task gradient. -/
theorem complexEquilibriumResponse_hasDerivAt
    (problem : ComplexScalarEPProblem) :
    HasDerivAt
      (fun beta : ℂ =>
        problem.theta -
          (problem.theta + beta * problem.target) / (1 + beta))
      (problem.theta - problem.target) 0 := by
  have numerator_deriv :
      HasDerivAt (fun beta : ℂ => problem.theta + beta * problem.target)
        problem.target 0 := by
    simpa only [one_mul] using
      ((hasDerivAt_id' (𝕜 := ℂ) 0).mul_const problem.target).const_add problem.theta
  have denominator_deriv :
      HasDerivAt (fun beta : ℂ => 1 + beta) 1 0 := by
    simpa only using (hasDerivAt_id' (𝕜 := ℂ) 0).const_add (1 : ℂ)
  have response_deriv :=
    (numerator_deriv.div denominator_deriv (by norm_num)).const_sub problem.theta
  simpa only [Pi.div_apply, mul_one, zero_mul, add_zero, one_pow, div_one,
    neg_sub] using response_deriv

/-- The derivative statement for the named response, separated from its
closed-form differentiation proof. -/
theorem deriv_complexEquilibriumResponse
    (problem : ComplexScalarEPProblem) :
    deriv (complexEquilibriumResponse problem) 0 =
      complexEPTaskGradient problem := by
  change
    deriv
        (fun beta : ℂ =>
          problem.theta -
            (problem.theta + beta * problem.target) / (1 + beta))
        0 =
      problem.theta - problem.target
  exact (complexEquilibriumResponse_hasDerivAt problem).deriv

/-- Every contour of radius strictly below one avoids the unique singular
nudge, so the solved response is differentiable on the disk and continuous on
its closure. -/
theorem complexEquilibriumResponse_diffContOnCl
    (problem : ComplexScalarEPProblem) {radius : ℝ}
    (radius_lt_one : radius < 1) :
    DiffContOnCl ℂ (complexEquilibriumResponse problem) (ball 0 radius) := by
  unfold complexEquilibriumResponse complexNudgedEquilibrium
  apply DifferentiableOn.diffContOnCl_ball
      (U := {beta : ℂ | 1 + beta ≠ 0})
  · intro beta denominator_ne
    have numerator_differentiable :
        DifferentiableAt ℂ
          (fun beta : ℂ => problem.theta + beta * problem.target) beta := by
      simpa only [Function.id_def] using
        ((differentiableAt_id (𝕜 := ℂ) (E := ℂ)).mul_const problem.target).const_add
          problem.theta
    have denominator_differentiable :
        DifferentiableAt ℂ (fun beta : ℂ => 1 + beta) beta := by
      simpa only [Function.id_def] using
        (differentiableAt_id (𝕜 := ℂ) (E := ℂ)).const_add (1 : ℂ)
    exact
      (numerator_differentiable.div denominator_differentiable denominator_ne).const_sub
        problem.theta |>.differentiableWithinAt
  · intro beta beta_mem denominator_zero
    have beta_norm : ‖beta‖ ≤ radius := by
      simpa [mem_closedBall] using beta_mem
    have beta_eq : beta = -1 := eq_neg_of_add_eq_zero_right denominator_zero
    rw [beta_eq] at beta_norm
    norm_num at beta_norm
    linarith

/-- The continuous phase readout of the solved implicit equilibrium equals its
task gradient at any positive radius below the singularity. -/
theorem continuousReadout_complexEquilibrium_eq_taskGradient
    (problem : ComplexScalarEPProblem) {radius : ℝ}
    (radius_pos : 0 < radius) (radius_lt_one : radius < 1) :
    continuousFirstPhaseReadout (complexEquilibriumResponse problem) radius =
      complexEPTaskGradient problem := by
  rw [continuousFirstPhaseReadout_eq_deriv _ _ radius_pos
    (complexEquilibriumResponse_diffContOnCl problem radius_lt_one)]
  exact deriv_complexEquilibriumResponse problem

/-! ## Concrete positive and negative boundaries -/

def concreteComplexEPProblem : ComplexScalarEPProblem where
  theta := 2
  target := -1

/-- A radius-one-half contour extracts the exact task gradient `3` from the
implicit equilibrium response. -/
theorem concrete_continuousReadout_recovers_gradient :
    continuousFirstPhaseReadout
      (complexEquilibriumResponse concreteComplexEPProblem) (1 / 2) = 3 := by
  rw [continuousReadout_complexEquilibrium_eq_taskGradient
    concreteComplexEPProblem (by norm_num) (by norm_num)]
  norm_num [complexEPTaskGradient, concreteComplexEPProblem]

/-- A contour crossing the pole at `beta = -1` violates the admissibility
premise: the response denominator vanishes at a point of the closed disk. -/
theorem radius_two_contains_singular_nudge :
    (-1 : ℂ) ∈ closedBall 0 2 ∧
      (1 + (-1 : ℂ)) = 0 := by
  constructor <;> norm_num [mem_closedBall]

#print axioms continuousFirstPhaseReadout_eq_deriv
#print axioms complexNudgedEquilibrium_residual_zero
#print axioms complexNudgedEquilibrium_unique
#print axioms complexEquilibriumResponse_hasDerivAt
#print axioms deriv_complexEquilibriumResponse
#print axioms complexEquilibriumResponse_diffContOnCl
#print axioms continuousReadout_complexEquilibrium_eq_taskGradient
#print axioms concrete_continuousReadout_recovers_gradient
#print axioms radius_two_contains_singular_nudge

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances
