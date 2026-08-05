import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.PreconditionedFlowTransport

/-!
# Strict descent under the ePC chart metric

Goemaere, Oliviers, Bogacz, and Demeester, *ePC: Fast and Deep Predictive
Coding in Digital Simulation*, Appendix C.2, transport error-coordinate
gradient flow into state coordinates as

`stateVelocity = -(J J†) stateGradient`.

The source is pinned to arXiv:2505.20137v5, with PDF SHA-256
`2decd981f8fb4e24bfbcaea649f278703f60edd9e1f20041a342a3f70bb3142d`.

The existing chart-transport theory proves the exact formula and critical-point
correspondence.  This file closes the next analytic step: an invertible chart
makes `J J†` strictly positive definite, so the transported ePC flow has a
strictly negative directional derivative away from a critical point.

This is a pointwise descent theorem, not a global convergence theorem.  The
final fixture shows why that distinction is necessary: gradient descent on a
concave energy decreases the energy while moving away from its unique critical
point.  Global convergence therefore requires additional hypotheses such as
lower boundedness, compact sublevel sets, or an appropriate gradient
inequality.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped InnerProduct InnerProductSpace

open Frontier

section ChartDescent

variable {Error State : Type*}
variable [NormedAddCommGroup Error] [InnerProductSpace ℝ Error] [CompleteSpace Error]
variable [NormedAddCommGroup State] [InnerProductSpace ℝ State] [CompleteSpace State]

/-- The quadratic form induced by `J J†` is the squared norm of the
adjoint-pulled gradient. -/
theorem chartJJt_quadratic_eq_adjoint_norm_sq
    (jacobian : Error ≃L[ℝ] State) (stateGradient : State) :
    ⟪stateGradient, chartJJtApply jacobian stateGradient⟫_ℝ =
      ‖((jacobian : Error →L[ℝ] State)†) stateGradient‖ ^ 2 := by
  calc
    ⟪stateGradient, chartJJtApply jacobian stateGradient⟫_ℝ =
        ⟪stateGradient,
          (jacobian : Error →L[ℝ] State)
            (((jacobian : Error →L[ℝ] State)†) stateGradient)⟫_ℝ := rfl
    _ = ⟪((jacobian : Error →L[ℝ] State)†) stateGradient,
          ((jacobian : Error →L[ℝ] State)†) stateGradient⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_left
        (jacobian : Error →L[ℝ] State)
        (((jacobian : Error →L[ℝ] State)†) stateGradient)
        stateGradient).symm
    _ = ‖((jacobian : Error →L[ℝ] State)†) stateGradient‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

/-- Invertibility of the chart makes the induced metric strictly positive
away from the zero gradient. -/
theorem chartJJt_quadratic_pos
    (jacobian : Error ≃L[ℝ] State) (stateGradient : State)
    (hgradient : stateGradient ≠ 0) :
    0 < ⟪stateGradient, chartJJtApply jacobian stateGradient⟫_ℝ := by
  rw [chartJJt_quadratic_eq_adjoint_norm_sq]
  exact sq_pos_of_pos
    (norm_pos_iff.mpr
      ((chart_adjoint_apply_eq_zero_iff jacobian stateGradient).not.mpr hgradient))

/-- The `J J†`-preconditioned flow vanishes exactly at a state-energy critical
point. -/
theorem chartJJt_apply_eq_zero_iff
    (jacobian : Error ≃L[ℝ] State) (stateGradient : State) :
    chartJJtApply jacobian stateGradient = 0 ↔ stateGradient = 0 := by
  constructor
  · intro hzero
    have hadjoint :
        ((jacobian : Error →L[ℝ] State)†) stateGradient = 0 := by
      apply jacobian.injective
      simpa [chartJJtApply] using hzero
    exact (chart_adjoint_apply_eq_zero_iff jacobian stateGradient).mp hadjoint
  · rintro rfl
    simp [chartJJtApply]

/-- At a point with state gradient `g`, the derivative of the state energy
along the transported error-coordinate flow is exactly `-‖J†g‖²`. -/
theorem chart_pushed_errorFlow_fderiv_eq_neg_adjoint_norm_sq
    (energy : State → ℝ) (state : State) (stateGradient : State)
    (jacobian : Error ≃L[ℝ] State)
    (henergy : HasGradientAt energy stateGradient state) :
    fderiv ℝ energy state (-(chartJJtApply jacobian stateGradient)) =
      -‖((jacobian : Error →L[ℝ] State)†) stateGradient‖ ^ 2 := by
  rw [henergy.fderiv_apply, inner_neg_right,
    chartJJt_quadratic_eq_adjoint_norm_sq]

/-- Consequently the transported ePC flow is a strict state-energy descent
direction at every noncritical point. -/
theorem chart_pushed_errorFlow_strict_descent
    (energy : State → ℝ) (state : State) (stateGradient : State)
    (jacobian : Error ≃L[ℝ] State)
    (henergy : HasGradientAt energy stateGradient state)
    (hgradient : stateGradient ≠ 0) :
    fderiv ℝ energy state (-(chartJJtApply jacobian stateGradient)) < 0 := by
  rw [chart_pushed_errorFlow_fderiv_eq_neg_adjoint_norm_sq
    energy state stateGradient jacobian henergy]
  have hpositive :
      0 < ‖((jacobian : Error →L[ℝ] State)†) stateGradient‖ := by
    exact norm_pos_iff.mpr
      ((chart_adjoint_apply_eq_zero_iff jacobian stateGradient).not.mpr hgradient)
  nlinarith

end ChartDescent

/-! ## Boundary: strict descent does not imply global convergence -/

/-- A one-dimensional concave energy with a unique critical point at zero. -/
noncomputable def concaveEnergy (state : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * state ^ 2

/-- The exact increment formula identifies `-state` as the linear
coefficient, without appealing to an external derivative oracle. -/
theorem concaveEnergy_increment_exact (state increment : ℝ) :
    concaveEnergy (state + increment) - concaveEnergy state =
      increment * (-state) - (1 / 2 : ℝ) * increment ^ 2 := by
  simp [concaveEnergy]
  ring

/-- Zero is the only critical point of the concave energy. -/
theorem concaveEnergy_gradient_eq_zero_iff (state : ℝ) :
    -state = 0 ↔ state = 0 := by
  simp

/-- An exact unit gradient step from one to two strictly decreases the energy
while doubling the distance from the unique critical point.  Hence pointwise
descent alone cannot license the source's unrestricted global-convergence
sentence. -/
theorem concaveEnergy_descent_moves_away_from_critical_point :
    concaveEnergy 2 < concaveEnergy 1 ∧ |(1 : ℝ)| < |(2 : ℝ)| := by
  norm_num [concaveEnergy]

/-- Positive fixture: the identity chart induces the ordinary unit metric. -/
theorem identityChart_JJt_quadratic :
    ⟪(1 : ℝ),
      chartJJtApply (ContinuousLinearEquiv.refl ℝ ℝ) (1 : ℝ)⟫_ℝ = 1 := by
  norm_num [chartJJtApply]

#print axioms chart_pushed_errorFlow_strict_descent
#print axioms chartJJt_apply_eq_zero_iff
#print axioms concaveEnergy_descent_moves_away_from_critical_point

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
