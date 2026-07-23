import Mathlib.Analysis.Calculus.MeanValue
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LocalAmortizedInitialization

/-!
# Jacobian-remainder contraction for nonlinear credit solvers

A nonlinear settling map can be certified locally by separating its linearized
transport from its nonlinear remainder.  The first certificate below accepts a
direct pairwise Lipschitz budget for the remainder.  The second derives that
budget from a differentiable remainder whose Jacobian is Lipschitz away from a
zero-Jacobian expansion point.  In both cases the sum of the linear and
nonlinear factors must remain strictly below one on the declared ball.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace JacobianRemainderContraction

open AmortizedInitialization
open LocalAmortizedInitialization
open PrimalDualStability

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Nonlinear solver obtained by adding a linearized displacement and an exact
remainder to the expansion point. -/
noncomputable def linearRemainderSolver
    (center : State) (linear : State →L[ℝ] State)
    (remainder : State → State) (state : State) : State :=
  center + linear (state - center) + remainder state

/-- Direct norm budget for a linear map plus a locally Lipschitz remainder. -/
structure LinearRemainderBudget
    (linear : State →L[ℝ] State) (remainder : State → State)
    (center : State) (radius : ℝ) where
  linearFactor : ℝ
  remainderFactor : ℝ
  linearFactor_nonneg : 0 ≤ linearFactor
  remainderFactor_nonneg : 0 ≤ remainderFactor
  radius_nonneg : 0 ≤ radius
  totalFactor_lt_one : linearFactor + remainderFactor < 1
  linear_bound : ∀ displacement,
    ‖linear displacement‖ ≤ linearFactor * ‖displacement‖
  remainder_center_zero : remainder center = 0
  remainder_pair_bound : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖remainder left - remainder right‖ ≤
      remainderFactor * ‖left - right‖

theorem linearRemainderSolver_center_fixed
    {linear : State →L[ℝ] State} {remainder : State → State}
    {center : State} {radius : ℝ}
    (budget : LinearRemainderBudget linear remainder center radius) :
    IsFixedPoint (linearRemainderSolver center linear remainder) center := by
  simp [IsFixedPoint, linearRemainderSolver, budget.remainder_center_zero]

/-- Pairwise contraction follows by adding the independently audited linear
and remainder budgets. -/
theorem linearRemainderSolver_pair_distance_le
    {linear : State →L[ℝ] State} {remainder : State → State}
    {center : State} {radius : ℝ}
    (budget : LinearRemainderBudget linear remainder center radius)
    (left right : State)
    (hleft : InClosedBall center radius left)
    (hright : InClosedBall center radius right) :
    ‖linearRemainderSolver center linear remainder left -
        linearRemainderSolver center linear remainder right‖ ≤
      (budget.linearFactor + budget.remainderFactor) * ‖left - right‖ := by
  have hdecompose :
      linearRemainderSolver center linear remainder left -
          linearRemainderSolver center linear remainder right =
        linear (left - right) + (remainder left - remainder right) := by
    simp [linearRemainderSolver, map_sub]
    abel
  rw [hdecompose]
  calc
    ‖linear (left - right) + (remainder left - remainder right)‖ ≤
        ‖linear (left - right)‖ + ‖remainder left - remainder right‖ :=
      norm_add_le _ _
    _ ≤ budget.linearFactor * ‖left - right‖ +
          budget.remainderFactor * ‖left - right‖ :=
      add_le_add (budget.linear_bound _) (budget.remainder_pair_bound _ _ hleft hright)
    _ = (budget.linearFactor + budget.remainderFactor) * ‖left - right‖ := by
      ring

/-- The direct linear-plus-remainder budget yields a reusable local
contraction certificate, including preservation of the certified ball. -/
noncomputable def LinearRemainderBudget.toLocalContractionCertificate
    {linear : State →L[ℝ] State} {remainder : State → State}
    {center : State} {radius : ℝ}
    (budget : LinearRemainderBudget linear remainder center radius) :
    LocalContractionCertificate
      (linearRemainderSolver center linear remainder) center radius where
  factor := budget.linearFactor + budget.remainderFactor
  factor_nonneg := add_nonneg budget.linearFactor_nonneg
    budget.remainderFactor_nonneg
  factor_lt_one := budget.totalFactor_lt_one
  radius_nonneg := budget.radius_nonneg
  maps_ball := by
    intro state hstate
    have hcenter : InClosedBall center radius center := by
      simp [InClosedBall, budget.radius_nonneg]
    have hpair := linearRemainderSolver_pair_distance_le budget
      state center hstate hcenter
    rw [linearRemainderSolver_center_fixed budget] at hpair
    calc
      ‖linearRemainderSolver center linear remainder state - center‖ ≤
          (budget.linearFactor + budget.remainderFactor) *
            ‖state - center‖ := hpair
      _ ≤ (budget.linearFactor + budget.remainderFactor) * radius := by
        exact mul_le_mul_of_nonneg_left hstate
          (add_nonneg budget.linearFactor_nonneg budget.remainderFactor_nonneg)
      _ ≤ radius := by
        nlinarith [budget.totalFactor_lt_one, budget.radius_nonneg]
  contracts_on_ball := by
    intro left right hleft hright
    exact linearRemainderSolver_pair_distance_le budget left right hleft hright

/-- A Jacobian-Lipschitz remainder budget.  The remainder has zero Jacobian at
the expansion point, so a radial Jacobian Lipschitz constant `K` gives the
pairwise remainder factor `K * radius` on the convex closed ball. -/
structure JacobianLipschitzRemainderBudget
    (linear : State →L[ℝ] State) (remainder : State → State)
    (center : State) (radius : ℝ) where
  jacobianLipschitz : ℝ
  jacobianLipschitz_nonneg : 0 ≤ jacobianLipschitz
  radius_nonneg : 0 ≤ radius
  totalFactor_lt_one : ‖linear‖ + jacobianLipschitz * radius < 1
  remainder_center_zero : remainder center = 0
  remainder_differentiable : ∀ state,
    InClosedBall center radius state → DifferentiableAt ℝ remainder state
  remainderJacobian_center_zero : fderiv ℝ remainder center = 0
  remainderJacobian_radial_lipschitz : ∀ state,
    InClosedBall center radius state →
    ‖fderiv ℝ remainder state - fderiv ℝ remainder center‖ ≤
      jacobianLipschitz * ‖state - center‖

theorem remainder_fderiv_norm_le
    {linear : State →L[ℝ] State} {remainder : State → State}
    {center : State} {radius : ℝ}
    (budget : JacobianLipschitzRemainderBudget
      linear remainder center radius)
    (state : State) (hstate : InClosedBall center radius state) :
    ‖fderiv ℝ remainder state‖ ≤ budget.jacobianLipschitz * radius := by
  calc
    ‖fderiv ℝ remainder state‖ =
        ‖fderiv ℝ remainder state - fderiv ℝ remainder center‖ := by
      rw [budget.remainderJacobian_center_zero, sub_zero]
    _ ≤ budget.jacobianLipschitz * ‖state - center‖ :=
      budget.remainderJacobian_radial_lipschitz state hstate
    _ ≤ budget.jacobianLipschitz * radius :=
      mul_le_mul_of_nonneg_left hstate budget.jacobianLipschitz_nonneg

/-- Mean-value transport converts the Jacobian-radius bound into the pairwise
remainder bound required by the local solver certificate. -/
theorem remainder_pair_distance_le
    {linear : State →L[ℝ] State} {remainder : State → State}
    {center : State} {radius : ℝ}
    (budget : JacobianLipschitzRemainderBudget
      linear remainder center radius)
    (left right : State)
    (hleft : InClosedBall center radius left)
    (hright : InClosedBall center radius right) :
    ‖remainder left - remainder right‖ ≤
      (budget.jacobianLipschitz * radius) * ‖left - right‖ := by
  let ball : Set State := Metric.closedBall center radius
  have hleftBall : left ∈ ball := by
    simpa [ball, InClosedBall, Metric.mem_closedBall, dist_eq_norm]
      using hleft
  have hrightBall : right ∈ ball := by
    simpa [ball, InClosedBall, Metric.mem_closedBall, dist_eq_norm]
      using hright
  have hdifferentiable : ∀ state ∈ ball, DifferentiableAt ℝ remainder state := by
    intro state hstate
    exact budget.remainder_differentiable state
      (by simpa [ball, InClosedBall, Metric.mem_closedBall, dist_eq_norm]
        using hstate)
  have hderivative : ∀ state ∈ ball,
      ‖fderiv ℝ remainder state‖ ≤ budget.jacobianLipschitz * radius := by
    intro state hstate
    exact remainder_fderiv_norm_le budget state
      (by simpa [ball, InClosedBall, Metric.mem_closedBall, dist_eq_norm]
        using hstate)
  exact (convex_closedBall center radius).norm_image_sub_le_of_norm_fderiv_le
    hdifferentiable hderivative hrightBall hleftBall

/-- A Jacobian-Lipschitz remainder certificate generates the direct budget and
therefore an invariant local contraction. -/
noncomputable def JacobianLipschitzRemainderBudget.toLinearRemainderBudget
    {linear : State →L[ℝ] State} {remainder : State → State}
    {center : State} {radius : ℝ}
    (budget : JacobianLipschitzRemainderBudget
      linear remainder center radius) :
    LinearRemainderBudget linear remainder center radius where
  linearFactor := ‖linear‖
  remainderFactor := budget.jacobianLipschitz * radius
  linearFactor_nonneg := norm_nonneg _
  remainderFactor_nonneg := mul_nonneg budget.jacobianLipschitz_nonneg
    budget.radius_nonneg
  radius_nonneg := budget.radius_nonneg
  totalFactor_lt_one := budget.totalFactor_lt_one
  linear_bound := linear.le_opNorm
  remainder_center_zero := budget.remainder_center_zero
  remainder_pair_bound := remainder_pair_distance_le budget

noncomputable def JacobianLipschitzRemainderBudget.toLocalContractionCertificate
    {linear : State →L[ℝ] State} {remainder : State → State}
    {center : State} {radius : ℝ}
    (budget : JacobianLipschitzRemainderBudget
      linear remainder center radius) :
    LocalContractionCertificate
      (linearRemainderSolver center linear remainder) center radius :=
  budget.toLinearRemainderBudget.toLocalContractionCertificate

/-! ## Exact bridge to the scalar nonlinear PC fixture -/

noncomputable def quarterScalarLinear : ℝ →L[ℝ] ℝ :=
  (1 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ

noncomputable def scalarQuadraticRemainder (state : ℝ) : ℝ :=
  state ^ 2 / 4

theorem hasDerivAt_scalarQuadraticRemainder (state : ℝ) :
    HasDerivAt scalarQuadraticRemainder (state / 2) state := by
  convert (hasDerivAt_pow 2 state).div_const 4 using 1
  all_goals first | rfl | ring

theorem fderiv_scalarQuadraticRemainder (state : ℝ) :
    fderiv ℝ scalarQuadraticRemainder state =
      ContinuousLinearMap.toSpanSingleton ℝ (state / 2) :=
  (hasDerivAt_scalarQuadraticRemainder state).hasFDerivAt.fderiv

noncomputable def scalarQuadraticJacobianBudget :
    JacobianLipschitzRemainderBudget quarterScalarLinear
      scalarQuadraticRemainder 0 1 where
  jacobianLipschitz := 1 / 2
  jacobianLipschitz_nonneg := by norm_num
  radius_nonneg := by norm_num
  totalFactor_lt_one := by
    simp [quarterScalarLinear, norm_smul]
    norm_num
  remainder_center_zero := by norm_num [scalarQuadraticRemainder]
  remainder_differentiable := by
    intro state _
    exact (hasDerivAt_scalarQuadraticRemainder state).differentiableAt
  remainderJacobian_center_zero := by
    rw [fderiv_scalarQuadraticRemainder]
    norm_num
  remainderJacobian_radial_lipschitz := by
    intro state _
    rw [fderiv_scalarQuadraticRemainder,
      fderiv_scalarQuadraticRemainder]
    simp [Real.norm_eq_abs, div_eq_mul_inv, mul_comm]

theorem scalarLinearRemainderSolver_eq_localQuadraticErrorMap (state : ℝ) :
    linearRemainderSolver 0 quarterScalarLinear
      scalarQuadraticRemainder state = localQuadraticErrorMap state := by
  simp [linearRemainderSolver, quarterScalarLinear,
    scalarQuadraticRemainder, localQuadraticErrorMap,
    scalarQuadraticErrorMap]
  ring

theorem scalarJacobianCertificate_iterates_stay_in_unitBall
    (initial : ℝ) (hinitial : InClosedBall 0 1 initial) (steps : ℕ) :
    InClosedBall 0 1
      ((linearRemainderSolver 0 quarterScalarLinear
        scalarQuadraticRemainder)^[steps] initial) :=
  iterate_mem_closedBall
    scalarQuadraticJacobianBudget.toLocalContractionCertificate
    initial hinitial steps

/-! ## A genuinely two-coordinate nonlinear fixture -/

noncomputable def quarterPairLinear :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (1 / 4 : ℝ) • ContinuousLinearMap.id ℝ (ℝ × ℝ)

noncomputable def firstCoordinateQuadraticRemainder
    (state : ℝ × ℝ) : ℝ × ℝ :=
  (state.1 ^ 2 / 4, 0)

theorem quarterPairLinear_bound (state : ℝ × ℝ) :
    ‖quarterPairLinear state‖ ≤ (1 / 4 : ℝ) * ‖state‖ := by
  simp [quarterPairLinear, norm_smul]

theorem firstCoordinateQuadraticRemainder_pair_bound
    (left right : ℝ × ℝ)
    (hleft : InClosedBall (0, 0) 1 left)
    (hright : InClosedBall (0, 0) 1 right) :
    ‖firstCoordinateQuadraticRemainder left -
        firstCoordinateQuadraticRemainder right‖ ≤
      (1 / 2 : ℝ) * ‖left - right‖ := by
  have hleftFirst : |left.1| ≤ 1 := by
    have h := hleft
    simp only [InClosedBall, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
      sub_zero, max_le_iff] at h
    simpa [Real.norm_eq_abs] using h.1
  have hrightFirst : |right.1| ≤ 1 := by
    have h := hright
    simp only [InClosedBall, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
      sub_zero, max_le_iff] at h
    simpa [Real.norm_eq_abs] using h.1
  have hsum : |left.1 + right.1| ≤ 2 := by
    calc
      |left.1 + right.1| ≤ |left.1| + |right.1| := abs_add_le _ _
      _ ≤ 2 := by linarith
  have hfirstDiff : |left.1 - right.1| ≤ ‖left - right‖ := by
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
    exact le_max_left _ _
  have hfactor :
      |left.1 ^ 2 / 4 - right.1 ^ 2 / 4| ≤
        (1 / 2 : ℝ) * |left.1 - right.1| := by
    rw [show left.1 ^ 2 / 4 - right.1 ^ 2 / 4 =
        (left.1 - right.1) * (left.1 + right.1) / 4 by ring]
    rw [abs_div, abs_mul]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (left.1 - right.1))]
  calc
    ‖firstCoordinateQuadraticRemainder left -
        firstCoordinateQuadraticRemainder right‖ =
        |left.1 ^ 2 / 4 - right.1 ^ 2 / 4| := by
      simp [firstCoordinateQuadraticRemainder, Prod.norm_def]
    _ ≤ (1 / 2 : ℝ) * |left.1 - right.1| := hfactor
    _ ≤ (1 / 2 : ℝ) * ‖left - right‖ := by
      exact mul_le_mul_of_nonneg_left hfirstDiff (by norm_num)

noncomputable def pairNonlinearBudget :
    LinearRemainderBudget quarterPairLinear
      firstCoordinateQuadraticRemainder (0, 0) 1 where
  linearFactor := 1 / 4
  remainderFactor := 1 / 2
  linearFactor_nonneg := by norm_num
  remainderFactor_nonneg := by norm_num
  radius_nonneg := by norm_num
  totalFactor_lt_one := by norm_num
  linear_bound := quarterPairLinear_bound
  remainder_center_zero := by
    norm_num [firstCoordinateQuadraticRemainder]
  remainder_pair_bound := firstCoordinateQuadraticRemainder_pair_bound

theorem pairNonlinearSolver_zero_fixed :
    IsFixedPoint
      (linearRemainderSolver (0, 0) quarterPairLinear
        firstCoordinateQuadraticRemainder) (0, 0) :=
  linearRemainderSolver_center_fixed pairNonlinearBudget

theorem pairNonlinearSolver_iterates_stay_in_unitBall
    (initial : ℝ × ℝ) (hinitial : InClosedBall (0, 0) 1 initial)
    (steps : ℕ) :
    InClosedBall (0, 0) 1
      ((linearRemainderSolver (0, 0) quarterPairLinear
        firstCoordinateQuadraticRemainder)^[steps] initial) :=
  iterate_mem_closedBall
    pairNonlinearBudget.toLocalContractionCertificate initial hinitial steps

/-- Radius matters: two states inside the radius-two ball are moved farther
apart by one solver step. Thus the unit-ball certificate cannot be widened
merely from the contractive linearization at the origin. -/
theorem pairNonlinearSolver_expands_inside_radiusTwo :
    InClosedBall (0, 0) 2 ((2, 0) : ℝ × ℝ) ∧
    InClosedBall (0, 0) 2 (((3 / 2 : ℝ), 0) : ℝ × ℝ) ∧
    ‖linearRemainderSolver (0, 0) quarterPairLinear
          firstCoordinateQuadraticRemainder (2, 0) -
        linearRemainderSolver (0, 0) quarterPairLinear
          firstCoordinateQuadraticRemainder ((3 / 2 : ℝ), 0)‖ >
      ‖((2, 0) : ℝ × ℝ) - ((3 / 2 : ℝ), 0)‖ := by
  norm_num [InClosedBall, linearRemainderSolver, quarterPairLinear,
    firstCoordinateQuadraticRemainder, Prod.norm_def]

/-- The two-coordinate nonlinear solver is only local: outside the certified
unit ball, the first coordinate maps four to five. -/
theorem pairNonlinearSolver_globalExpansion :
    linearRemainderSolver (0, 0) quarterPairLinear
      firstCoordinateQuadraticRemainder (4, 0) = (5, 0) ∧
    ‖((4, 0) : ℝ × ℝ)‖ <
      ‖linearRemainderSolver (0, 0) quarterPairLinear
        firstCoordinateQuadraticRemainder (4, 0)‖ := by
  norm_num [linearRemainderSolver, quarterPairLinear,
    firstCoordinateQuadraticRemainder, Prod.norm_def]

#print axioms linearRemainderSolver_pair_distance_le
#print axioms LinearRemainderBudget.toLocalContractionCertificate
#print axioms remainder_pair_distance_le
#print axioms JacobianLipschitzRemainderBudget.toLocalContractionCertificate
#print axioms scalarJacobianCertificate_iterates_stay_in_unitBall
#print axioms pairNonlinearSolver_iterates_stay_in_unitBall
#print axioms pairNonlinearSolver_expands_inside_radiusTwo
#print axioms pairNonlinearSolver_globalExpansion

end JacobianRemainderContraction

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
