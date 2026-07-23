import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ErrorCoordinateResidualSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LocalAmortizedInitialization
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FiniteSettlingGradientGap

/-!
# Regional contraction for error-coordinate settling

A one-point Hessian estimate is not a nonlinear convergence certificate.  This
file states the uniform two-point assumptions actually needed on a declared
closed ball, proves that the corresponding gradient step contracts and
preserves that ball, and then specializes the result to error-coordinate
predictive coding.

For a task gradient with negative-curvature budget `rho` and Lipschitz budget
`beta`, adding quadratic precision `p` gives regional strong monotonicity
`p - rho` and regional Lipschitz constant `p + beta`.  The resulting step is
contractive only under the explicit rate condition
`rate * (p + beta)^2 < 2 * (p - rho)`.  Equality `p = rho` is retained as a
negative fixture: the settling map can become the identity on a nontrivial
ball, so no strict local contraction certificate exists.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RegionalErrorCoordinateContraction

open scoped InnerProductSpace
open AmortizedInitialization
open ErrorCoordinateResidualSemantics
open LocalAmortizedInitialization
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-! ## Generic regional gradient contraction -/

/-- Uniform first-order data for a gradient field on one declared ball. -/
structure RegionalGradientCertificate
    (gradient : State → State) (center : State) (radius modulus lipschitz : ℝ) where
  radius_nonneg : 0 ≤ radius
  modulus_nonneg : 0 ≤ modulus
  lipschitz_nonneg : 0 ≤ lipschitz
  modulus_le_lipschitz : modulus ≤ lipschitz
  gradient_center_zero : gradient center = 0
  gradient_strongMonotone_on_ball : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    modulus * ‖left - right‖ ^ 2 ≤
      ⟪gradient left - gradient right, left - right⟫_ℝ
  gradient_lipschitz_on_ball : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖gradient left - gradient right‖ ≤
      lipschitz * ‖left - right‖

/-- One explicit gradient-settling sweep. -/
def regionalGradientStep
    (rate : ℝ) (gradient : State → State) (state : State) : State :=
  state - rate • gradient state

theorem regionalGradientStep_center_fixed
    {gradient : State → State} {center : State}
    {radius modulus lipschitz rate : ℝ}
    (certificate : RegionalGradientCertificate
      gradient center radius modulus lipschitz) :
    regionalGradientStep rate gradient center = center := by
  simp [regionalGradientStep, certificate.gradient_center_zero]

/-- The usual strong-monotonicity/Lipschitz calculation, restricted to the
declared region rather than promoted to a global statement. -/
theorem regionalGradientStep_sub_sq_le
    {gradient : State → State} {center : State}
    {radius modulus lipschitz rate : ℝ}
    (certificate : RegionalGradientCertificate
      gradient center radius modulus lipschitz)
    (hrate : 0 ≤ rate) (left right : State)
    (hleft : InClosedBall center radius left)
    (hright : InClosedBall center radius right) :
    ‖regionalGradientStep rate gradient left -
        regionalGradientStep rate gradient right‖ ^ 2 ≤
      hilbertSettlingContractionSq modulus lipschitz rate *
        ‖left - right‖ ^ 2 := by
  let difference := left - right
  let gradientDifference := gradient left - gradient right
  have hstep :
      regionalGradientStep rate gradient left -
          regionalGradientStep rate gradient right =
        difference - rate • gradientDifference := by
    dsimp [regionalGradientStep, difference, gradientDifference]
    module
  have hmono :
      modulus * ‖difference‖ ^ 2 ≤
        ⟪gradientDifference, difference⟫_ℝ :=
    certificate.gradient_strongMonotone_on_ball left right hleft hright
  have hlip :
      ‖gradientDifference‖ ≤ lipschitz * ‖difference‖ :=
    certificate.gradient_lipschitz_on_ball left right hleft hright
  have hlipSq :
      ‖gradientDifference‖ ^ 2 ≤
        (lipschitz * ‖difference‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg certificate.lipschitz_nonneg (norm_nonneg _))).2 hlip
  rw [hstep, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hrate, mul_pow]
  rw [real_inner_comm gradientDifference difference]
  unfold hilbertSettlingContractionSq
  nlinarith [mul_nonneg hrate (sub_nonneg.mpr hmono)]

/-- The square-root contraction coefficient is real under the intrinsic
`modulus ≤ lipschitz` boundary. -/
theorem regionalContractionSq_nonneg
    {gradient : State → State} {center : State}
    {radius modulus lipschitz rate : ℝ}
    (certificate : RegionalGradientCertificate
      gradient center radius modulus lipschitz) :
    0 ≤ hilbertSettlingContractionSq modulus lipschitz rate := by
  have hlip : 0 ≤ lipschitz := certificate.lipschitz_nonneg
  have hsq : modulus ^ 2 ≤ lipschitz ^ 2 :=
    (sq_le_sq₀ certificate.modulus_nonneg hlip).2
      certificate.modulus_le_lipschitz
  have hscaled :
      rate ^ 2 * modulus ^ 2 ≤ rate ^ 2 * lipschitz ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg rate)
  unfold hilbertSettlingContractionSq
  nlinarith [sq_nonneg (1 - rate * modulus)]

/-- Norm contraction on the declared region. -/
theorem regionalGradientStep_distance_le
    {gradient : State → State} {center : State}
    {radius modulus lipschitz rate : ℝ}
    (certificate : RegionalGradientCertificate
      gradient center radius modulus lipschitz)
    (hrate : 0 ≤ rate) (left right : State)
    (hleft : InClosedBall center radius left)
    (hright : InClosedBall center radius right) :
    ‖regionalGradientStep rate gradient left -
        regionalGradientStep rate gradient right‖ ≤
      hilbertSettlingContraction modulus lipschitz rate *
        ‖left - right‖ := by
  have hcoefficient := regionalContractionSq_nonneg certificate (rate := rate)
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (hilbertSettlingContraction_nonneg modulus lipschitz rate)
      (norm_nonneg _))).1
  rw [mul_pow, show hilbertSettlingContraction modulus lipschitz rate ^ 2 =
      hilbertSettlingContractionSq modulus lipschitz rate by
    exact Real.sq_sqrt hcoefficient]
  exact regionalGradientStep_sub_sq_le certificate hrate left right hleft hright

/-- A uniform regional gradient certificate plus the exact stable-rate
inequality yields the invariant local contraction needed by residual stopping
and amortized initialization. -/
noncomputable def RegionalGradientCertificate.toLocalContractionCertificate
    {gradient : State → State} {center : State}
    {radius modulus lipschitz rate : ℝ}
    (certificate : RegionalGradientCertificate
      gradient center radius modulus lipschitz)
    (hrate : 0 < rate)
    (hstable : rate * lipschitz ^ 2 < 2 * modulus) :
    LocalContractionCertificate
      (regionalGradientStep rate gradient) center radius where
  factor := hilbertSettlingContraction modulus lipschitz rate
  factor_nonneg := hilbertSettlingContraction_nonneg _ _ _
  factor_lt_one := hilbertSettlingContraction_lt_one
    modulus lipschitz rate hrate hstable
      (regionalContractionSq_nonneg certificate)
  radius_nonneg := certificate.radius_nonneg
  maps_ball := by
    intro state hstate
    have hcenter : InClosedBall center radius center := by
      simp [InClosedBall, certificate.radius_nonneg]
    have hpair := regionalGradientStep_distance_le certificate hrate.le
      state center hstate hcenter
    rw [regionalGradientStep_center_fixed certificate] at hpair
    calc
      ‖regionalGradientStep rate gradient state - center‖ ≤
          hilbertSettlingContraction modulus lipschitz rate *
            ‖state - center‖ := hpair
      _ ≤ hilbertSettlingContraction modulus lipschitz rate * radius := by
        exact mul_le_mul_of_nonneg_left hstate
          (hilbertSettlingContraction_nonneg _ _ _)
      _ ≤ radius := by
        have hfactor := hilbertSettlingContraction_lt_one
          modulus lipschitz rate hrate hstable
            (regionalContractionSq_nonneg certificate)
        nlinarith [certificate.radius_nonneg,
          hilbertSettlingContraction_nonneg modulus lipschitz rate]
  contracts_on_ball := by
    intro left right hleft hright
    exact regionalGradientStep_distance_le certificate hrate.le
      left right hleft hright

/-! ## Error-coordinate specialization -/

/-- The regional step is not a new solver: on error coordinates it is exactly
the zero-prediction specialization of the existing prospective gradient step. -/
theorem regionalErrorCoordinateStep_eq_prospective
    (precision rate : ℝ) (taskGradient : State → State) :
    regionalGradientStep rate
        (errorCoordinateEnergyGradient precision taskGradient) =
      ProspectiveResidualSemantics.prospectiveGradientStep
        0 precision rate taskGradient := by
  funext error
  simp [regionalGradientStep,
    errorCoordinateEnergyGradient_eq_prospective,
    ProspectiveResidualSemantics.prospectiveGradientStep]

/-- Uniform task-gradient evidence sufficient to certify regional
error-coordinate settling. -/
structure RegionalTaskGradientCertificate
    (precision rho beta : ℝ) (taskGradient : State → State)
    (center : State) (radius : ℝ) where
  rho_nonneg : 0 ≤ rho
  beta_nonneg : 0 ≤ beta
  radius_nonneg : 0 ≤ radius
  precision_dominates : rho < precision
  energy_stationary :
    errorCoordinateEnergyGradient precision taskGradient center = 0
  task_hypomonotone_on_ball : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    -(rho * ‖left - right‖ ^ 2) ≤
      ⟪taskGradient left - taskGradient right, left - right⟫_ℝ
  task_lipschitz_on_ball : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖taskGradient left - taskGradient right‖ ≤
      beta * ‖left - right‖

theorem RegionalTaskGradientCertificate.precision_pos
    {precision rho beta : ℝ} {taskGradient : State → State}
    {center : State} {radius : ℝ}
    (certificate : RegionalTaskGradientCertificate
      precision rho beta taskGradient center radius) :
    0 < precision :=
  lt_of_le_of_lt certificate.rho_nonneg certificate.precision_dominates

/-- Adding precision converts the task certificate into the generic regional
gradient certificate with exact constants `precision - rho` and
`precision + beta`. -/
noncomputable def RegionalTaskGradientCertificate.toRegionalGradientCertificate
    {precision rho beta : ℝ} {taskGradient : State → State}
    {center : State} {radius : ℝ}
    (certificate : RegionalTaskGradientCertificate
      precision rho beta taskGradient center radius) :
    RegionalGradientCertificate
      (errorCoordinateEnergyGradient precision taskGradient)
      center radius (precision - rho) (precision + beta) where
  radius_nonneg := certificate.radius_nonneg
  modulus_nonneg := sub_nonneg.mpr certificate.precision_dominates.le
  lipschitz_nonneg := add_nonneg certificate.precision_pos.le
    certificate.beta_nonneg
  modulus_le_lipschitz := by
    linarith [certificate.rho_nonneg, certificate.beta_nonneg]
  gradient_center_zero := certificate.energy_stationary
  gradient_strongMonotone_on_ball := by
    intro left right hleft hright
    have htask := certificate.task_hypomonotone_on_ball
      left right hleft hright
    have hrewrite :
        errorCoordinateEnergyGradient precision taskGradient left -
            errorCoordinateEnergyGradient precision taskGradient right =
          (taskGradient left - taskGradient right) +
            precision • (left - right) := by
      simp [errorCoordinateEnergyGradient, smul_sub]
      abel
    rw [hrewrite, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    nlinarith
  gradient_lipschitz_on_ball := by
    intro left right hleft hright
    have htask := certificate.task_lipschitz_on_ball
      left right hleft hright
    have hrewrite :
        errorCoordinateEnergyGradient precision taskGradient left -
            errorCoordinateEnergyGradient precision taskGradient right =
          (taskGradient left - taskGradient right) +
            precision • (left - right) := by
      simp [errorCoordinateEnergyGradient, smul_sub]
      abel
    rw [hrewrite]
    calc
      ‖(taskGradient left - taskGradient right) +
          precision • (left - right)‖ ≤
          ‖taskGradient left - taskGradient right‖ +
            ‖precision • (left - right)‖ := norm_add_le _ _
      _ ≤ beta * ‖left - right‖ +
          precision * ‖left - right‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos certificate.precision_pos]
        exact add_le_add htask le_rfl
      _ = (precision + beta) * ‖left - right‖ := by ring

/-- The directly usable local contraction certificate for regional
error-coordinate settling. -/
noncomputable def RegionalTaskGradientCertificate.toLocalContractionCertificate
    {precision rho beta : ℝ} {taskGradient : State → State}
    {center : State} {radius rate : ℝ}
    (certificate : RegionalTaskGradientCertificate
      precision rho beta taskGradient center radius)
    (hrate : 0 < rate)
    (hstable : rate * (precision + beta) ^ 2 <
      2 * (precision - rho)) :
    LocalContractionCertificate
      (regionalGradientStep rate
        (errorCoordinateEnergyGradient precision taskGradient))
      center radius :=
  certificate.toRegionalGradientCertificate.toLocalContractionCertificate
    hrate hstable

/-! ## Positive fixture: precision dominates mild negative curvature -/

def halfConcaveTaskGradient (error : ℝ) : ℝ := -(1 / 2) * error

noncomputable def halfConcaveRegionalCertificate :
    RegionalTaskGradientCertificate
      1 (1 / 2) (1 / 2) halfConcaveTaskGradient 0 1 where
  rho_nonneg := by norm_num
  beta_nonneg := by norm_num
  radius_nonneg := by norm_num
  precision_dominates := by norm_num
  energy_stationary := by
    norm_num [errorCoordinateEnergyGradient, halfConcaveTaskGradient]
  task_hypomonotone_on_ball := by
    intro left right _ _
    norm_num [halfConcaveTaskGradient, Real.norm_eq_abs, sq_abs]
    ring_nf
    exact le_rfl
  task_lipschitz_on_ball := by
    intro left right _ _
    rw [show halfConcaveTaskGradient left - halfConcaveTaskGradient right =
        -(1 / 2) * (left - right) by
      simp [halfConcaveTaskGradient]
      ring]
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    norm_num

noncomputable def halfConcaveLocalContraction :
    LocalContractionCertificate
      (regionalGradientStep (1 / 4)
        (errorCoordinateEnergyGradient 1 halfConcaveTaskGradient))
      0 1 :=
  halfConcaveRegionalCertificate.toLocalContractionCertificate
    (by norm_num) (by norm_num)

theorem halfConcave_step_exact (error : ℝ) :
    regionalGradientStep (1 / 4)
      (errorCoordinateEnergyGradient 1 halfConcaveTaskGradient) error =
        (7 / 8) * error := by
  simp [regionalGradientStep, errorCoordinateEnergyGradient,
    halfConcaveTaskGradient]
  ring

theorem halfConcave_iterates_stay_in_unitBall
    (initial : ℝ) (hinitial : InClosedBall 0 1 initial) (steps : ℕ) :
    InClosedBall 0 1
      ((regionalGradientStep (1 / 4)
        (errorCoordinateEnergyGradient 1 halfConcaveTaskGradient))^[steps]
          initial) :=
  iterate_mem_closedBall halfConcaveLocalContraction initial hinitial steps

/-! ## Sharp negative fixture: precision equals negative curvature -/

def criticalTaskGradient (error : ℝ) : ℝ := -error

theorem critical_energyGradient_zero (error : ℝ) :
    errorCoordinateEnergyGradient 1 criticalTaskGradient error = 0 := by
  simp [errorCoordinateEnergyGradient, criticalTaskGradient]

theorem critical_regionalStep_is_identity (rate : ℝ) :
    regionalGradientStep rate
      (errorCoordinateEnergyGradient 1 criticalTaskGradient) = id := by
  funext error
  simp [regionalGradientStep, critical_energyGradient_zero]

/-- At `precision = rho`, the identity settling map fixes both zero and one
inside the unit ball, so no strict local contraction certificate can exist. -/
theorem critical_noLocalContractionCertificate (rate : ℝ) :
    ¬ Nonempty
      (LocalContractionCertificate
        (regionalGradientStep rate
          (errorCoordinateEnergyGradient 1 criticalTaskGradient))
        0 1) := by
  rintro ⟨certificate⟩
  have hzeroMem : InClosedBall (0 : ℝ) 1 0 := by
    norm_num [InClosedBall]
  have honeMem : InClosedBall (0 : ℝ) 1 1 := by
    norm_num [InClosedBall]
  have hzeroFixed : IsFixedPoint
      (regionalGradientStep rate
        (errorCoordinateEnergyGradient 1 criticalTaskGradient)) 0 := by
    rw [critical_regionalStep_is_identity]
    rfl
  have honeFixed : IsFixedPoint
      (regionalGradientStep rate
        (errorCoordinateEnergyGradient 1 criticalTaskGradient)) 1 := by
    rw [critical_regionalStep_is_identity]
    rfl
  have hequal := fixedPoint_unique_in_closedBall certificate
    hzeroMem honeMem hzeroFixed honeFixed
  norm_num at hequal

#print axioms regionalGradientStep_sub_sq_le
#print axioms regionalContractionSq_nonneg
#print axioms RegionalGradientCertificate.toLocalContractionCertificate
#print axioms regionalErrorCoordinateStep_eq_prospective
#print axioms RegionalTaskGradientCertificate.toRegionalGradientCertificate
#print axioms RegionalTaskGradientCertificate.toLocalContractionCertificate
#print axioms halfConcave_step_exact
#print axioms halfConcave_iterates_stay_in_unitBall
#print axioms critical_noLocalContractionCertificate

end

end RegionalErrorCoordinateContraction

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
