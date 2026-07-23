import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.JacobianRemainderContraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegionalErrorCoordinateContraction

/-!
# Regional certificates from a linearization and a derivative enclosure

A Hessian or Jacobian computed at one point is not a regional convergence
certificate.  This file isolates the additional datum that is needed: a
uniform bound on the nonlinear remainder, or equivalently a uniform enclosure
of the Jacobian around an audited linear map on a declared ball.

The central linear map supplies a strong-monotonicity margin.  The nonlinear
variation spends that margin.  Only a strict positive remainder survives as a
regional modulus, and the total Lipschitz constant includes both pieces.  The
result feeds the existing regional error-coordinate contraction theorem.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RegionalLinearizationCertificate

open scoped InnerProductSpace
open AmortizedInitialization
open JacobianRemainderContraction
open LocalAmortizedInitialization
open RegionalErrorCoordinateContraction
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- The exact nonlinear part left after subtracting one affine
linearization. -/
def gradientLinearizationRemainder
    (gradient : State → State) (center : State)
    (linear : State →L[ℝ] State) (state : State) : State :=
  gradient state - gradient center - (linear state - linear center)

theorem gradient_sub_eq_linear_add_remainder_sub
    (gradient : State → State) (center : State)
    (linear : State →L[ℝ] State) (left right : State) :
    gradient left - gradient right =
      linear (left - right) +
        (gradientLinearizationRemainder gradient center linear left -
          gradientLinearizationRemainder gradient center linear right) := by
  simp only [gradientLinearizationRemainder, map_sub]
  abel

/-! ## Direct remainder certificate -/

/-- A source may certify the nonlinear part directly, without exposing a
derivative implementation.  The remainder factor must be strictly smaller
than the strong-monotonicity modulus of the audited linear map. -/
structure RegionalGradientRemainderBudget
    (gradient : State → State) (center : State) (radius : ℝ)
    (linear : State →L[ℝ] State) where
  linearModulus : ℝ
  remainderFactor : ℝ
  radius_nonneg : 0 ≤ radius
  linearModulus_nonneg : 0 ≤ linearModulus
  remainderFactor_nonneg : 0 ≤ remainderFactor
  remainderFactor_lt_linearModulus : remainderFactor < linearModulus
  linearModulus_le_norm : linearModulus ≤ ‖linear‖
  gradient_center_zero : gradient center = 0
  linear_strongMonotone : ∀ displacement,
    linearModulus * ‖displacement‖ ^ 2 ≤
      ⟪linear displacement, displacement⟫_ℝ
  remainder_pair_bound : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖gradientLinearizationRemainder gradient center linear left -
        gradientLinearizationRemainder gradient center linear right‖ ≤
      remainderFactor * ‖left - right‖

/-- A linear margin minus a uniform nonlinear remainder yields the exact
two-point regional certificate required by gradient settling. -/
noncomputable def RegionalGradientRemainderBudget.toRegionalGradientCertificate
    {gradient : State → State} {center : State} {radius : ℝ}
    {linear : State →L[ℝ] State}
    (budget : RegionalGradientRemainderBudget
      gradient center radius linear) :
    RegionalGradientCertificate gradient center radius
      (budget.linearModulus - budget.remainderFactor)
      (‖linear‖ + budget.remainderFactor) where
  radius_nonneg := budget.radius_nonneg
  modulus_nonneg := sub_nonneg.mpr budget.remainderFactor_lt_linearModulus.le
  lipschitz_nonneg := add_nonneg (norm_nonneg _) budget.remainderFactor_nonneg
  modulus_le_lipschitz := by
    linarith [budget.linearModulus_le_norm, budget.remainderFactor_nonneg]
  gradient_center_zero := budget.gradient_center_zero
  gradient_strongMonotone_on_ball := by
    intro left right hleft hright
    let displacement := left - right
    let remainderDifference :=
      gradientLinearizationRemainder gradient center linear left -
        gradientLinearizationRemainder gradient center linear right
    have hlinear := budget.linear_strongMonotone displacement
    have hremainder := budget.remainder_pair_bound left right hleft hright
    have hremainderProduct :
        ‖remainderDifference‖ * ‖displacement‖ ≤
          budget.remainderFactor * ‖displacement‖ ^ 2 := by
      dsimp [remainderDifference, displacement]
      calc
        ‖gradientLinearizationRemainder gradient center linear left -
              gradientLinearizationRemainder gradient center linear right‖ *
            ‖left - right‖ ≤
            (budget.remainderFactor * ‖left - right‖) *
              ‖left - right‖ :=
          mul_le_mul_of_nonneg_right hremainder (norm_nonneg _)
        _ = budget.remainderFactor * ‖left - right‖ ^ 2 := by ring
    have hcauchy :
        -(‖remainderDifference‖ * ‖displacement‖) ≤
          ⟪remainderDifference, displacement⟫_ℝ :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    rw [gradient_sub_eq_linear_add_remainder_sub,
      inner_add_left]
    dsimp [displacement, remainderDifference] at hlinear hremainderProduct hcauchy ⊢
    nlinarith
  gradient_lipschitz_on_ball := by
    intro left right hleft hright
    let remainderDifference :=
      gradientLinearizationRemainder gradient center linear left -
        gradientLinearizationRemainder gradient center linear right
    have hremainder := budget.remainder_pair_bound left right hleft hright
    rw [gradient_sub_eq_linear_add_remainder_sub]
    calc
      ‖linear (left - right) + remainderDifference‖ ≤
          ‖linear (left - right)‖ + ‖remainderDifference‖ := norm_add_le _ _
      _ ≤ ‖linear‖ * ‖left - right‖ +
          budget.remainderFactor * ‖left - right‖ :=
        add_le_add (linear.le_opNorm _) hremainder
      _ = (‖linear‖ + budget.remainderFactor) * ‖left - right‖ := by ring

/-! ## Uniform Jacobian-deviation certificate -/

/-- A directly checkable derivative enclosure.  `linear` is pinned to the
Jacobian at the center, while `jacobianVariation` encloses its operator-norm
change everywhere on the ball. -/
structure RegionalGradientJacobianEnclosure
    (gradient : State → State) (center : State) (radius : ℝ)
    (linear : State →L[ℝ] State) where
  linearModulus : ℝ
  jacobianVariation : ℝ
  radius_nonneg : 0 ≤ radius
  linearModulus_nonneg : 0 ≤ linearModulus
  jacobianVariation_nonneg : 0 ≤ jacobianVariation
  jacobianVariation_lt_linearModulus : jacobianVariation < linearModulus
  linearModulus_le_norm : linearModulus ≤ ‖linear‖
  gradient_center_zero : gradient center = 0
  gradient_differentiable_on_ball : ∀ state,
    InClosedBall center radius state → DifferentiableAt ℝ gradient state
  linear_eq_centerJacobian : linear = fderiv ℝ gradient center
  linear_strongMonotone : ∀ displacement,
    linearModulus * ‖displacement‖ ^ 2 ≤
      ⟪linear displacement, displacement⟫_ℝ
  jacobian_deviation_on_ball : ∀ state,
    InClosedBall center radius state →
    ‖fderiv ℝ gradient state - linear‖ ≤ jacobianVariation

/-- The same derivative data at an audited point that need not already be a
stationary state.  Its nonzero solver displacement will be charged separately
when proving that the declared ball is invariant. -/
structure AuditedCenterJacobianEnclosure
    (gradient : State → State) (center : State) (radius : ℝ)
    (linear : State →L[ℝ] State) where
  linearModulus : ℝ
  jacobianVariation : ℝ
  radius_nonneg : 0 ≤ radius
  linearModulus_nonneg : 0 ≤ linearModulus
  jacobianVariation_nonneg : 0 ≤ jacobianVariation
  jacobianVariation_lt_linearModulus : jacobianVariation < linearModulus
  linearModulus_le_norm : linearModulus ≤ ‖linear‖
  gradient_differentiable_on_ball : ∀ state,
    InClosedBall center radius state → DifferentiableAt ℝ gradient state
  linear_eq_centerJacobian : linear = fderiv ℝ gradient center
  linear_strongMonotone : ∀ displacement,
    linearModulus * ‖displacement‖ ^ 2 ≤
      ⟪linear displacement, displacement⟫_ℝ
  jacobian_deviation_on_ball : ∀ state,
    InClosedBall center radius state →
    ‖fderiv ℝ gradient state - linear‖ ≤ jacobianVariation

/-- Subtracting the value at the audited center preserves every Jacobian and
every two-point gradient difference while making the center stationary. -/
def centerShiftedGradient
    (gradient : State → State) (center state : State) : State :=
  gradient state - gradient center

theorem centerShiftedGradient_hasFDerivAt
    {gradient : State → State} {center state : State}
    (hgradient : DifferentiableAt ℝ gradient state) :
    HasFDerivAt (centerShiftedGradient gradient center)
      (fderiv ℝ gradient state) state := by
  exact hgradient.hasFDerivAt.sub_const (gradient center)

/-- The audited nonstationary enclosure becomes a stationary enclosure for
the shifted field. -/
noncomputable def AuditedCenterJacobianEnclosure.toStationaryShiftedEnclosure
    {gradient : State → State} {center : State} {radius : ℝ}
    {linear : State →L[ℝ] State}
    (enclosure : AuditedCenterJacobianEnclosure
      gradient center radius linear) :
    RegionalGradientJacobianEnclosure
      (centerShiftedGradient gradient center) center radius linear where
  linearModulus := enclosure.linearModulus
  jacobianVariation := enclosure.jacobianVariation
  radius_nonneg := enclosure.radius_nonneg
  linearModulus_nonneg := enclosure.linearModulus_nonneg
  jacobianVariation_nonneg := enclosure.jacobianVariation_nonneg
  jacobianVariation_lt_linearModulus := enclosure.jacobianVariation_lt_linearModulus
  linearModulus_le_norm := enclosure.linearModulus_le_norm
  gradient_center_zero := by simp [centerShiftedGradient]
  gradient_differentiable_on_ball := by
    intro state hstate
    exact (centerShiftedGradient_hasFDerivAt
      (enclosure.gradient_differentiable_on_ball state hstate)).differentiableAt
  linear_eq_centerJacobian := by
    have hcenter : InClosedBall center radius center := by
      simp [InClosedBall, enclosure.radius_nonneg]
    rw [(centerShiftedGradient_hasFDerivAt
      (enclosure.gradient_differentiable_on_ball center hcenter)).fderiv]
    exact enclosure.linear_eq_centerJacobian
  linear_strongMonotone := enclosure.linear_strongMonotone
  jacobian_deviation_on_ball := by
    intro state hstate
    rw [(centerShiftedGradient_hasFDerivAt
      (enclosure.gradient_differentiable_on_ball state hstate)).fderiv]
    exact enclosure.jacobian_deviation_on_ball state hstate

theorem gradientLinearizationRemainder_hasFDerivAt
    {gradient : State → State} {center state : State}
    {linear : State →L[ℝ] State}
    (hgradient : DifferentiableAt ℝ gradient state) :
    HasFDerivAt (gradientLinearizationRemainder gradient center linear)
      (fderiv ℝ gradient state - linear) state := by
  have hlinear :
      HasFDerivAt (fun candidate : State => linear candidate - linear center)
        linear state := by
    exact linear.hasFDerivAt.sub_const (linear center)
  change HasFDerivAt
    (fun candidate =>
      gradient candidate - gradient center - (linear candidate - linear center))
    (fderiv ℝ gradient state - linear) state
  exact (hgradient.hasFDerivAt.sub_const (gradient center)).sub hlinear

theorem RegionalGradientJacobianEnclosure.remainder_pair_bound
    {gradient : State → State} {center : State} {radius : ℝ}
    {linear : State →L[ℝ] State}
    (enclosure : RegionalGradientJacobianEnclosure
      gradient center radius linear)
    (left right : State)
    (hleft : InClosedBall center radius left)
    (hright : InClosedBall center radius right) :
    ‖gradientLinearizationRemainder gradient center linear left -
        gradientLinearizationRemainder gradient center linear right‖ ≤
      enclosure.jacobianVariation * ‖left - right‖ := by
  let ball : Set State := Metric.closedBall center radius
  have hleftBall : left ∈ ball := by
    simpa [ball, InClosedBall, Metric.mem_closedBall, dist_eq_norm] using hleft
  have hrightBall : right ∈ ball := by
    simpa [ball, InClosedBall, Metric.mem_closedBall, dist_eq_norm] using hright
  have hdifferentiable : ∀ state ∈ ball,
      DifferentiableAt ℝ
        (gradientLinearizationRemainder gradient center linear) state := by
    intro state hstate
    apply (gradientLinearizationRemainder_hasFDerivAt
      (enclosure.gradient_differentiable_on_ball state ?_)).differentiableAt
    simpa [ball, InClosedBall, Metric.mem_closedBall, dist_eq_norm] using hstate
  have hderivative : ∀ state ∈ ball,
      ‖fderiv ℝ (gradientLinearizationRemainder gradient center linear) state‖ ≤
        enclosure.jacobianVariation := by
    intro state hstate
    have hstate' : InClosedBall center radius state := by
      simpa [ball, InClosedBall, Metric.mem_closedBall, dist_eq_norm] using hstate
    rw [(gradientLinearizationRemainder_hasFDerivAt
      (enclosure.gradient_differentiable_on_ball state hstate')).fderiv]
    exact enclosure.jacobian_deviation_on_ball state hstate'
  exact (convex_closedBall center radius).norm_image_sub_le_of_norm_fderiv_le
    hdifferentiable hderivative hrightBall hleftBall

/-- The derivative enclosure discharges the direct nonlinear remainder
premise and therefore yields a regional gradient certificate. -/
noncomputable def RegionalGradientJacobianEnclosure.toRemainderBudget
    {gradient : State → State} {center : State} {radius : ℝ}
    {linear : State →L[ℝ] State}
    (enclosure : RegionalGradientJacobianEnclosure
      gradient center radius linear) :
    RegionalGradientRemainderBudget gradient center radius linear where
  linearModulus := enclosure.linearModulus
  remainderFactor := enclosure.jacobianVariation
  radius_nonneg := enclosure.radius_nonneg
  linearModulus_nonneg := enclosure.linearModulus_nonneg
  remainderFactor_nonneg := enclosure.jacobianVariation_nonneg
  remainderFactor_lt_linearModulus := enclosure.jacobianVariation_lt_linearModulus
  linearModulus_le_norm := enclosure.linearModulus_le_norm
  gradient_center_zero := enclosure.gradient_center_zero
  linear_strongMonotone := enclosure.linear_strongMonotone
  remainder_pair_bound := enclosure.remainder_pair_bound

noncomputable def RegionalGradientJacobianEnclosure.toRegionalGradientCertificate
    {gradient : State → State} {center : State} {radius : ℝ}
    {linear : State →L[ℝ] State}
    (enclosure : RegionalGradientJacobianEnclosure
      gradient center radius linear) :
    RegionalGradientCertificate gradient center radius
      (enclosure.linearModulus - enclosure.jacobianVariation)
      (‖linear‖ + enclosure.jacobianVariation) :=
  enclosure.toRemainderBudget.toRegionalGradientCertificate

/-- A uniform derivative enclosure therefore feeds the existing invariant
local solver certificate with no new settling semantics. -/
noncomputable def RegionalGradientJacobianEnclosure.toLocalContractionCertificate
    {gradient : State → State} {center : State} {radius rate : ℝ}
    {linear : State →L[ℝ] State}
    (enclosure : RegionalGradientJacobianEnclosure
      gradient center radius linear)
    (hrate : 0 < rate)
    (hstable :
      rate * (‖linear‖ + enclosure.jacobianVariation) ^ 2 <
        2 * (enclosure.linearModulus - enclosure.jacobianVariation)) :
    LocalContractionCertificate
      (regionalGradientStep rate gradient) center radius :=
  enclosure.toRegionalGradientCertificate.toLocalContractionCertificate
    hrate hstable

/-- Pairwise contraction around a nonstationary audited center.  Shifting the
gradient by its center value changes every step by the same translation, so
step differences are unchanged. -/
theorem AuditedCenterJacobianEnclosure.gradientStep_distance_le
    {gradient : State → State} {center : State} {radius rate : ℝ}
    {linear : State →L[ℝ] State}
    (enclosure : AuditedCenterJacobianEnclosure
      gradient center radius linear)
    (hrate : 0 ≤ rate) (left right : State)
    (hleft : InClosedBall center radius left)
    (hright : InClosedBall center radius right) :
    ‖regionalGradientStep rate gradient left -
        regionalGradientStep rate gradient right‖ ≤
      hilbertSettlingContraction
          (enclosure.linearModulus - enclosure.jacobianVariation)
          (‖linear‖ + enclosure.jacobianVariation) rate *
        ‖left - right‖ := by
  have hshifted := regionalGradientStep_distance_le
    enclosure.toStationaryShiftedEnclosure.toRegionalGradientCertificate
    hrate left right hleft hright
  have hsteps :
      regionalGradientStep rate
          (centerShiftedGradient gradient center) left -
        regionalGradientStep rate
          (centerShiftedGradient gradient center) right =
      regionalGradientStep rate gradient left -
        regionalGradientStep rate gradient right := by
    simp only [regionalGradientStep, centerShiftedGradient]
    module
  rw [hsteps] at hshifted
  exact hshifted

/-- A posteriori ball admission.  The center need not be a fixed point: its
observed one-step displacement must fit inside the contraction margin left by
the radius. -/
noncomputable def AuditedCenterJacobianEnclosure.toLocalContractionCertificate
    {gradient : State → State} {center : State} {radius rate : ℝ}
    {linear : State →L[ℝ] State}
    (enclosure : AuditedCenterJacobianEnclosure
      gradient center radius linear)
    (hrate : 0 < rate)
    (hstable :
      rate * (‖linear‖ + enclosure.jacobianVariation) ^ 2 <
        2 * (enclosure.linearModulus - enclosure.jacobianVariation))
    (hadmission :
      ‖regionalGradientStep rate gradient center - center‖ ≤
        (1 - hilbertSettlingContraction
          (enclosure.linearModulus - enclosure.jacobianVariation)
          (‖linear‖ + enclosure.jacobianVariation) rate) * radius) :
    LocalContractionCertificate
      (regionalGradientStep rate gradient) center radius where
  factor := hilbertSettlingContraction
    (enclosure.linearModulus - enclosure.jacobianVariation)
    (‖linear‖ + enclosure.jacobianVariation) rate
  factor_nonneg := hilbertSettlingContraction_nonneg _ _ _
  factor_lt_one := hilbertSettlingContraction_lt_one
    (enclosure.linearModulus - enclosure.jacobianVariation)
    (‖linear‖ + enclosure.jacobianVariation) rate hrate hstable
    (regionalContractionSq_nonneg
      enclosure.toStationaryShiftedEnclosure.toRegionalGradientCertificate)
  radius_nonneg := enclosure.radius_nonneg
  maps_ball := by
    intro state hstate
    have hpair := enclosure.gradientStep_distance_le hrate.le
      state center hstate (by simp [InClosedBall, enclosure.radius_nonneg])
    have htriangle :
        ‖regionalGradientStep rate gradient state - center‖ ≤
          ‖regionalGradientStep rate gradient state -
              regionalGradientStep rate gradient center‖ +
            ‖regionalGradientStep rate gradient center - center‖ := by
      have hraw := norm_add_le
        (regionalGradientStep rate gradient state -
          regionalGradientStep rate gradient center)
        (regionalGradientStep rate gradient center - center)
      simpa only [sub_add_sub_cancel] using hraw
    calc
      ‖regionalGradientStep rate gradient state - center‖ ≤
          ‖regionalGradientStep rate gradient state -
              regionalGradientStep rate gradient center‖ +
            ‖regionalGradientStep rate gradient center - center‖ := htriangle
      _ ≤ hilbertSettlingContraction
              (enclosure.linearModulus - enclosure.jacobianVariation)
              (‖linear‖ + enclosure.jacobianVariation) rate *
            ‖state - center‖ +
          (1 - hilbertSettlingContraction
              (enclosure.linearModulus - enclosure.jacobianVariation)
              (‖linear‖ + enclosure.jacobianVariation) rate) * radius :=
        add_le_add hpair hadmission
      _ ≤ hilbertSettlingContraction
              (enclosure.linearModulus - enclosure.jacobianVariation)
              (‖linear‖ + enclosure.jacobianVariation) rate * radius +
          (1 - hilbertSettlingContraction
              (enclosure.linearModulus - enclosure.jacobianVariation)
              (‖linear‖ + enclosure.jacobianVariation) rate) * radius := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left hstate
            (hilbertSettlingContraction_nonneg _ _ _)) _
      _ = radius := by ring
  contracts_on_ball := by
    intro left right hleft hright
    exact enclosure.gradientStep_distance_le hrate.le
      left right hleft hright

/-! ## Positive fixture -/

noncomputable def scalarIdentityLinear : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.id ℝ ℝ

def scalarQuadraticGradient (state : ℝ) : ℝ := state + state ^ 2 / 4

theorem hasDerivAt_scalarQuadraticGradient (state : ℝ) :
    HasDerivAt scalarQuadraticGradient (1 + state / 2) state := by
  convert (hasDerivAt_id state).add
    ((hasDerivAt_pow 2 state).div_const 4) using 1
  all_goals first | rfl | ring

theorem fderiv_scalarQuadraticGradient (state : ℝ) :
    fderiv ℝ scalarQuadraticGradient state =
      ContinuousLinearMap.toSpanSingleton ℝ (1 + state / 2) :=
  (hasDerivAt_scalarQuadraticGradient state).hasFDerivAt.fderiv

noncomputable def scalarQuadraticJacobianEnclosure :
    RegionalGradientJacobianEnclosure
      scalarQuadraticGradient 0 1 scalarIdentityLinear where
  linearModulus := 1
  jacobianVariation := 1 / 2
  radius_nonneg := by norm_num
  linearModulus_nonneg := by norm_num
  jacobianVariation_nonneg := by norm_num
  jacobianVariation_lt_linearModulus := by norm_num
  linearModulus_le_norm := by
    simp [scalarIdentityLinear]
  gradient_center_zero := by norm_num [scalarQuadraticGradient]
  gradient_differentiable_on_ball := by
    intro state _
    exact (hasDerivAt_scalarQuadraticGradient state).differentiableAt
  linear_eq_centerJacobian := by
    rw [fderiv_scalarQuadraticGradient]
    apply ContinuousLinearMap.ext
    intro direction
    simp [scalarIdentityLinear]
  linear_strongMonotone := by
    intro displacement
    simp [scalarIdentityLinear]
  jacobian_deviation_on_ball := by
    intro state hstate
    rw [fderiv_scalarQuadraticGradient]
    have hnorm : |state| ≤ 1 := by
      simpa [InClosedBall, Real.norm_eq_abs] using hstate
    rw [show ContinuousLinearMap.toSpanSingleton ℝ (1 + state / 2) -
          scalarIdentityLinear =
        ContinuousLinearMap.toSpanSingleton ℝ (state / 2) by
      apply ContinuousLinearMap.ext
      intro direction
      simp [scalarIdentityLinear]
      ring]
    calc
      ‖ContinuousLinearMap.toSpanSingleton ℝ (state / 2)‖ = |state| / 2 := by
        simp [Real.norm_eq_abs]
      _ ≤ 1 / 2 := by nlinarith [abs_nonneg state]

noncomputable def scalarQuadraticRegionalCertificate :
    RegionalGradientCertificate scalarQuadraticGradient 0 1 (1 / 2) (3 / 2) := by
  convert scalarQuadraticJacobianEnclosure.toRegionalGradientCertificate using 1 <;>
    norm_num [scalarQuadraticJacobianEnclosure, scalarIdentityLinear]

noncomputable def scalarQuadraticLocalContraction :
    LocalContractionCertificate
      (regionalGradientStep (1 / 4) scalarQuadraticGradient) 0 1 :=
  scalarQuadraticJacobianEnclosure.toLocalContractionCertificate
    (by norm_num)
    (by norm_num [scalarQuadraticJacobianEnclosure, scalarIdentityLinear])

theorem scalarQuadratic_step_exact (state : ℝ) :
    regionalGradientStep (1 / 4) scalarQuadraticGradient state =
      (3 / 4) * state - state ^ 2 / 16 := by
  simp [regionalGradientStep, scalarQuadraticGradient]
  ring

theorem scalarQuadratic_iterates_stay_in_unitBall
    (initial : ℝ) (hinitial : InClosedBall 0 1 initial) (steps : ℕ) :
    InClosedBall 0 1
      ((regionalGradientStep (1 / 4) scalarQuadraticGradient)^[steps] initial) :=
  iterate_mem_closedBall scalarQuadraticLocalContraction initial hinitial steps

/-! ## Audited-center fixtures -/

def affineTargetOneGradient (state : ℝ) : ℝ := state - 1

theorem hasDerivAt_affineTargetOneGradient (state : ℝ) :
    HasDerivAt affineTargetOneGradient 1 state := by
  change HasDerivAt (fun candidate : ℝ => candidate - 1) 1 state
  exact (hasDerivAt_id state).sub_const 1

theorem fderiv_affineTargetOneGradient (state : ℝ) :
    fderiv ℝ affineTargetOneGradient state = scalarIdentityLinear := by
  rw [(hasDerivAt_affineTargetOneGradient state).hasFDerivAt.fderiv]
  apply ContinuousLinearMap.ext
  intro direction
  simp [scalarIdentityLinear]

noncomputable def affineTargetOneAuditedEnclosure :
    AuditedCenterJacobianEnclosure
      affineTargetOneGradient 0 1 scalarIdentityLinear where
  linearModulus := 1
  jacobianVariation := 0
  radius_nonneg := by norm_num
  linearModulus_nonneg := by norm_num
  jacobianVariation_nonneg := by norm_num
  jacobianVariation_lt_linearModulus := by norm_num
  linearModulus_le_norm := by simp [scalarIdentityLinear]
  gradient_differentiable_on_ball := by
    intro state _
    exact (hasDerivAt_affineTargetOneGradient state).differentiableAt
  linear_eq_centerJacobian := by
    exact (fderiv_affineTargetOneGradient 0).symm
  linear_strongMonotone := by
    intro displacement
    simp [scalarIdentityLinear]
  jacobian_deviation_on_ball := by
    intro state _
    rw [fderiv_affineTargetOneGradient]
    simp

/-- The center is not stationary, but its observed half-step exactly fits the
remaining half-radius after contraction. -/
noncomputable def affineTargetOneLocalContraction :
    LocalContractionCertificate
      (regionalGradientStep (1 / 2) affineTargetOneGradient) 0 1 :=
  affineTargetOneAuditedEnclosure.toLocalContractionCertificate
    (by norm_num)
    (by norm_num [affineTargetOneAuditedEnclosure, scalarIdentityLinear])
    (by
      norm_num [regionalGradientStep, affineTargetOneGradient,
        affineTargetOneAuditedEnclosure, scalarIdentityLinear,
        hilbertSettlingContraction, hilbertSettlingContractionSq])

theorem affineTargetOne_target_fixed :
    IsFixedPoint
      (regionalGradientStep (1 / 2) affineTargetOneGradient) 1 := by
  norm_num [IsFixedPoint, regionalGradientStep, affineTargetOneGradient]

theorem affineTargetOne_iterates_stay_in_unitBall
    (initial : ℝ) (hinitial : InClosedBall 0 1 initial) (steps : ℕ) :
    InClosedBall 0 1
      ((regionalGradientStep (1 / 2) affineTargetOneGradient)^[steps] initial) :=
  iterate_mem_closedBall affineTargetOneLocalContraction initial hinitial steps

def affineTargetTwoGradient (state : ℝ) : ℝ := state - 2

theorem hasDerivAt_affineTargetTwoGradient (state : ℝ) :
    HasDerivAt affineTargetTwoGradient 1 state := by
  change HasDerivAt (fun candidate : ℝ => candidate - 2) 1 state
  exact (hasDerivAt_id state).sub_const 2

/-- Pairwise contraction alone does not make an arbitrary centered ball
invariant: this half-step sends the boundary point `1` to `3 / 2`. -/
theorem affineTargetTwo_pairwiseContraction_not_ballInvariant :
    ¬ Nonempty
      (LocalContractionCertificate
        (regionalGradientStep (1 / 2) affineTargetTwoGradient) 0 1) := by
  rintro ⟨certificate⟩
  have honeMem : InClosedBall (0 : ℝ) 1 1 := by
    norm_num [InClosedBall]
  have hmapped := certificate.maps_ball 1 honeMem
  norm_num [InClosedBall, regionalGradientStep, affineTargetTwoGradient] at hmapped

/-! ## Negative fixture: a positive center Jacobian is not enough -/

def centerPositiveNonlinearGradient (state : ℝ) : ℝ := state - state ^ 2

theorem centerPositiveNonlinearGradient_centerDerivative :
    HasDerivAt centerPositiveNonlinearGradient 1 0 := by
  convert (hasDerivAt_id (0 : ℝ)).sub (hasDerivAt_pow 2 0) using 1
  all_goals first | rfl | ring

theorem centerPositiveNonlinearGradient_two_roots :
    centerPositiveNonlinearGradient 0 = 0 ∧
      centerPositiveNonlinearGradient 1 = 0 := by
  norm_num [centerPositiveNonlinearGradient]

/-- Despite its positive unit derivative at the center, this field gives a
gradient step with two distinct fixed points in the unit ball. -/
theorem centerJacobian_positive_not_sufficient (rate : ℝ) :
    ¬ Nonempty
      (LocalContractionCertificate
        (regionalGradientStep rate centerPositiveNonlinearGradient) 0 1) := by
  rintro ⟨certificate⟩
  have hzeroMem : InClosedBall (0 : ℝ) 1 0 := by norm_num [InClosedBall]
  have honeMem : InClosedBall (0 : ℝ) 1 1 := by norm_num [InClosedBall]
  have hzeroFixed :
      IsFixedPoint (regionalGradientStep rate centerPositiveNonlinearGradient) 0 := by
    simp [IsFixedPoint, regionalGradientStep, centerPositiveNonlinearGradient]
  have honeFixed :
      IsFixedPoint (regionalGradientStep rate centerPositiveNonlinearGradient) 1 := by
    simp [IsFixedPoint, regionalGradientStep, centerPositiveNonlinearGradient]
  have hequal := fixedPoint_unique_in_closedBall certificate
    hzeroMem honeMem hzeroFixed honeFixed
  norm_num at hequal

#print axioms RegionalGradientRemainderBudget.toRegionalGradientCertificate
#print axioms RegionalGradientJacobianEnclosure.remainder_pair_bound
#print axioms RegionalGradientJacobianEnclosure.toRegionalGradientCertificate
#print axioms RegionalGradientJacobianEnclosure.toLocalContractionCertificate
#print axioms AuditedCenterJacobianEnclosure.gradientStep_distance_le
#print axioms AuditedCenterJacobianEnclosure.toLocalContractionCertificate
#print axioms scalarQuadraticRegionalCertificate
#print axioms scalarQuadratic_iterates_stay_in_unitBall
#print axioms affineTargetOneLocalContraction
#print axioms affineTargetOne_iterates_stay_in_unitBall
#print axioms affineTargetTwo_pairwiseContraction_not_ballInvariant
#print axioms centerJacobian_positive_not_sufficient

end

end RegionalLinearizationCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
