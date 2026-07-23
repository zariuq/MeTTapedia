import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegionalErrorCoordinateContraction

/-!
# Nonlinear readout transport for error-coordinate credit

The task gradient seen by an error coordinate is a pullback through the
adapter residual and the frozen task path.  For a state-dependent pullback
`J(x)^*` and output-space gradient `g`, it has the form

`J(x)^* g(r(x))`.

This file separates the four quantities needed to bound that field on a
declared ball: motion of the readout, the pullback norm, variation of the
pullback, and the output-gradient norm and Lipschitz constant.  Their exact
composition gives the regional task-gradient constant

`J * L * R + H * G`.

The second summand is essential for nonlinear readouts.  A negative fixture
uses a constant output gradient, for which `L = 0`, while a varying Jacobian
still produces a nonconstant pulled-back gradient.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace NonlinearReadoutGradientTransport

open scoped InnerProduct InnerProductSpace
open AmortizedInitialization
open ErrorCoordinateResidualSemantics
open LocalAmortizedInitialization
open RegionalErrorCoordinateContraction

noncomputable section

variable {State Feature : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]
  [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]

/-- The pullback of an output-space task gradient through a declared readout.
`pullback state` is the adjoint-Jacobian action exposed by the source model. -/
def pullbackTaskGradient
    (readout : State → Feature)
    (pullback : State → Feature →L[ℝ] State)
    (outputGradient : Feature → Feature) (state : State) : State :=
  pullback state (outputGradient (readout state))

/-- Source-level regional bounds for a nonlinear readout and its task-gradient
pullback.  The readout and pullback bounds are kept separate: identifying them
requires a derivative theorem for the concrete source map and is not assumed
by this interface. -/
structure PullbackGradientBudget
    (readout : State → Feature)
    (pullback : State → Feature →L[ℝ] State)
    (outputGradient : Feature → Feature)
    (center : State) (radius readoutRate pullbackRate
      pullbackVariation outputGradientRate outputGradientBound : ℝ) where
  radius_nonneg : 0 ≤ radius
  readoutRate_nonneg : 0 ≤ readoutRate
  pullbackRate_nonneg : 0 ≤ pullbackRate
  pullbackVariation_nonneg : 0 ≤ pullbackVariation
  outputGradientRate_nonneg : 0 ≤ outputGradientRate
  outputGradientBound_nonneg : 0 ≤ outputGradientBound
  readout_lipschitz_on_ball : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖readout left - readout right‖ ≤ readoutRate * ‖left - right‖
  pullback_action_on_ball : ∀ state feature,
    InClosedBall center radius state →
    ‖pullback state feature‖ ≤ pullbackRate * ‖feature‖
  pullback_variation_on_ball : ∀ left right feature,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖(pullback left - pullback right) feature‖ ≤
      pullbackVariation * ‖left - right‖ * ‖feature‖
  outputGradient_lipschitz_on_image : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖outputGradient (readout left) - outputGradient (readout right)‖ ≤
      outputGradientRate * ‖readout left - readout right‖
  outputGradient_norm_on_image : ∀ state,
    InClosedBall center radius state →
    ‖outputGradient (readout state)‖ ≤ outputGradientBound

/-- The exact conservative coefficient obtained by transporting output credit
through a nonlinear readout. -/
def pullbackGradientRate
    (readoutRate pullbackRate pullbackVariation
      outputGradientRate outputGradientBound : ℝ) : ℝ :=
  pullbackRate * outputGradientRate * readoutRate +
    pullbackVariation * outputGradientBound

theorem PullbackGradientBudget.pullbackGradientRate_nonneg
    {readout : State → Feature}
    {pullback : State → Feature →L[ℝ] State}
    {outputGradient : Feature → Feature}
    {center : State}
    {radius readoutRate pullbackRate pullbackVariation
      outputGradientRate outputGradientBound : ℝ}
    (budget : PullbackGradientBudget readout pullback outputGradient center
      radius readoutRate pullbackRate pullbackVariation
      outputGradientRate outputGradientBound) :
    0 ≤ pullbackGradientRate readoutRate pullbackRate pullbackVariation
      outputGradientRate outputGradientBound := by
  unfold pullbackGradientRate
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg budget.pullbackRate_nonneg
        budget.outputGradientRate_nonneg)
      budget.readoutRate_nonneg)
    (mul_nonneg budget.pullbackVariation_nonneg
      budget.outputGradientBound_nonneg)

theorem pullbackTaskGradient_sub
    (readout : State → Feature)
    (pullback : State → Feature →L[ℝ] State)
    (outputGradient : Feature → Feature) (left right : State) :
    pullbackTaskGradient readout pullback outputGradient left -
        pullbackTaskGradient readout pullback outputGradient right =
      pullback left
          (outputGradient (readout left) - outputGradient (readout right)) +
        (pullback left - pullback right)
          (outputGradient (readout right)) := by
  simp only [pullbackTaskGradient, map_sub, sub_apply]
  abel

/-- Nonlinear readout transport.  The first term charges motion of the output
gradient through the readout.  The second charges motion of the pullback
itself, weighted by the absolute size of output credit. -/
theorem PullbackGradientBudget.taskGradient_lipschitz_on_ball
    {readout : State → Feature}
    {pullback : State → Feature →L[ℝ] State}
    {outputGradient : Feature → Feature}
    {center : State}
    {radius readoutRate pullbackRate pullbackVariation
      outputGradientRate outputGradientBound : ℝ}
    (budget : PullbackGradientBudget readout pullback outputGradient center
      radius readoutRate pullbackRate pullbackVariation
      outputGradientRate outputGradientBound)
    (left right : State)
    (hleft : InClosedBall center radius left)
    (hright : InClosedBall center radius right) :
    ‖pullbackTaskGradient readout pullback outputGradient left -
        pullbackTaskGradient readout pullback outputGradient right‖ ≤
      pullbackGradientRate readoutRate pullbackRate pullbackVariation
        outputGradientRate outputGradientBound * ‖left - right‖ := by
  let outputDifference :=
    outputGradient (readout left) - outputGradient (readout right)
  have hreadout := budget.readout_lipschitz_on_ball left right hleft hright
  have houtput :=
    budget.outputGradient_lipschitz_on_image left right hleft hright
  have hpullback := budget.pullback_action_on_ball left outputDifference hleft
  have hvariation := budget.pullback_variation_on_ball left right
    (outputGradient (readout right)) hleft hright
  have houtputNorm := budget.outputGradient_norm_on_image right hright
  have hfirst :
      ‖pullback left outputDifference‖ ≤
        pullbackRate * outputGradientRate * readoutRate *
          ‖left - right‖ := by
    calc
      ‖pullback left outputDifference‖ ≤
          pullbackRate * ‖outputDifference‖ := hpullback
      _ ≤ pullbackRate *
          (outputGradientRate * ‖readout left - readout right‖) := by
        exact mul_le_mul_of_nonneg_left houtput budget.pullbackRate_nonneg
      _ ≤ pullbackRate *
          (outputGradientRate * (readoutRate * ‖left - right‖)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hreadout
            budget.outputGradientRate_nonneg)
          budget.pullbackRate_nonneg
      _ = pullbackRate * outputGradientRate * readoutRate *
          ‖left - right‖ := by ring
  have hsecond :
      ‖(pullback left - pullback right) (outputGradient (readout right))‖ ≤
        pullbackVariation * outputGradientBound * ‖left - right‖ := by
    calc
      ‖(pullback left - pullback right) (outputGradient (readout right))‖ ≤
          pullbackVariation * ‖left - right‖ *
            ‖outputGradient (readout right)‖ := hvariation
      _ ≤ pullbackVariation * ‖left - right‖ * outputGradientBound := by
        exact mul_le_mul_of_nonneg_left houtputNorm
          (mul_nonneg budget.pullbackVariation_nonneg (norm_nonneg _))
      _ = pullbackVariation * outputGradientBound *
          ‖left - right‖ := by ring
  rw [pullbackTaskGradient_sub]
  calc
    ‖pullback left outputDifference +
        (pullback left - pullback right)
          (outputGradient (readout right))‖ ≤
      ‖pullback left outputDifference‖ +
        ‖(pullback left - pullback right)
          (outputGradient (readout right))‖ := norm_add_le _ _
    _ ≤
        pullbackRate * outputGradientRate * readoutRate *
            ‖left - right‖ +
          pullbackVariation * outputGradientBound *
            ‖left - right‖ := add_le_add hfirst hsecond
    _ = pullbackGradientRate readoutRate pullbackRate pullbackVariation
          outputGradientRate outputGradientBound * ‖left - right‖ := by
      unfold pullbackGradientRate
      ring

/-- Every nonnegative Lipschitz bound also gives the conservative matching
hypomonotonicity bound needed by precision-dominated PC settling. -/
theorem lipschitz_pair_bound_implies_hypomonotone
    (gradient : State → State) (center : State) (radius beta : ℝ)
    (_hbeta : 0 ≤ beta)
    (hlipschitz : ∀ left right,
      InClosedBall center radius left → InClosedBall center radius right →
      ‖gradient left - gradient right‖ ≤ beta * ‖left - right‖) :
    ∀ left right,
      InClosedBall center radius left → InClosedBall center radius right →
      -(beta * ‖left - right‖ ^ 2) ≤
        ⟪gradient left - gradient right, left - right⟫_ℝ := by
  intro left right hleft hright
  have hlip := hlipschitz left right hleft hright
  have hproduct :
      ‖gradient left - gradient right‖ * ‖left - right‖ ≤
        beta * ‖left - right‖ ^ 2 := by
    calc
      ‖gradient left - gradient right‖ * ‖left - right‖ ≤
          (beta * ‖left - right‖) * ‖left - right‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
      _ = beta * ‖left - right‖ ^ 2 := by ring
  have hcauchy :
      -(‖gradient left - gradient right‖ * ‖left - right‖) ≤
        ⟪gradient left - gradient right, left - right⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  linarith

/-- The source budget compiles into the existing regional PC certificate.
The task-gradient Lipschitz rate is used conservatively for both `rho` and
`beta`; a sharper source-specific hypomonotonicity proof may replace it. -/
noncomputable def PullbackGradientBudget.toRegionalTaskGradientCertificate
    {readout : State → Feature}
    {pullback : State → Feature →L[ℝ] State}
    {outputGradient : Feature → Feature}
    {center : State}
    {radius readoutRate pullbackRate pullbackVariation
      outputGradientRate outputGradientBound precision : ℝ}
    (budget : PullbackGradientBudget readout pullback outputGradient center
      radius readoutRate pullbackRate pullbackVariation
      outputGradientRate outputGradientBound)
    (hdominates :
      pullbackGradientRate readoutRate pullbackRate pullbackVariation
        outputGradientRate outputGradientBound < precision)
    (hstationary :
      errorCoordinateEnergyGradient precision
        (pullbackTaskGradient readout pullback outputGradient) center = 0) :
    RegionalTaskGradientCertificate precision
      (pullbackGradientRate readoutRate pullbackRate pullbackVariation
        outputGradientRate outputGradientBound)
      (pullbackGradientRate readoutRate pullbackRate pullbackVariation
        outputGradientRate outputGradientBound)
      (pullbackTaskGradient readout pullback outputGradient) center radius where
  rho_nonneg := budget.pullbackGradientRate_nonneg
  beta_nonneg := budget.pullbackGradientRate_nonneg
  radius_nonneg := budget.radius_nonneg
  precision_dominates := hdominates
  energy_stationary := hstationary
  task_hypomonotone_on_ball :=
    lipschitz_pair_bound_implies_hypomonotone
      (pullbackTaskGradient readout pullback outputGradient) center radius
      (pullbackGradientRate readoutRate pullbackRate pullbackVariation
        outputGradientRate outputGradientBound)
      budget.pullbackGradientRate_nonneg
      budget.taskGradient_lipschitz_on_ball
  task_lipschitz_on_ball := budget.taskGradient_lipschitz_on_ball

/-! ## Constructor from an audited forward Jacobian -/

section AdjointJacobian

variable [CompleteSpace State] [CompleteSpace Feature]

/-- Reverse-mode pullback obtained from the adjoint of a declared forward
Jacobian. -/
def adjointJacobianPullback
    (jacobian : State → State →L[ℝ] Feature)
    (state : State) : Feature →L[ℝ] State :=
  (jacobian state)†

/-- The corresponding source-facing certificate.  Unlike
`PullbackGradientBudget`, this interface asks only for forward-Jacobian
operator bounds; adjoint isometry supplies the reverse-mode bounds. -/
structure ForwardJacobianGradientBudget
    (readout : State → Feature)
    (jacobian : State → State →L[ℝ] Feature)
    (outputGradient : Feature → Feature)
    (center : State) (radius readoutRate jacobianRate
      jacobianVariation outputGradientRate outputGradientBound : ℝ) where
  radius_nonneg : 0 ≤ radius
  readoutRate_nonneg : 0 ≤ readoutRate
  jacobianRate_nonneg : 0 ≤ jacobianRate
  jacobianVariation_nonneg : 0 ≤ jacobianVariation
  outputGradientRate_nonneg : 0 ≤ outputGradientRate
  outputGradientBound_nonneg : 0 ≤ outputGradientBound
  readout_lipschitz_on_ball : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖readout left - readout right‖ ≤ readoutRate * ‖left - right‖
  jacobian_norm_on_ball : ∀ state,
    InClosedBall center radius state → ‖jacobian state‖ ≤ jacobianRate
  jacobian_variation_on_ball : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖jacobian left - jacobian right‖ ≤
      jacobianVariation * ‖left - right‖
  outputGradient_lipschitz_on_image : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖outputGradient (readout left) - outputGradient (readout right)‖ ≤
      outputGradientRate * ‖readout left - readout right‖
  outputGradient_norm_on_image : ∀ state,
    InClosedBall center radius state →
    ‖outputGradient (readout state)‖ ≤ outputGradientBound

/-- Forward operator-norm bounds transport without loss through adjoint. -/
noncomputable def ForwardJacobianGradientBudget.toPullbackGradientBudget
    {readout : State → Feature}
    {jacobian : State → State →L[ℝ] Feature}
    {outputGradient : Feature → Feature}
    {center : State}
    {radius readoutRate jacobianRate jacobianVariation
      outputGradientRate outputGradientBound : ℝ}
    (budget : ForwardJacobianGradientBudget readout jacobian outputGradient
      center radius readoutRate jacobianRate jacobianVariation
      outputGradientRate outputGradientBound) :
    PullbackGradientBudget readout (adjointJacobianPullback jacobian)
      outputGradient center radius readoutRate jacobianRate
      jacobianVariation outputGradientRate outputGradientBound where
  radius_nonneg := budget.radius_nonneg
  readoutRate_nonneg := budget.readoutRate_nonneg
  pullbackRate_nonneg := budget.jacobianRate_nonneg
  pullbackVariation_nonneg := budget.jacobianVariation_nonneg
  outputGradientRate_nonneg := budget.outputGradientRate_nonneg
  outputGradientBound_nonneg := budget.outputGradientBound_nonneg
  readout_lipschitz_on_ball := budget.readout_lipschitz_on_ball
  pullback_action_on_ball := by
    intro state feature hstate
    calc
      ‖adjointJacobianPullback jacobian state feature‖ ≤
          ‖adjointJacobianPullback jacobian state‖ * ‖feature‖ :=
        (adjointJacobianPullback jacobian state).le_opNorm feature
      _ = ‖jacobian state‖ * ‖feature‖ := by
        rw [adjointJacobianPullback, ContinuousLinearMap.adjoint.norm_map]
      _ ≤ jacobianRate * ‖feature‖ :=
        mul_le_mul_of_nonneg_right
          (budget.jacobian_norm_on_ball state hstate) (norm_nonneg _)
  pullback_variation_on_ball := by
    intro left right feature hleft hright
    have hadjoint :
        adjointJacobianPullback jacobian left -
            adjointJacobianPullback jacobian right =
          (jacobian left - jacobian right)† := by
      simp [adjointJacobianPullback]
    rw [hadjoint]
    calc
      ‖((jacobian left - jacobian right)†) feature‖ ≤
          ‖(jacobian left - jacobian right)†‖ * ‖feature‖ :=
        ((jacobian left - jacobian right)†).le_opNorm feature
      _ = ‖jacobian left - jacobian right‖ * ‖feature‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ (jacobianVariation * ‖left - right‖) * ‖feature‖ :=
        mul_le_mul_of_nonneg_right
          (budget.jacobian_variation_on_ball left right hleft hright)
          (norm_nonneg _)
  outputGradient_lipschitz_on_image :=
    budget.outputGradient_lipschitz_on_image
  outputGradient_norm_on_image := budget.outputGradient_norm_on_image

/-- When one operator bound controls both forward motion and the Jacobian,
the transport coefficient has the familiar `B^2 L + H G` form. -/
theorem pullbackGradientRate_same_bound
    (bound variation outputRate outputBound : ℝ) :
    pullbackGradientRate bound bound variation outputRate outputBound =
      bound ^ 2 * outputRate + variation * outputBound := by
  unfold pullbackGradientRate
  ring

end AdjointJacobian

/-! ## Exact affine fixture -/

def scalarReadoutTwo (state : ℝ) : ℝ := 2 * state

noncomputable def scalarPullbackTwo (_state : ℝ) : ℝ →L[ℝ] ℝ :=
  2 • ContinuousLinearMap.id ℝ ℝ

def scalarQuadraticOutputGradient (feature : ℝ) : ℝ := feature

noncomputable def scalarAffineQuadraticBudget :
    PullbackGradientBudget scalarReadoutTwo scalarPullbackTwo
      scalarQuadraticOutputGradient 0 1 2 2 0 1 2 where
  radius_nonneg := by norm_num
  readoutRate_nonneg := by norm_num
  pullbackRate_nonneg := by norm_num
  pullbackVariation_nonneg := by norm_num
  outputGradientRate_nonneg := by norm_num
  outputGradientBound_nonneg := by norm_num
  readout_lipschitz_on_ball := by
    intro left right _ _
    norm_num [scalarReadoutTwo, Real.norm_eq_abs]
    rw [show 2 * left - 2 * right = 2 * (left - right) by ring, abs_mul]
    norm_num
  pullback_action_on_ball := by
    intro state feature _
    norm_num [scalarPullbackTwo, Real.norm_eq_abs, abs_mul]
  pullback_variation_on_ball := by
    intro left right feature _ _
    simp [scalarPullbackTwo]
  outputGradient_lipschitz_on_image := by
    intro left right _ _
    simp [scalarQuadraticOutputGradient]
  outputGradient_norm_on_image := by
    intro state hstate
    change |2 * state| ≤ 2
    rw [abs_mul]
    norm_num [InClosedBall, Real.norm_eq_abs] at hstate ⊢
    linarith

theorem scalarAffineQuadratic_rate :
    pullbackGradientRate 2 2 0 1 2 = 4 := by
  norm_num [pullbackGradientRate]

theorem scalarAffineQuadratic_taskGradient (state : ℝ) :
    pullbackTaskGradient scalarReadoutTwo scalarPullbackTwo
      scalarQuadraticOutputGradient state = 4 * state := by
  norm_num [pullbackTaskGradient, scalarReadoutTwo, scalarPullbackTwo,
    scalarQuadraticOutputGradient]
  ring

noncomputable def scalarAffineQuadraticRegionalCertificate :
    RegionalTaskGradientCertificate 5 4 4
      (pullbackTaskGradient scalarReadoutTwo scalarPullbackTwo
        scalarQuadraticOutputGradient) 0 1 := by
  convert scalarAffineQuadraticBudget.toRegionalTaskGradientCertificate
    (precision := 5)
    (by norm_num [pullbackGradientRate])
    (by norm_num [errorCoordinateEnergyGradient,
      scalarAffineQuadratic_taskGradient]) using 1 <;>
    norm_num [pullbackGradientRate]

/-! ## Nonlinear fixture: the pullback-variation term is necessary -/

def scalarSquareReadout (state : ℝ) : ℝ := state ^ 2 / 2

noncomputable def scalarStatePullback (state : ℝ) : ℝ →L[ℝ] ℝ :=
  state • ContinuousLinearMap.id ℝ ℝ

def constantOutputGradient (_feature : ℝ) : ℝ := 1

noncomputable def scalarNonlinearConstantCreditBudget :
    PullbackGradientBudget scalarSquareReadout scalarStatePullback
      constantOutputGradient 0 1 2 1 1 0 1 where
  radius_nonneg := by norm_num
  readoutRate_nonneg := by norm_num
  pullbackRate_nonneg := by norm_num
  pullbackVariation_nonneg := by norm_num
  outputGradientRate_nonneg := by norm_num
  outputGradientBound_nonneg := by norm_num
  readout_lipschitz_on_ball := by
    intro left right hleft hright
    rw [show scalarSquareReadout left - scalarSquareReadout right =
        (left - right) * (left + right) / 2 by
      simp [scalarSquareReadout]
      ring]
    rw [Real.norm_eq_abs, abs_div, abs_mul]
    norm_num [InClosedBall, Real.norm_eq_abs] at hleft hright ⊢
    have hsum : |left + right| ≤ 2 := by
      calc
        |left + right| ≤ |left| + |right| := abs_add_le _ _
        _ ≤ 2 := by linarith
    nlinarith [abs_nonneg (left - right)]
  pullback_action_on_ball := by
    intro state feature hstate
    norm_num [scalarStatePullback, Real.norm_eq_abs, abs_mul,
      InClosedBall] at hstate ⊢
    simpa using mul_le_mul_of_nonneg_right hstate (abs_nonneg feature)
  pullback_variation_on_ball := by
    intro left right feature _ _
    norm_num [scalarStatePullback, Real.norm_eq_abs]
    rw [show left * feature - right * feature =
        (left - right) * feature by ring, abs_mul]
  outputGradient_lipschitz_on_image := by
    intro left right _ _
    simp [constantOutputGradient]
  outputGradient_norm_on_image := by
    intro state _
    norm_num [constantOutputGradient]

theorem scalarNonlinearConstantCredit_rate :
    pullbackGradientRate 2 1 1 0 1 = 1 := by
  norm_num [pullbackGradientRate]

theorem scalarNonlinearConstantCredit_taskGradient (state : ℝ) :
    pullbackTaskGradient scalarSquareReadout scalarStatePullback
      constantOutputGradient state = state := by
  norm_num [pullbackTaskGradient, scalarStatePullback,
    constantOutputGradient]

/-- Omitting `pullbackVariation * outputGradientBound` would assign rate zero
to this nonlinear pullback, although its pulled-back task gradient changes by
one between zero and one. -/
theorem scalarNonlinear_variation_term_is_necessary :
    ¬ (∀ left right : ℝ,
      InClosedBall 0 1 left → InClosedBall 0 1 right →
      ‖pullbackTaskGradient scalarSquareReadout scalarStatePullback
          constantOutputGradient left -
        pullbackTaskGradient scalarSquareReadout scalarStatePullback
          constantOutputGradient right‖ ≤
        (1 * 0 * 2) * ‖left - right‖) := by
  intro h
  have hbad := h 1 0 (by norm_num [InClosedBall])
    (by norm_num [InClosedBall])
  norm_num [scalarNonlinearConstantCredit_taskGradient] at hbad

#print axioms PullbackGradientBudget.taskGradient_lipschitz_on_ball
#print axioms lipschitz_pair_bound_implies_hypomonotone
#print axioms PullbackGradientBudget.toRegionalTaskGradientCertificate
#print axioms ForwardJacobianGradientBudget.toPullbackGradientBudget
#print axioms scalarAffineQuadraticRegionalCertificate
#print axioms scalarNonlinear_variation_term_is_necessary

end

end NonlinearReadoutGradientTransport

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
