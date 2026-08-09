import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.BacktrackingDescent
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.RankedDAGTensorSubstitution

/-!
# Certified inexact damped descent

This file gives the solver license used by the ranked-DAG predictive-coding
boundary.  A coercive damped operator may be solved inexactly: if its linear
residual is strictly smaller than the coercivity margin times the proposed
step norm, the proposed step is a genuine descent direction.  A standard
quadratic upper bound then makes geometric Armijo backtracking terminate.

The damping changes the direction equation, not the energy.  An exact damped
direction is zero exactly at a zero energy gradient.  Under explicit local
strong monotonicity and credit-Lipschitz assumptions, gradient residual also
controls credit error.  A scalar counterexample records that no such credit
bound follows without those assumptions.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped InnerProductSpace

section CertifiedDirection

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- Coercivity with an explicit lower constant. -/
def CoerciveWith
    (operator : State →L[ℝ] State) (lower : ℝ) : Prop :=
  ∀ direction,
    lower * ‖direction‖ ^ 2 ≤ ⟪operator direction, direction⟫_ℝ

/-- Residual certificate for an inexact solution of
`operator direction + gradient = 0`. -/
def InexactDampedDirectionCertificate
    (operator : State →L[ℝ] State) (gradient direction : State)
    (lower : ℝ) : Prop :=
  CoerciveWith operator lower ∧
    ‖operator direction + gradient‖ < lower * ‖direction‖

/-- A coercive inexact damped solve is a strict descent direction whenever
its residual lies strictly inside the coercivity margin. -/
theorem inexactDampedDirection_inner_lt_zero
    (operator : State →L[ℝ] State) (gradient direction : State)
    (lower : ℝ) (_hlower : 0 < lower)
    (hcertificate :
      InexactDampedDirectionCertificate operator gradient direction lower) :
    ⟪gradient, direction⟫_ℝ < 0 := by
  have hdirection : direction ≠ 0 := by
    intro hzero
    subst direction
    have himpossible := hcertificate.2
    simp only [map_zero, zero_add, norm_zero, mul_zero] at himpossible
    exact (not_lt_of_ge (norm_nonneg gradient)) himpossible
  have hnorm : 0 < ‖direction‖ := norm_pos_iff.mpr hdirection
  have hcoercive := hcertificate.1 direction
  have hcauchy := real_inner_le_norm
    (operator direction + gradient) direction
  have hresidual := hcertificate.2
  have hresidualMul :
      ‖operator direction + gradient‖ * ‖direction‖ <
        lower * ‖direction‖ ^ 2 := by
    nlinarith
  rw [inner_add_left] at hcauchy
  nlinarith

/-- Armijo sufficient decrease along an arbitrary proposed direction. -/
def directionalArmijoCondition
    (energy : State → ℝ) (state gradient direction : State)
    (c step : ℝ) : Prop :=
  energy (state + step • direction) ≤
    energy state + c * step * ⟪gradient, direction⟫_ℝ

/-- Local quadratic upper model along an arbitrary proposed direction.  This
is the differentiability/smoothness assumption needed by the Armijo proof. -/
def HasDirectionalDescentUpperBoundAt
    (energy : State → ℝ) (state gradient direction : State)
    (smoothness : ℝ) : Prop :=
  ∀ step, 0 ≤ step →
    energy (state + step • direction) ≤
      energy state + step * ⟪gradient, direction⟫_ℝ +
        (smoothness / 2) * step ^ 2 * ‖direction‖ ^ 2

theorem directionalArmijoCondition_of_upperBound
    (energy : State → ℝ) (state gradient direction : State)
    (smoothness c step : ℝ)
    (hsmoothness : 0 < smoothness)
    (hdescent : ⟪gradient, direction⟫_ℝ < 0)
    (hstep0 : 0 ≤ step)
    (hstep : step ≤
      2 * (1 - c) * (-⟪gradient, direction⟫_ℝ) /
        (smoothness * ‖direction‖ ^ 2))
    (hupper : HasDirectionalDescentUpperBoundAt
      energy state gradient direction smoothness) :
    directionalArmijoCondition energy state gradient direction c step := by
  have hdirection : direction ≠ 0 := by
    intro hzero
    subst direction
    simp at hdescent
  have hnormSq : 0 < ‖direction‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hdirection)
  have hdenominator : 0 < smoothness * ‖direction‖ ^ 2 := mul_pos hsmoothness hnormSq
  have hscaled := (le_div_iff₀ hdenominator).mp hstep
  have hstepScaled :
      step * (step * (smoothness * ‖direction‖ ^ 2)) ≤
        step * (2 * (1 - c) * (-⟪gradient, direction⟫_ℝ)) :=
    mul_le_mul_of_nonneg_left hscaled hstep0
  have henergy := hupper step hstep0
  unfold directionalArmijoCondition
  nlinarith

/-- Geometric Armijo backtracking terminates for every certified strict
descent direction satisfying the explicit local quadratic upper bound. -/
theorem directionalArmijoBacktracking_terminates
    (energy : State → ℝ) (state gradient direction : State)
    (smoothness c initial shrink : ℝ)
    (hsmoothness : 0 < smoothness) (_hc0 : 0 ≤ c) (hc1 : c < 1)
    (hinitial : 0 < initial) (hshrink0 : 0 < shrink) (hshrink1 : shrink < 1)
    (hdescent : ⟪gradient, direction⟫_ℝ < 0)
    (hupper : HasDirectionalDescentUpperBoundAt
      energy state gradient direction smoothness) :
    ∃ iterations : ℕ,
      directionalArmijoCondition energy state gradient direction c
        (initial * shrink ^ iterations) := by
  have hdirection : direction ≠ 0 := by
    intro hzero
    subst direction
    simp at hdescent
  let threshold :=
    2 * (1 - c) * (-⟪gradient, direction⟫_ℝ) /
      (smoothness * ‖direction‖ ^ 2)
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    have honeMinus : 0 < 1 - c := sub_pos.mpr hc1
    have hnegativeInner : 0 < -⟪gradient, direction⟫_ℝ := neg_pos.mpr hdescent
    have hnormSq : 0 < ‖direction‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hdirection)
    exact div_pos
      (mul_pos (mul_pos (by norm_num) honeMinus) hnegativeInner)
      (mul_pos hsmoothness hnormSq)
  obtain ⟨iterations, hiterations⟩ :=
    geometric_backtracking_reaches_threshold
      initial shrink threshold hinitial hshrink1 hthreshold
  refine ⟨iterations, directionalArmijoCondition_of_upperBound
    energy state gradient direction smoothness c
      (initial * shrink ^ iterations) hsmoothness hdescent ?_
      (le_of_lt hiterations) hupper⟩
  exact mul_nonneg hinitial.le (pow_nonneg hshrink0.le _)

/-- The inexact coercive residual certificate directly licenses terminating
geometric Armijo backtracking under the stated directional upper model. -/
theorem inexactDampedDirection_armijoBacktracking_terminates
    (operator : State →L[ℝ] State)
    (energy : State → ℝ) (state gradient direction : State)
    (lower smoothness c initial shrink : ℝ)
    (hlower : 0 < lower) (hsmoothness : 0 < smoothness)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hinitial : 0 < initial) (hshrink0 : 0 < shrink) (hshrink1 : shrink < 1)
    (hcertificate :
      InexactDampedDirectionCertificate operator gradient direction lower)
    (hupper : HasDirectionalDescentUpperBoundAt
      energy state gradient direction smoothness) :
    ∃ iterations : ℕ,
      directionalArmijoCondition energy state gradient direction c
        (initial * shrink ^ iterations) := by
  exact directionalArmijoBacktracking_terminates
    energy state gradient direction smoothness c initial shrink hsmoothness
      hc0 hc1 hinitial hshrink0 hshrink1
      (inexactDampedDirection_inner_lt_zero
        operator gradient direction lower hlower hcertificate)
      hupper

/-- A positive coercivity constant makes the damped operator injective at
zero. -/
theorem coerciveWith_apply_eq_zero_iff
    (operator : State →L[ℝ] State) (lower : ℝ)
    (hlower : 0 < lower) (hcoercive : CoerciveWith operator lower)
    (direction : State) :
    operator direction = 0 ↔ direction = 0 := by
  constructor
  · intro hzero
    by_contra hdirection
    have hnorm : 0 < ‖direction‖ := norm_pos_iff.mpr hdirection
    have hbound := hcoercive direction
    rw [hzero] at hbound
    simp at hbound
    nlinarith [sq_pos_of_pos hnorm]
  · rintro rfl
    simp

/-- Solving a coercive damped equation changes the step but preserves the
unchanged energy's stationary set: the exact proposed step is zero exactly
when the original gradient is zero. -/
theorem exactDampedDirection_zero_iff_gradient_zero
    (operator : State →L[ℝ] State) (gradient direction : State)
    (lower : ℝ) (hlower : 0 < lower)
    (hcoercive : CoerciveWith operator lower)
    (hequation : operator direction + gradient = 0) :
    direction = 0 ↔ gradient = 0 := by
  constructor
  · rintro rfl
    simpa using hequation
  · intro hgradient
    rw [hgradient, add_zero] at hequation
    exact (coerciveWith_apply_eq_zero_iff
      operator lower hlower hcoercive direction).1 hequation

end CertifiedDirection

/-! ## Residual-to-credit control -/

section CreditBound

variable {State Credit : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]
  [NormedAddCommGroup Credit]

/-- Local strong monotonicity of the state gradient around a reference
stationary point. -/
def LocallyStronglyMonotoneAt
    (gradient : State → State) (reference : State) (lower : ℝ) : Prop :=
  ∀ state,
    lower * ‖state - reference‖ ^ 2 ≤
      ⟪gradient state - gradient reference, state - reference⟫_ℝ

/-- Local Lipschitz control of detached credit around the same reference
point. -/
def CreditLipschitzAt
    (credit : State → Credit) (reference : State) (constant : ℝ) : Prop :=
  ∀ state,
    ‖credit state - credit reference‖ ≤ constant * ‖state - reference‖

/-- Under explicit local monotonicity and credit-Lipschitz constants, state
gradient residual controls detached-credit error by `K * ‖g‖ / μ`. -/
theorem creditError_le_lipschitz_mul_gradient_div_monotonicity
    (gradient : State → State) (credit : State → Credit)
    (reference state : State) (lower constant : ℝ)
    (hlower : 0 < lower) (hconstant : 0 ≤ constant)
    (hstationary : gradient reference = 0)
    (hmonotone : LocallyStronglyMonotoneAt gradient reference lower)
    (hlipschitz : CreditLipschitzAt credit reference constant) :
    ‖credit state - credit reference‖ ≤
      constant * ‖gradient state‖ / lower := by
  by_cases hstate : state = reference
  · subst state
    rw [hstationary]
    simp
  · have hdistance : 0 < ‖state - reference‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hstate)
    have hmonotoneState := hmonotone state
    rw [hstationary, sub_zero] at hmonotoneState
    have hcauchy := real_inner_le_norm (gradient state) (state - reference)
    have hgradientDistance :
        lower * ‖state - reference‖ ≤ ‖gradient state‖ := by
      nlinarith
    apply (le_div_iff₀ hlower).2
    calc
      ‖credit state - credit reference‖ * lower ≤
          (constant * ‖state - reference‖) * lower :=
        mul_le_mul_of_nonneg_right (hlipschitz state) hlower.le
      _ = constant * (lower * ‖state - reference‖) := by ring
      _ ≤ constant * ‖gradient state‖ :=
        mul_le_mul_of_nonneg_left hgradientDistance hconstant

/-- Negative boundary: without monotonicity and credit-Lipschitz assumptions,
zero gradient residual can coexist with nonzero credit error, defeating every
bound of the proposed form. -/
theorem creditErrorBound_fails_without_regularities (constant : ℝ) :
    |(fun state : ℝ => state) 1 - (fun state : ℝ => state) 0| >
      constant * |(fun _state : ℝ => 0) 1| := by
  norm_num

end CreditBound

/-! ## Composition with the ranked-DAG coordinate equivalence -/

section RankedDAGComposition

variable {Node Edge Coord Credit SolverState : Type*}
  [Fintype Node] [Fintype Edge] [Fintype Coord]
  [DecidableEq Node] [DecidableEq Coord]
  [NormedAddCommGroup Credit]
  [NormedAddCommGroup SolverState] [InnerProductSpace ℝ SolverState]

/-- The residual-to-credit bound transports directly through the exact
ranked-DAG error-to-state reconstruction. -/
theorem rankedDAG_errorCoordinate_creditError_bound
    (G : RankedDAGTensor Node Edge Coord)
    (toSolverState : (Coord → ℝ) → SolverState)
    (gradient : SolverState → SolverState)
    (credit : SolverState → Credit)
    (referenceError error : Coord → ℝ) (lower constant : ℝ)
    (hlower : 0 < lower) (hconstant : 0 ≤ constant)
    (hstationary : gradient
      (toSolverState (rankedDAGErrorToState G referenceError)) = 0)
    (hmonotone : LocallyStronglyMonotoneAt gradient
      (toSolverState (rankedDAGErrorToState G referenceError)) lower)
    (hlipschitz : CreditLipschitzAt credit
      (toSolverState (rankedDAGErrorToState G referenceError)) constant) :
    ‖credit (toSolverState (rankedDAGErrorToState G error)) -
        credit (toSolverState (rankedDAGErrorToState G referenceError))‖ ≤
      constant *
        ‖gradient (toSolverState (rankedDAGErrorToState G error))‖ / lower := by
  exact creditError_le_lipschitz_mul_gradient_div_monotonicity
    gradient credit (toSolverState (rankedDAGErrorToState G referenceError))
      (toSolverState (rankedDAGErrorToState G error))
      lower constant hlower hconstant
      hstationary hmonotone hlipschitz

/-- Exact damping, the state/error differential equivalence, and the solver
fixed-point condition compose: zero damped step is equivalent to a critical
point of the unchanged state-coordinate energy. -/
theorem rankedDAG_exactDampedDirection_zero_iff_stateCritical
    (G : RankedDAGTensor Node Edge Coord)
    (operator : SolverState →L[ℝ] SolverState)
    (errorGradient direction : SolverState)
    (stateDifferential : (Coord → ℝ) →L[ℝ] ℝ)
    (lower : ℝ) (hlower : 0 < lower)
    (hcoercive : CoerciveWith operator lower)
    (hequation : operator direction + errorGradient = 0)
    (hgradient : errorGradient = 0 ↔
      stateDifferential ∘L rankedDAGErrorJacobian G = 0) :
    direction = 0 ↔ stateDifferential = 0 := by
  rw [exactDampedDirection_zero_iff_gradient_zero
    operator errorGradient direction lower hlower hcoercive hequation]
  rw [hgradient]
  exact rankedDAG_criticalDifferential_iff G stateDifferential

end RankedDAGComposition

#print axioms inexactDampedDirection_inner_lt_zero
#print axioms directionalArmijoBacktracking_terminates
#print axioms inexactDampedDirection_armijoBacktracking_terminates
#print axioms exactDampedDirection_zero_iff_gradient_zero
#print axioms creditError_le_lipschitz_mul_gradient_div_monotonicity
#print axioms creditErrorBound_fails_without_regularities
#print axioms rankedDAG_errorCoordinate_creditError_bound
#print axioms rankedDAG_exactDampedDirection_zero_iff_stateCritical

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
