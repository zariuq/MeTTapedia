import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactForwardBackward

/-!
# Residual certificates for approximate implicit solves

A global approximation bound for a learned or truncated resolver can be hard
to establish directly.  The defining equation of a monotone resolvent gives an
observable alternative.  If a proposed output nearly reconstructs its input
through `y + A y`, firm nonexpansiveness bounds its distance from the exact
implicit solution.

This file turns that equation residual into pointwise and uniform solver-error
certificates, one-step and adaptive-stopping bounds for nonlinear
forward--backward inference, and a variable-error finite-trajectory theorem.
The positive fixture attains the residual bound on a branch of a globally
nonlinear resolvent.  The negative fixture shows that the raw input--output
distance is not a valid substitute for the resolvent-equation residual.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ResolverResidual

open scoped InnerProductSpace
open NonlinearResolvent
open NonlinearForwardBackward
open InexactForwardBackward
open AmortizedInitialization

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-! ## Equation residual and exact-solver distance -/

/-- Residual of the unit-resolvent equation at a proposed output. -/
def resolverEquationResidual
    (operator : State → State) (input output : State) : State :=
  output + operator output - input

/-- A proof-carrying uniform bound on an approximate resolver's defining
equation residual. -/
structure ResolverResidualCertificate
    (operator approximateResolver : State → State) where
  error : ℝ
  error_nonneg : 0 ≤ error
  residual_le : ∀ input,
    ‖resolverEquationResidual operator input (approximateResolver input)‖ ≤ error

/-- Feeding a candidate's reconstructed input through an exact monotone
resolvent returns the candidate. -/
theorem exactResolvent_reconstructedInput
    {operator resolvent : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator resolvent)
    (candidate : State) :
    resolvent (candidate + operator candidate) = candidate := by
  apply monotone_shift_solution_unique monotone
    (resolventEquation (candidate + operator candidate))
  rfl

/-- The resolvent-equation residual of one proposed output bounds its distance
from the exact implicit solution at the same input. -/
theorem distance_exactResolvent_le_equationResidual
    {operator resolvent : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator resolvent)
    (input candidate : State) :
    ‖candidate - resolvent input‖ ≤
      ‖resolverEquationResidual operator input candidate‖ := by
  have hfirm := FirmlyNonexpansiveMap.norm_sub_le
    (firmlyNonexpansive_of_monotone_resolvent monotone resolventEquation)
    (candidate + operator candidate) input
  rw [exactResolvent_reconstructedInput monotone resolventEquation candidate] at hfirm
  simpa [resolverEquationResidual] using hfirm

/-- Zero equation residual recovers the exact resolvent output, without an
inverse-function premise. -/
theorem zero_equationResidual_forces_exactResolverOutput
    {operator resolvent : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator resolvent)
    (input candidate : State)
    (hzero : resolverEquationResidual operator input candidate = 0) :
    candidate = resolvent input := by
  have hdistance := distance_exactResolvent_le_equationResidual
    monotone resolventEquation input candidate
  rw [hzero, norm_zero] at hdistance
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hdistance)

/-- A uniform equation-residual certificate induces the uniform map
approximation required by the inexact-iteration calculus. -/
theorem uniformApproximation_of_resolverResidual
    {operator exactResolver approximateResolver : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator exactResolver)
    (certificate : ResolverResidualCertificate operator approximateResolver) :
    UniformApproximation exactResolver approximateResolver certificate.error := by
  intro input
  exact (distance_exactResolvent_le_equationResidual
    monotone resolventEquation input (approximateResolver input)).trans
      (certificate.residual_le input)

/-- Package a residual-certified approximate resolver as an inexact map. -/
def inexactResolverCertificate_of_residual
    {operator exactResolver approximateResolver : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator exactResolver)
    (certificate : ResolverResidualCertificate operator approximateResolver) :
    InexactMapCertificate exactResolver approximateResolver where
  error := certificate.error
  error_nonneg := certificate.error_nonneg
  approximates := uniformApproximation_of_resolverResidual
    monotone resolventEquation certificate

/-- Package the full approximate forward--backward map from a residual
certificate on its implicit resolver. -/
def inexactForwardBackwardCertificate_of_residual
    {operator exactResolver approximateResolver forwardOperator : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator exactResolver)
    (certificate : ResolverResidualCertificate operator approximateResolver) :
    InexactMapCertificate
      (nonlinearForwardBackwardStep exactResolver forwardOperator)
      (nonlinearForwardBackwardStep approximateResolver forwardOperator) where
  error := certificate.error
  error_nonneg := certificate.error_nonneg
  approximates := uniformApproximation_forwardBackward_of_resolvent
    (uniformApproximation_of_resolverResidual
      monotone resolventEquation certificate)

/-! ## Pointwise forward--backward certificates -/

/-- One approximate implicit step is controlled by its observed equation
residual plus contraction of the previous fixed-point error. -/
theorem residualCertified_oneStep_to_fixedPoint_le
    {operator exactResolver approximateResolver forwardOperator : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator exactResolver)
    (exactCertificate : ContractionCertificate
      (nonlinearForwardBackwardStep exactResolver forwardOperator))
    (target state : State)
    (htarget : IsFixedPoint
      (nonlinearForwardBackwardStep exactResolver forwardOperator) target) :
    ‖nonlinearForwardBackwardStep approximateResolver forwardOperator state - target‖ ≤
      ‖resolverEquationResidual operator
        (explicitForwardStep forwardOperator state)
        (approximateResolver (explicitForwardStep forwardOperator state))‖ +
      exactCertificate.factor * ‖state - target‖ := by
  let exactStep := nonlinearForwardBackwardStep exactResolver forwardOperator
  let approximateStep :=
    nonlinearForwardBackwardStep approximateResolver forwardOperator
  calc
    ‖approximateStep state - target‖ ≤
        ‖approximateStep state - exactStep state‖ +
          ‖exactStep state - target‖ := by
      have htriangle := norm_add_le
        (approximateStep state - exactStep state) (exactStep state - target)
      simpa only [sub_add_sub_cancel] using htriangle
    _ ≤ ‖resolverEquationResidual operator
          (explicitForwardStep forwardOperator state)
          (approximateResolver (explicitForwardStep forwardOperator state))‖ +
        ‖exactStep state - target‖ := by
      gcongr
      exact distance_exactResolvent_le_equationResidual monotone
        resolventEquation (explicitForwardStep forwardOperator state)
        (approximateResolver (explicitForwardStep forwardOperator state))
    _ ≤ ‖resolverEquationResidual operator
          (explicitForwardStep forwardOperator state)
          (approximateResolver (explicitForwardStep forwardOperator state))‖ +
        exactCertificate.factor * ‖state - target‖ := by
      gcongr
      have hcontract := exactCertificate.contracts state target
      rw [htarget] at hcontract
      exact hcontract

/-- The current approximate step residual plus its implicit-equation residual
controls distance to the exact fixed point. -/
theorem fixedPoint_distance_le_resolverResidual_div
    {operator exactResolver approximateResolver forwardOperator : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator exactResolver)
    (exactCertificate : ContractionCertificate
      (nonlinearForwardBackwardStep exactResolver forwardOperator))
    (target state : State)
    (htarget : IsFixedPoint
      (nonlinearForwardBackwardStep exactResolver forwardOperator) target) :
    ‖state - target‖ ≤
      (‖state - nonlinearForwardBackwardStep
          approximateResolver forwardOperator state‖ +
        ‖resolverEquationResidual operator
          (explicitForwardStep forwardOperator state)
          (approximateResolver (explicitForwardStep forwardOperator state))‖) /
        (1 - exactCertificate.factor) := by
  have hdenominator : 0 < 1 - exactCertificate.factor := by
    linarith [exactCertificate.factor_lt_one]
  have hexactResidual :
      ‖state - nonlinearForwardBackwardStep exactResolver forwardOperator state‖ ≤
        ‖state - nonlinearForwardBackwardStep
          approximateResolver forwardOperator state‖ +
        ‖resolverEquationResidual operator
          (explicitForwardStep forwardOperator state)
          (approximateResolver (explicitForwardStep forwardOperator state))‖ := by
    calc
      ‖state - nonlinearForwardBackwardStep exactResolver forwardOperator state‖ ≤
          ‖state - nonlinearForwardBackwardStep
            approximateResolver forwardOperator state‖ +
          ‖nonlinearForwardBackwardStep approximateResolver forwardOperator state -
            nonlinearForwardBackwardStep exactResolver forwardOperator state‖ := by
        have htriangle := norm_add_le
          (state - nonlinearForwardBackwardStep
            approximateResolver forwardOperator state)
          (nonlinearForwardBackwardStep approximateResolver forwardOperator state -
            nonlinearForwardBackwardStep exactResolver forwardOperator state)
        simpa only [sub_add_sub_cancel] using htriangle
      _ ≤ ‖state - nonlinearForwardBackwardStep
            approximateResolver forwardOperator state‖ +
          ‖resolverEquationResidual operator
            (explicitForwardStep forwardOperator state)
            (approximateResolver (explicitForwardStep forwardOperator state))‖ := by
        gcongr
        exact distance_exactResolvent_le_equationResidual monotone
          resolventEquation (explicitForwardStep forwardOperator state)
          (approximateResolver (explicitForwardStep forwardOperator state))
  calc
    ‖state - target‖ ≤
        ‖state - nonlinearForwardBackwardStep exactResolver forwardOperator state‖ /
          (1 - exactCertificate.factor) :=
      fixedPoint_distance_le_residual_div exactCertificate target state htarget
    _ ≤ (‖state - nonlinearForwardBackwardStep
            approximateResolver forwardOperator state‖ +
          ‖resolverEquationResidual operator
            (explicitForwardStep forwardOperator state)
            (approximateResolver (explicitForwardStep forwardOperator state))‖) /
          (1 - exactCertificate.factor) :=
      (div_le_div_iff_of_pos_right hdenominator).2 hexactResidual

/-- Adaptive stopping from quantities observable at one approximate implicit
solve. -/
theorem resolverResidual_adaptiveStop
    {operator exactResolver approximateResolver forwardOperator : State → State}
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator exactResolver)
    (exactCertificate : ContractionCertificate
      (nonlinearForwardBackwardStep exactResolver forwardOperator))
    (target state : State)
    (htarget : IsFixedPoint
      (nonlinearForwardBackwardStep exactResolver forwardOperator) target)
    (tolerance : ℝ)
    (hresidual :
      ‖state - nonlinearForwardBackwardStep
          approximateResolver forwardOperator state‖ +
        ‖resolverEquationResidual operator
          (explicitForwardStep forwardOperator state)
          (approximateResolver (explicitForwardStep forwardOperator state))‖ <
        (1 - exactCertificate.factor) * tolerance) :
    ‖state - target‖ < tolerance := by
  have hdenominator : 0 < 1 - exactCertificate.factor := by
    linarith [exactCertificate.factor_lt_one]
  have hbound := fixedPoint_distance_le_resolverResidual_div
    (approximateResolver := approximateResolver) monotone
    resolventEquation exactCertificate target state htarget
  have hstrict :
      (‖state - nonlinearForwardBackwardStep
          approximateResolver forwardOperator state‖ +
        ‖resolverEquationResidual operator
          (explicitForwardStep forwardOperator state)
          (approximateResolver (explicitForwardStep forwardOperator state))‖) /
        (1 - exactCertificate.factor) < tolerance :=
    (div_lt_iff₀ hdenominator).2 (by simpa [mul_comm] using hresidual)
  exact hbound.trans_lt hstrict

/-! ## Variable-error finite trajectories -/

/-- Time-ordered accumulation of solver residual budgets. -/
def accumulatedResolverResidual
    (factor : ℝ) (errorAt : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | steps + 1 =>
      errorAt steps + factor * accumulatedResolverResidual factor errorAt steps

theorem accumulatedResolverResidual_zero (factor : ℝ) :
    ∀ steps, accumulatedResolverResidual factor (fun _ => 0) steps = 0 := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      simp [accumulatedResolverResidual, inductionHypothesis]

/-- A trajectory whose approximate implicit solver may change at every step
inherits the exact solver's geometric contraction plus the time-ordered
equation-residual budget. -/
theorem residualCertified_trajectory_to_fixedPoint_le
    {operator exactResolver forwardOperator : State → State}
    (approximateResolver : ℕ → State → State)
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator exactResolver)
    (exactCertificate : ContractionCertificate
      (nonlinearForwardBackwardStep exactResolver forwardOperator))
    (target : State)
    (htarget : IsFixedPoint
      (nonlinearForwardBackwardStep exactResolver forwardOperator) target)
    (trajectory : ℕ → State)
    (initial : State)
    (hinitial : trajectory 0 = initial)
    (errorAt : ℕ → ℝ)
    (hstep : ∀ step,
      trajectory (step + 1) = nonlinearForwardBackwardStep
        (approximateResolver step) forwardOperator (trajectory step))
    (hresidual : ∀ step,
      ‖resolverEquationResidual operator
        (explicitForwardStep forwardOperator (trajectory step))
        (approximateResolver step
          (explicitForwardStep forwardOperator (trajectory step)))‖ ≤
        errorAt step) :
    ∀ steps,
      ‖trajectory steps - target‖ ≤
        exactCertificate.factor ^ steps * ‖initial - target‖ +
          accumulatedResolverResidual exactCertificate.factor errorAt steps := by
  intro steps
  induction steps with
  | zero => simp [hinitial, accumulatedResolverResidual]
  | succ steps inductionHypothesis =>
      rw [hstep steps, pow_succ, accumulatedResolverResidual]
      calc
        ‖nonlinearForwardBackwardStep (approximateResolver steps)
            forwardOperator (trajectory steps) - target‖ ≤
            ‖resolverEquationResidual operator
              (explicitForwardStep forwardOperator (trajectory steps))
              (approximateResolver steps
                (explicitForwardStep forwardOperator (trajectory steps)))‖ +
            exactCertificate.factor * ‖trajectory steps - target‖ :=
          residualCertified_oneStep_to_fixedPoint_le monotone
            resolventEquation exactCertificate target (trajectory steps) htarget
        _ ≤ errorAt steps + exactCertificate.factor *
              (exactCertificate.factor ^ steps * ‖initial - target‖ +
                accumulatedResolverResidual exactCertificate.factor errorAt steps) := by
          have hscaled := mul_le_mul_of_nonneg_left inductionHypothesis
            exactCertificate.factor_nonneg
          linarith [hresidual steps]
        _ = exactCertificate.factor ^ steps * exactCertificate.factor *
              ‖initial - target‖ +
            (errorAt steps + exactCertificate.factor *
              accumulatedResolverResidual exactCertificate.factor errorAt steps) := by
          ring

/-- Exact satisfaction of every implicit equation removes the approximation
floor entirely, even when a different resolver implementation is used at each
step. -/
theorem zeroResidual_trajectory_to_fixedPoint_le
    {operator exactResolver forwardOperator : State → State}
    (approximateResolver : ℕ → State → State)
    (monotone : MonotoneMap operator)
    (resolventEquation : IsUnitResolventMapOf operator exactResolver)
    (exactCertificate : ContractionCertificate
      (nonlinearForwardBackwardStep exactResolver forwardOperator))
    (target : State)
    (htarget : IsFixedPoint
      (nonlinearForwardBackwardStep exactResolver forwardOperator) target)
    (trajectory : ℕ → State)
    (initial : State)
    (hinitial : trajectory 0 = initial)
    (hstep : ∀ step,
      trajectory (step + 1) = nonlinearForwardBackwardStep
        (approximateResolver step) forwardOperator (trajectory step))
    (hresidual : ∀ step,
      resolverEquationResidual operator
        (explicitForwardStep forwardOperator (trajectory step))
        (approximateResolver step
          (explicitForwardStep forwardOperator (trajectory step))) = 0) :
    ∀ steps,
      ‖trajectory steps - target‖ ≤
        exactCertificate.factor ^ steps * ‖initial - target‖ := by
  intro steps
  have hbound := residualCertified_trajectory_to_fixedPoint_le
    approximateResolver monotone resolventEquation exactCertificate target
    htarget trajectory initial hinitial (fun _ => 0) hstep (by
      intro step
      rw [hresidual step, norm_zero]) steps
  rw [accumulatedResolverResidual_zero] at hbound
  simpa using hbound

/-! ## Positive and negative residual fixtures -/

/-- On the nonpositive branch of the globally nonlinear positive-part
resolvent, the equation-residual distance bound is attained exactly. -/
theorem positivePart_negativeBranch_residualBound_attained :
    ‖(-3 / 2 : ℝ) - positivePartResolvent (-2)‖ =
      ‖resolverEquationResidual positivePartOperator (-2) (-3 / 2)‖ := by
  norm_num [positivePartResolvent, positivePartOperator,
    resolverEquationResidual, Real.norm_eq_abs]

/-- Raw input--output equality is not evidence of a solved implicit equation:
the identity proposal has zero raw residual at input two but differs from the
exact positive-part resolvent. -/
theorem rawInputOutputResidual_does_not_certify_implicitSolve :
    ‖(2 : ℝ) - 2‖ = 0 ∧ (2 : ℝ) ≠ positivePartResolvent 2 := by
  constructor
  · norm_num
  · norm_num [positivePartResolvent]

#print axioms exactResolvent_reconstructedInput
#print axioms distance_exactResolvent_le_equationResidual
#print axioms zero_equationResidual_forces_exactResolverOutput
#print axioms uniformApproximation_of_resolverResidual
#print axioms inexactForwardBackwardCertificate_of_residual
#print axioms residualCertified_oneStep_to_fixedPoint_le
#print axioms fixedPoint_distance_le_resolverResidual_div
#print axioms resolverResidual_adaptiveStop
#print axioms residualCertified_trajectory_to_fixedPoint_le
#print axioms zeroResidual_trajectory_to_fixedPoint_le
#print axioms positivePart_negativeBranch_residualBound_attained
#print axioms rawInputOutputResidual_does_not_certify_implicitSolve

end

end ResolverResidual

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
