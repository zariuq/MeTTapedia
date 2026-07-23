import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearForwardBackward

/-!
# Inexact nonlinear forward--backward inference

Exact implicit solves can be too expensive to use at every learning step.  A
truncated solver or learned initializer is useful only if its error is exposed
rather than silently identified with the exact resolvent.  This file carries a
uniform one-step approximation budget through a contractive exact solver.

The resulting bounds separate transient initializer error from accumulated
solver error, prove the geometric error floor, and give a residual stopping
rule that remains sound for the inexact map.  A biased half-solver attains the
error floor exactly and moves the fixed point, showing why nonzero approximation
error cannot be treated as exact equilibrium preservation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace InexactForwardBackward

open NonlinearForwardBackward
open AmortizedInitialization

noncomputable section

variable {State : Type*} [NormedAddCommGroup State]

/-! ## Uniform approximation and resolvent transport -/

/-- A pointwise uniform approximation budget between two solver maps. -/
def UniformApproximation
    (exact approximate : State → State) (error : ℝ) : Prop :=
  ∀ state, ‖approximate state - exact state‖ ≤ error

/-- Proof-carrying inexact-map certificate. -/
structure InexactMapCertificate
    (exact approximate : State → State) where
  error : ℝ
  error_nonneg : 0 ≤ error
  approximates : UniformApproximation exact approximate error

/-- A uniform approximation of the implicit resolvent induces the same
uniform approximation of the complete forward--backward map. -/
theorem uniformApproximation_forwardBackward_of_resolvent
    {exactResolvent approximateResolvent forwardOperator : State → State}
    {error : ℝ}
    (approximation :
      UniformApproximation exactResolvent approximateResolvent error) :
    UniformApproximation
      (nonlinearForwardBackwardStep exactResolvent forwardOperator)
      (nonlinearForwardBackwardStep approximateResolvent forwardOperator)
      error := by
  intro state
  exact approximation (explicitForwardStep forwardOperator state)

/-! ## Finite-time error transport -/

/-- Accumulated additive error after repeated contraction and injection of one
fresh approximation error at every step. -/
def accumulatedApproximationError
    (factor error : ℝ) : ℕ → ℝ
  | 0 => 0
  | steps + 1 => error + factor * accumulatedApproximationError factor error steps

theorem accumulatedApproximationError_nonneg
    {factor error : ℝ}
    (hfactor : 0 ≤ factor) (herror : 0 ≤ error) :
    ∀ steps, 0 ≤ accumulatedApproximationError factor error steps := by
  intro steps
  induction steps with
  | zero => simp [accumulatedApproximationError]
  | succ steps inductionHypothesis =>
      rw [accumulatedApproximationError]
      positivity

/-- One approximate step incurs the declared solver error plus the exact
contraction of the current fixed-point error. -/
theorem inexact_oneStep_to_fixedPoint_le
    {exact approximate : State → State}
    (exactCertificate : ContractionCertificate exact)
    (approximation : InexactMapCertificate exact approximate)
    (target state : State)
    (htarget : IsFixedPoint exact target) :
    ‖approximate state - target‖ ≤
      approximation.error +
        exactCertificate.factor * ‖state - target‖ := by
  calc
    ‖approximate state - target‖ ≤
        ‖approximate state - exact state‖ + ‖exact state - target‖ := by
      have htriangle := norm_add_le
        (approximate state - exact state) (exact state - target)
      simpa only [sub_add_sub_cancel] using htriangle
    _ ≤ approximation.error + ‖exact state - target‖ := by
      gcongr
      exact approximation.approximates state
    _ ≤ approximation.error +
          exactCertificate.factor * ‖state - target‖ := by
      gcongr
      have hcontract := exactCertificate.contracts state target
      rw [htarget] at hcontract
      exact hcontract

/-- Repeated approximate inference separates the geometrically decaying
initializer error from the accumulated per-step solver error. -/
theorem inexact_iterate_to_fixedPoint_le
    {exact approximate : State → State}
    (exactCertificate : ContractionCertificate exact)
    (approximation : InexactMapCertificate exact approximate)
    (target initial : State)
    (htarget : IsFixedPoint exact target) :
    ∀ steps,
      ‖approximate^[steps] initial - target‖ ≤
        exactCertificate.factor ^ steps * ‖initial - target‖ +
          accumulatedApproximationError exactCertificate.factor
            approximation.error steps := by
  intro steps
  induction steps with
  | zero => simp [accumulatedApproximationError]
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', pow_succ,
        accumulatedApproximationError]
      calc
        ‖approximate (approximate^[steps] initial) - target‖ ≤
            approximation.error + exactCertificate.factor *
              ‖approximate^[steps] initial - target‖ :=
          inexact_oneStep_to_fixedPoint_le exactCertificate approximation
            target (approximate^[steps] initial) htarget
        _ ≤ approximation.error + exactCertificate.factor *
              (exactCertificate.factor ^ steps * ‖initial - target‖ +
                accumulatedApproximationError exactCertificate.factor
                  approximation.error steps) := by
          have hscaled := mul_le_mul_of_nonneg_left inductionHypothesis
            exactCertificate.factor_nonneg
          linarith
        _ = exactCertificate.factor ^ steps *
              exactCertificate.factor * ‖initial - target‖ +
            (approximation.error + exactCertificate.factor *
              accumulatedApproximationError exactCertificate.factor
                approximation.error steps) := by ring

/-- The accumulated approximation term never exceeds the familiar geometric
error floor `error / (1-factor)`. -/
theorem accumulatedApproximationError_le_floor
    {factor error : ℝ}
    (hfactorNonneg : 0 ≤ factor)
    (hfactorLtOne : factor < 1)
    (herrorNonneg : 0 ≤ error) :
    ∀ steps,
      accumulatedApproximationError factor error steps ≤
        error / (1 - factor) := by
  intro steps
  have hdenominator : 0 < 1 - factor := by linarith
  induction steps with
  | zero =>
      simp only [accumulatedApproximationError]
      exact div_nonneg herrorNonneg (le_of_lt hdenominator)
  | succ steps inductionHypothesis =>
      rw [accumulatedApproximationError]
      calc
        error + factor * accumulatedApproximationError factor error steps ≤
            error + factor * (error / (1 - factor)) := by
          have hscaled := mul_le_mul_of_nonneg_left inductionHypothesis
            hfactorNonneg
          linarith
        _ = error / (1 - factor) := by
          field_simp [ne_of_gt hdenominator]
          ring

/-- Finite approximate inference converges to a certified neighborhood of the
exact fixed point. -/
theorem inexact_iterate_to_errorFloor_le
    {exact approximate : State → State}
    (exactCertificate : ContractionCertificate exact)
    (approximation : InexactMapCertificate exact approximate)
    (target initial : State)
    (htarget : IsFixedPoint exact target)
    (steps : ℕ) :
    ‖approximate^[steps] initial - target‖ ≤
      exactCertificate.factor ^ steps * ‖initial - target‖ +
        approximation.error / (1 - exactCertificate.factor) := by
  have hfinite := inexact_iterate_to_fixedPoint_le exactCertificate
    approximation target initial htarget steps
  have hfloor := accumulatedApproximationError_le_floor
    exactCertificate.factor_nonneg exactCertificate.factor_lt_one
    approximation.error_nonneg steps
  exact hfinite.trans (by linarith)

/-! ## Inexact residual and perturbed fixed points -/

/-- The observable inexact residual plus one approximation budget controls
distance to the exact fixed point. -/
theorem fixedPoint_distance_le_inexactResidual_div
    {exact approximate : State → State}
    (exactCertificate : ContractionCertificate exact)
    (approximation : InexactMapCertificate exact approximate)
    (target state : State)
    (htarget : IsFixedPoint exact target) :
    ‖state - target‖ ≤
      (‖state - approximate state‖ + approximation.error) /
        (1 - exactCertificate.factor) := by
  have hdenominator : 0 < 1 - exactCertificate.factor := by
    linarith [exactCertificate.factor_lt_one]
  have hexactResidual :
      ‖state - exact state‖ ≤
        ‖state - approximate state‖ + approximation.error := by
    calc
      ‖state - exact state‖ ≤
          ‖state - approximate state‖ +
            ‖approximate state - exact state‖ := by
        have htriangle := norm_add_le
          (state - approximate state) (approximate state - exact state)
        simpa only [sub_add_sub_cancel] using htriangle
      _ ≤ ‖state - approximate state‖ + approximation.error := by
        gcongr
        exact approximation.approximates state
  calc
    ‖state - target‖ ≤
        ‖state - exact state‖ / (1 - exactCertificate.factor) :=
      fixedPoint_distance_le_residual_div exactCertificate target state htarget
    _ ≤ (‖state - approximate state‖ + approximation.error) /
          (1 - exactCertificate.factor) :=
      (div_le_div_iff_of_pos_right hdenominator).2 hexactResidual

/-- Sound adaptive stopping for an approximate solver. -/
theorem inexactResidual_adaptiveStop
    {exact approximate : State → State}
    (exactCertificate : ContractionCertificate exact)
    (approximation : InexactMapCertificate exact approximate)
    (target state : State)
    (htarget : IsFixedPoint exact target)
    (tolerance : ℝ)
    (hresidual :
      ‖state - approximate state‖ + approximation.error <
        (1 - exactCertificate.factor) * tolerance) :
    ‖state - target‖ < tolerance := by
  have hdenominator : 0 < 1 - exactCertificate.factor := by
    linarith [exactCertificate.factor_lt_one]
  have hbound := fixedPoint_distance_le_inexactResidual_div
    exactCertificate approximation target state htarget
  have hstrict :
      (‖state - approximate state‖ + approximation.error) /
          (1 - exactCertificate.factor) < tolerance :=
    (div_lt_iff₀ hdenominator).2 (by simpa [mul_comm] using hresidual)
  exact hbound.trans_lt hstrict

/-- Any fixed point of the approximate map lies inside the geometric error
floor around the exact fixed point. -/
theorem approximateFixedPoint_distance_le_errorFloor
    {exact approximate : State → State}
    (exactCertificate : ContractionCertificate exact)
    (approximation : InexactMapCertificate exact approximate)
    (exactTarget approximateTarget : State)
    (hexact : IsFixedPoint exact exactTarget)
    (happroximate : IsFixedPoint approximate approximateTarget) :
    ‖approximateTarget - exactTarget‖ ≤
      approximation.error / (1 - exactCertificate.factor) := by
  have hstep := inexact_oneStep_to_fixedPoint_le exactCertificate
    approximation exactTarget approximateTarget hexact
  rw [happroximate] at hstep
  have hdenominator : 0 < 1 - exactCertificate.factor := by
    linarith [exactCertificate.factor_lt_one]
  apply (le_div_iff₀ hdenominator).2
  nlinarith

/-! ## An attained biased-solver fixture -/

def biasedHalfSolver (state : ℝ) : ℝ := state / 2 + 1 / 10

def biasedHalfApproximation :
    InexactMapCertificate halfSolver biasedHalfSolver where
  error := 1 / 10
  error_nonneg := by norm_num
  approximates := by
    intro state
    have heq : biasedHalfSolver state - halfSolver state = (1 / 10 : ℝ) := by
      simp [biasedHalfSolver, halfSolver]
    rw [heq]
    norm_num [Real.norm_eq_abs]

theorem biasedHalfSolver_oneFifth_fixed :
    IsFixedPoint biasedHalfSolver (1 / 5) := by
  norm_num [IsFixedPoint, biasedHalfSolver]

theorem biasedHalfSolver_zero_not_fixed :
    ¬ IsFixedPoint biasedHalfSolver 0 := by
  norm_num [IsFixedPoint, biasedHalfSolver]

/-- The generic fixed-point perturbation bound is sharp on the biased solver. -/
theorem biasedHalfSolver_errorFloor_attained :
    ‖(1 / 5 : ℝ) - 0‖ =
      biasedHalfApproximation.error /
        (1 - halfSolverCertificate.factor) := by
  norm_num [biasedHalfApproximation, halfSolverCertificate, Real.norm_eq_abs]

/-- Uniformly small per-step error does not preserve the exact fixed point. -/
theorem uniformApproximation_does_not_preserve_exact_fixedPoint :
    UniformApproximation halfSolver biasedHalfSolver (1 / 10) ∧
      IsFixedPoint halfSolver 0 ∧
      ¬ IsFixedPoint biasedHalfSolver 0 :=
  ⟨biasedHalfApproximation.approximates,
    halfSolver_zero_fixed,
    biasedHalfSolver_zero_not_fixed⟩

#print axioms uniformApproximation_forwardBackward_of_resolvent
#print axioms inexact_oneStep_to_fixedPoint_le
#print axioms inexact_iterate_to_fixedPoint_le
#print axioms accumulatedApproximationError_le_floor
#print axioms inexact_iterate_to_errorFloor_le
#print axioms fixedPoint_distance_le_inexactResidual_div
#print axioms inexactResidual_adaptiveStop
#print axioms approximateFixedPoint_distance_le_errorFloor
#print axioms biasedHalfSolver_errorFloor_attained
#print axioms uniformApproximation_does_not_preserve_exact_fixedPoint

end

end InexactForwardBackward

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
