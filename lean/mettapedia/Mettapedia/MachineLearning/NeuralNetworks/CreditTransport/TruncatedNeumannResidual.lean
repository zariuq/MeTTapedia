import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Certified truncated Neumann corrections

Fung, Heaton, Li, McKenzie, Osher, and Yin (2021), *JFB: Jacobian-free
backpropagation for implicit networks*, identify Jacobian-free
backpropagation with the zeroth-order truncation of the Neumann expansion of
an implicit inverse.  This file isolates the reusable algebraic and analytic
content of that observation.

For a continuous linear map `A`, the `n`-term approximation

`Sₙ x = (I + A + ... + Aⁿ⁻¹) x`

has exact linear-system residual `Aⁿ x`.  If `A` contracts by `q`, that
residual is bounded by `qⁿ ‖x‖`.  If `y - A y = x`, the approximation error is
exactly `Aⁿ y`, so the same geometric certificate feeds the existing
finite-step task-descent theorem.

The results here do not silently assume that an arbitrary implicit model
satisfies the paper's full-rank or conditioning hypotheses.  Those hypotheses
must be discharged by a concrete model before the final descent theorem can
be applied.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace TruncatedNeumannResidual

noncomputable section

open Filter
open scoped InnerProductSpace

variable {State : Type*} [NormedAddCommGroup State]

section Linear

variable [NormedSpace ℝ State]

/-- The first `terms` powers of a linearized fixed-point map. -/
def partialSum (operator : State →L[ℝ] State) (terms : ℕ) :
    State →L[ℝ] State :=
  ∑ power ∈ Finset.range terms, operator ^ power

/-- Apply the truncated Neumann inverse to a right-hand side. -/
def approximation (operator : State →L[ℝ] State)
    (terms : ℕ) (rightHandSide : State) : State :=
  partialSum operator terms rightHandSide

/-- Residual of the truncated solve for `(I - A) y = x`. -/
def residual (operator : State →L[ℝ] State)
    (terms : ℕ) (rightHandSide : State) : State :=
  rightHandSide -
    (approximation operator terms rightHandSide -
      operator (approximation operator terms rightHandSide))

/-- A pointwise contraction bound.  This form is directly dischargeable by a
replay certificate and does not require a separately computed operator norm. -/
def ContractsBy (operator : State →L[ℝ] State) (factor : ℝ) : Prop :=
  ∀ state, ‖operator state‖ ≤ factor * ‖state‖

/-- Left multiplication by `I - A` leaves exactly the omitted power. -/
theorem one_sub_mul_partialSum
    (operator : State →L[ℝ] State) (terms : ℕ) :
    (1 - operator) * partialSum operator terms =
      1 - operator ^ terms := by
  simpa [partialSum] using mul_neg_geom_sum operator terms

/-- Right multiplication gives the same residual because the partial sum is a
polynomial in the operator. -/
theorem partialSum_mul_one_sub
    (operator : State →L[ℝ] State) (terms : ℕ) :
    partialSum operator terms * (1 - operator) =
      1 - operator ^ terms := by
  simpa [partialSum] using geom_sum_mul_neg operator terms

/-- The solve residual is not merely bounded: it is exactly the first omitted
power applied to the right-hand side. -/
theorem residual_eq_power_apply
    (operator : State →L[ℝ] State) (terms : ℕ)
    (rightHandSide : State) :
    residual operator terms rightHandSide =
      (operator ^ terms) rightHandSide := by
  have hoperator := congrArg
    (fun map : State →L[ℝ] State => map rightHandSide)
    (one_sub_mul_partialSum operator terms)
  simpa [residual, approximation, sub_eq_add_neg] using
    congrArg (fun value : State => rightHandSide - value) hoperator

/-- A pointwise contraction certificate composes through every finite power. -/
theorem pow_apply_norm_le
    {operator : State →L[ℝ] State} {factor : ℝ}
    (hcontract : ContractsBy operator factor) (hfactor : 0 ≤ factor)
    (terms : ℕ) (state : State) :
    ‖(operator ^ terms) state‖ ≤ factor ^ terms * ‖state‖ := by
  induction terms with
  | zero =>
      simp
  | succ terms inductionHypothesis =>
      rw [pow_succ']
      change ‖operator ((operator ^ terms) state)‖ ≤
        factor ^ (terms + 1) * ‖state‖
      calc
        ‖operator ((operator ^ terms) state)‖ ≤
            factor * ‖(operator ^ terms) state‖ :=
          hcontract _
        _ ≤ factor * (factor ^ terms * ‖state‖) :=
          mul_le_mul_of_nonneg_left inductionHypothesis hfactor
        _ = factor ^ (terms + 1) * ‖state‖ := by
          rw [pow_succ']
          ring

/-- Geometric residual certificate for a finite truncated solve. -/
theorem residual_norm_le
    {operator : State →L[ℝ] State} {factor : ℝ}
    (hcontract : ContractsBy operator factor) (hfactor : 0 ≤ factor)
    (terms : ℕ) (rightHandSide : State) :
    ‖residual operator terms rightHandSide‖ ≤
      factor ^ terms * ‖rightHandSide‖ := by
  rw [residual_eq_power_apply]
  exact pow_apply_norm_le hcontract hfactor terms rightHandSide

/-- A declared finite depth is sufficient whenever its geometric budget fits
the requested residual tolerance. -/
theorem residual_norm_le_of_geometric_budget
    {operator : State →L[ℝ] State} {factor tolerance : ℝ}
    (hcontract : ContractsBy operator factor) (hfactor : 0 ≤ factor)
    (terms : ℕ) (rightHandSide : State)
    (hbudget : factor ^ terms * ‖rightHandSide‖ ≤ tolerance) :
    ‖residual operator terms rightHandSide‖ ≤ tolerance :=
  (residual_norm_le hcontract hfactor terms rightHandSide).trans hbudget

/-- For an exact solution of `(I - A) y = x`, the truncation error is exactly
the omitted power applied to the solution. -/
theorem exactSolution_sub_approximation_eq_power_apply
    (operator : State →L[ℝ] State) (terms : ℕ)
    (rightHandSide exactSolution : State)
    (hsolution :
      exactSolution - operator exactSolution = rightHandSide) :
    exactSolution - approximation operator terms rightHandSide =
      (operator ^ terms) exactSolution := by
  have hoperator := congrArg
    (fun map : State →L[ℝ] State => map exactSolution)
    (partialSum_mul_one_sub operator terms)
  rw [← hsolution]
  simpa [approximation, sub_eq_add_neg] using
    congrArg (fun value : State => exactSolution - value) hoperator

/-- Quantitative error of the finite inverse approximation. -/
theorem approximation_sub_exactSolution_norm_le
    {operator : State →L[ℝ] State} {factor : ℝ}
    (hcontract : ContractsBy operator factor) (hfactor : 0 ≤ factor)
    (terms : ℕ) (rightHandSide exactSolution : State)
    (hsolution :
      exactSolution - operator exactSolution = rightHandSide) :
    ‖approximation operator terms rightHandSide - exactSolution‖ ≤
      factor ^ terms * ‖exactSolution‖ := by
  rw [norm_sub_rev]
  rw [exactSolution_sub_approximation_eq_power_apply
    operator terms rightHandSide exactSolution hsolution]
  exact pow_apply_norm_le hcontract hfactor terms exactSolution

/-- The one-term Neumann approximation is the Jacobian-free approximation:
it returns the right-hand side without applying the implicit inverse. -/
@[simp] theorem approximation_one
    (operator : State →L[ℝ] State) (rightHandSide : State) :
    approximation operator 1 rightHandSide = rightHandSide := by
  simp [approximation, partialSum]

/-- The zero-term approximation performs no correction. -/
@[simp] theorem approximation_zero
    (operator : State →L[ℝ] State) (rightHandSide : State) :
    approximation operator 0 rightHandSide = 0 := by
  simp [approximation, partialSum]

/-- Jacobian-free approximation inherits the first-order geometric error
budget. -/
theorem jacobianFree_approximation_error_le
    {operator : State →L[ℝ] State} {factor : ℝ}
    (hcontract : ContractsBy operator factor) (hfactor : 0 ≤ factor)
    (rightHandSide exactSolution : State)
    (hsolution :
      exactSolution - operator exactSolution = rightHandSide) :
    ‖rightHandSide - exactSolution‖ ≤ factor * ‖exactSolution‖ := by
  simpa using approximation_sub_exactSolution_norm_le
    hcontract hfactor 1 rightHandSide exactSolution hsolution

/-- Under a strict contraction, the finite residuals converge to zero. -/
theorem residual_tendsto_zero
    {operator : State →L[ℝ] State} {factor : ℝ}
    (hcontract : ContractsBy operator factor)
    (hfactor : 0 ≤ factor) (hfactor_lt_one : factor < 1)
    (rightHandSide : State) :
    Tendsto (fun terms => residual operator terms rightHandSide)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
  · exact fun terms => residual_norm_le hcontract hfactor terms rightHandSide
  · simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hfactor hfactor_lt_one).mul_const
        ‖rightHandSide‖

end Linear

section TaskDescent

variable [InnerProductSpace ℝ State]

open DirectionalTaskDescent

/-- A certified Neumann truncation feeds the generic finite-step descent
theorem.  This states the exact assumptions needed to turn an implicit inverse
approximation into task descent; contraction alone is not enough. -/
theorem smoothTask_strict_descent_of_neumannApproximation
    {operator : State →L[ℝ] State} {factor beta step : ℝ}
    {loss : State → ℝ} {parameter rightHandSide exactGradient : State}
    {terms : ℕ}
    (hcontract : ContractsBy operator factor) (hfactor : 0 ≤ factor)
    (hsolution :
      exactGradient - operator exactGradient = rightHandSide)
    (certificate :
      HasSmoothTaskUpperModelAt loss parameter exactGradient beta)
    (hbeta : 0 ≤ beta) (hstep : 0 < step)
    (hrelative : factor ^ terms * ‖exactGradient‖ < ‖exactGradient‖)
    (htrust :
      beta * step *
          (‖exactGradient‖ + factor ^ terms * ‖exactGradient‖) ^ 2 / 2 <
        ‖exactGradient‖ *
          (‖exactGradient‖ - factor ^ terms * ‖exactGradient‖)) :
    loss (parameter -
        step • approximation operator terms rightHandSide) <
      loss parameter := by
  apply smoothTask_strict_descent_of_norm_error certificate
    (approximation_sub_exactSolution_norm_le
      hcontract hfactor terms rightHandSide exactGradient hsolution)
    hbeta hstep hrelative htrust

end TaskDescent

/-! ## Positive and negative fixtures -/

noncomputable def halfOperator : ℝ →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

theorem halfOperator_contracts :
    ContractsBy halfOperator (1 / 2) := by
  intro state
  simp [halfOperator, Real.norm_eq_abs]

theorem halfOperator_three_term_residual :
    residual halfOperator 3 (8 : ℝ) = 1 := by
  rw [residual_eq_power_apply]
  norm_num [halfOperator, pow_succ]

/-- At the boundary factor `1`, truncation need not improve the residual at
all. -/
theorem identity_residual
    (terms : ℕ) (rightHandSide : ℝ) :
    residual (ContinuousLinearMap.id ℝ ℝ) terms rightHandSide =
      rightHandSide := by
  rw [residual_eq_power_apply]
  simp

/-- The identity map cannot satisfy a strict contraction certificate. -/
theorem identity_not_contractsBy_lt_one
    {factor : ℝ} (hfactor_lt_one : factor < 1) :
    ¬ ContractsBy (ContinuousLinearMap.id ℝ ℝ) factor := by
  intro hcontract
  have hunit := hcontract (1 : ℝ)
  norm_num at hunit
  linarith

#print axioms one_sub_mul_partialSum
#print axioms residual_eq_power_apply
#print axioms residual_norm_le
#print axioms approximation_sub_exactSolution_norm_le
#print axioms residual_tendsto_zero
#print axioms smoothTask_strict_descent_of_neumannApproximation
#print axioms halfOperator_three_term_residual
#print axioms identity_not_contractsBy_lt_one

end

end TruncatedNeumannResidual

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
