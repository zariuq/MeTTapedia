import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Depth-one Anderson gain and its nonlinear rate boundary

The depth-one Anderson subproblem removes from the current fixed-point
residual its least-squares component along the most recent residual
difference.  In a real Hilbert space this is an orthogonal projection.  We
prove its exact norm identity, global least-squares optimality, and the sharp
condition for a strict gain.

The source first-order rate is the ordinary damped fixed-point factor
multiplied by this gain.  A nonlinear Taylor remainder can erase that
improvement.  We therefore isolate the exact break-even budget and the local
radius obtained from a quadratic remainder bound.  This is the condition a
runtime acceleration trace must discharge; gain below one alone is not a
rate certificate.

For a scalar affine fixed-point map, depth-one Anderson is the secant method
on the residual.  With two distinct states and a nonidentity affine map, the
next Anderson state is exactly the fixed point.  Repeated history gives a
matching negative boundary.

Source correspondence: Evans, Pollock, Rebholz, and Xiao, *A proof that
Anderson acceleration improves the convergence rate in linearly converging
fixed point methods (but not in those converging quadratically)*,
arXiv:1810.08455, Algorithm 2.1, equations (2.6), (3.27)--(3.28),
Theorem 4.1, and Section 5.1.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace AndersonGainGeometry

open scoped InnerProductSpace

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-! ## Exact Hilbert-space gain geometry -/

/-- Least-squares coefficient for removing the component of `residual` along
the latest residual-history direction.  Division by zero is total in Lean;
the strict projection theorems expose the required nonzero premise. -/
def depthOneCoefficient (residual history : State) : ℝ :=
  ⟪history, residual⟫_ℝ / ‖history‖ ^ 2

/-- Residual returned by the depth-one Anderson least-squares subproblem. -/
def depthOneOptimizedResidual (residual history : State) : State :=
  residual - depthOneCoefficient residual history • history

@[simp] theorem depthOneCoefficient_zero_history (residual : State) :
    depthOneCoefficient residual 0 = 0 := by
  simp [depthOneCoefficient]

@[simp] theorem depthOneOptimizedResidual_zero_history (residual : State) :
    depthOneOptimizedResidual residual 0 = residual := by
  simp [depthOneOptimizedResidual]

theorem history_ne_zero_of_inner_ne_zero
    {residual history : State}
    (inner_ne_zero : ⟪history, residual⟫_ℝ ≠ 0) :
    history ≠ 0 := by
  intro historyZero
  subst history
  simp at inner_ne_zero

theorem residual_ne_zero_of_inner_ne_zero
    {residual history : State}
    (inner_ne_zero : ⟪history, residual⟫_ℝ ≠ 0) :
    residual ≠ 0 := by
  intro residualZero
  subst residual
  simp at inner_ne_zero

/-- The optimized residual is orthogonal to the history direction. -/
theorem inner_history_optimizedResidual_eq_zero
    (residual history : State) (history_ne_zero : history ≠ 0) :
    ⟪history, depthOneOptimizedResidual residual history⟫_ℝ = 0 := by
  have historyNormSq_ne_zero : ‖history‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr history_ne_zero)
  rw [depthOneOptimizedResidual, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    depthOneCoefficient]
  exact sub_eq_zero.mpr
    (div_mul_cancel₀ _ historyNormSq_ne_zero).symm

/-- Pythagorean least-squares optimality against every scalar coefficient. -/
theorem depthOneOptimizedResidual_minimizes
    (residual history : State) (history_ne_zero : history ≠ 0)
    (candidateCoefficient : ℝ) :
    ‖depthOneOptimizedResidual residual history‖ ^ 2 ≤
      ‖residual - candidateCoefficient • history‖ ^ 2 := by
  have decomposition :
      residual - candidateCoefficient • history =
        depthOneOptimizedResidual residual history +
          (depthOneCoefficient residual history -
            candidateCoefficient) • history := by
    simp [depthOneOptimizedResidual]
    module
  have optimizedOrthogonal :
      ⟪depthOneOptimizedResidual residual history, history⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact inner_history_optimizedResidual_eq_zero
      residual history history_ne_zero
  rw [decomposition, norm_add_sq_real, real_inner_smul_right,
    optimizedOrthogonal, mul_zero]
  nlinarith
    [sq_nonneg
      ‖(depthOneCoefficient residual history -
        candidateCoefficient) • history‖]

/-- Exact direction-sine identity from the source's equation (3.28). -/
theorem depthOneOptimizedResidual_norm_sq
    (residual history : State) (history_ne_zero : history ≠ 0) :
    ‖depthOneOptimizedResidual residual history‖ ^ 2 =
      ‖residual‖ ^ 2 -
        ⟪history, residual⟫_ℝ ^ 2 / ‖history‖ ^ 2 := by
  have historyNormSq_ne_zero : ‖history‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr history_ne_zero)
  rw [depthOneOptimizedResidual, norm_sub_sq_real,
    real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, depthOneCoefficient]
  rw [real_inner_comm residual history]
  field_simp
  ring

/-- Least-squares optimization never increases residual norm. -/
theorem depthOneOptimizedResidual_norm_le
    (residual history : State) :
    ‖depthOneOptimizedResidual residual history‖ ≤ ‖residual‖ := by
  by_cases historyZero : history = 0
  · subst history
    simp
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [depthOneOptimizedResidual_norm_sq
      residual history historyZero]
    exact sub_le_self _
      (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The gain is strict exactly when the history direction sees a nonzero
component of the current residual. -/
theorem depthOneOptimizedResidual_norm_lt
    (residual history : State)
    (history_ne_zero : history ≠ 0)
    (inner_ne_zero : ⟪history, residual⟫_ℝ ≠ 0) :
    ‖depthOneOptimizedResidual residual history‖ < ‖residual‖ := by
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [depthOneOptimizedResidual_norm_sq
    residual history history_ne_zero]
  have historyNormSq_pos : 0 < ‖history‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr history_ne_zero)
  have innerSq_pos : 0 < ⟪history, residual⟫_ℝ ^ 2 :=
    sq_pos_of_ne_zero inner_ne_zero
  have quotient_pos :
      0 < ⟪history, residual⟫_ℝ ^ 2 / ‖history‖ ^ 2 :=
    div_pos innerSq_pos historyNormSq_pos
  linarith

/-- Ratio form of the depth-one optimization gain. -/
def depthOneGain (residual history : State) : ℝ :=
  ‖depthOneOptimizedResidual residual history‖ / ‖residual‖

theorem depthOneGain_nonneg (residual history : State) :
    0 ≤ depthOneGain residual history :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

theorem depthOneGain_le_one (residual history : State) :
    depthOneGain residual history ≤ 1 := by
  by_cases residualZero : residual = 0
  · subst residual
    have optimizedNormZero :
        ‖depthOneOptimizedResidual (0 : State) history‖ = 0 :=
      le_antisymm
        (by
          simpa using
            depthOneOptimizedResidual_norm_le
              (0 : State) history)
        (norm_nonneg _)
    simp [depthOneGain, optimizedNormZero]
  · exact
      (div_le_one (norm_pos_iff.mpr residualZero)).2
        (depthOneOptimizedResidual_norm_le residual history)

theorem depthOneGain_lt_one
    (residual history : State)
    (residual_ne_zero : residual ≠ 0)
    (history_ne_zero : history ≠ 0)
    (inner_ne_zero : ⟪history, residual⟫_ℝ ≠ 0) :
    depthOneGain residual history < 1 :=
  (div_lt_one (norm_pos_iff.mpr residual_ne_zero)).2
    (depthOneOptimizedResidual_norm_lt residual history
      history_ne_zero inner_ne_zero)

theorem depthOneGain_lt_one_iff
    (residual history : State)
    (residual_ne_zero : residual ≠ 0)
    (history_ne_zero : history ≠ 0) :
    depthOneGain residual history < 1 ↔
      ⟪history, residual⟫_ℝ ≠ 0 := by
  constructor
  · intro gain_lt_one innerZero
    have optimized_eq :
        depthOneOptimizedResidual residual history = residual := by
      simp [depthOneOptimizedResidual, depthOneCoefficient, innerZero]
    rw [depthOneGain, optimized_eq,
      div_self (norm_ne_zero_iff.mpr residual_ne_zero)] at gain_lt_one
    exact lt_irrefl 1 gain_lt_one
  · exact depthOneGain_lt_one residual history
      residual_ne_zero history_ne_zero

/-- Squared gain is one minus the squared direction cosine. -/
theorem depthOneGain_sq
    (residual history : State)
    (residual_ne_zero : residual ≠ 0)
    (history_ne_zero : history ≠ 0) :
    depthOneGain residual history ^ 2 =
      1 -
        ⟪history, residual⟫_ℝ ^ 2 /
          (‖history‖ ^ 2 * ‖residual‖ ^ 2) := by
  have residualNormSq_ne_zero : ‖residual‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr residual_ne_zero)
  have historyNormSq_ne_zero : ‖history‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr history_ne_zero)
  rw [depthOneGain, div_pow,
    depthOneOptimizedResidual_norm_sq
      residual history history_ne_zero]
  field_simp

/-! ## First-order gain versus nonlinear remainder -/

/-- Damped baseline factor `(1-beta) + beta*kappa`. -/
def dampedBaselineFactor (contraction damping : ℝ) : ℝ :=
  (1 - damping) + damping * contraction

/-- First-order Anderson factor from Theorem 4.1. -/
def acceleratedFirstOrderFactor
    (gain contraction damping : ℝ) : ℝ :=
  gain * dampedBaselineFactor contraction damping

theorem dampedBaselineFactor_nonneg
    {contraction damping : ℝ}
    (contraction_nonneg : 0 ≤ contraction)
    (damping_nonneg : 0 ≤ damping)
    (damping_le_one : damping ≤ 1) :
    0 ≤ dampedBaselineFactor contraction damping := by
  unfold dampedBaselineFactor
  positivity

theorem dampedBaselineFactor_lt_one
    {contraction damping : ℝ}
    (contraction_lt_one : contraction < 1)
    (damping_pos : 0 < damping) :
    dampedBaselineFactor contraction damping < 1 := by
  unfold dampedBaselineFactor
  nlinarith
    [mul_pos damping_pos (sub_pos.mpr contraction_lt_one)]

/-- Damping interpolates between the contractive factor and one. -/
theorem contraction_le_dampedBaselineFactor
    {contraction damping : ℝ}
    (contraction_le_one : contraction ≤ 1)
    (damping_le_one : damping ≤ 1) :
    contraction ≤ dampedBaselineFactor contraction damping := by
  unfold dampedBaselineFactor
  nlinarith
    [mul_nonneg
      (sub_nonneg.mpr damping_le_one)
      (sub_nonneg.mpr contraction_le_one)]

theorem dampedBaselineFactor_le_one
    {contraction damping : ℝ}
    (contraction_le_one : contraction ≤ 1)
    (damping_nonneg : 0 ≤ damping) :
    dampedBaselineFactor contraction damping ≤ 1 := by
  unfold dampedBaselineFactor
  nlinarith
    [mul_nonneg damping_nonneg
      (sub_nonneg.mpr contraction_le_one)]

theorem acceleratedFirstOrderFactor_le_baseline
    {gain contraction damping : ℝ}
    (gain_le_one : gain ≤ 1)
    (baseline_nonneg :
      0 ≤ dampedBaselineFactor contraction damping) :
    acceleratedFirstOrderFactor gain contraction damping ≤
      dampedBaselineFactor contraction damping := by
  unfold acceleratedFirstOrderFactor
  nlinarith
    [mul_nonneg baseline_nonneg (sub_nonneg.mpr gain_le_one)]

theorem acceleratedFirstOrderFactor_lt_baseline
    {gain contraction damping : ℝ}
    (gain_lt_one : gain < 1)
    (baseline_pos :
      0 < dampedBaselineFactor contraction damping) :
    acceleratedFirstOrderFactor gain contraction damping <
      dampedBaselineFactor contraction damping := by
  unfold acceleratedFirstOrderFactor
  nlinarith
    [mul_pos baseline_pos (sub_pos.mpr gain_lt_one)]

/-- First-order term plus the nonnegative nonlinear remainder. -/
def residualRateEnvelope
    (gain contraction damping currentResidual remainder : ℝ) : ℝ :=
  acceleratedFirstOrderFactor gain contraction damping *
      currentResidual +
    remainder

/-- Exact budget that the nonlinear remainder must stay below for the
Anderson envelope to beat the damped baseline envelope. -/
def nonlinearImprovementBudget
    (gain contraction damping currentResidual : ℝ) : ℝ :=
  (1 - gain) * dampedBaselineFactor contraction damping *
    currentResidual

theorem residualRateEnvelope_lt_baseline_iff
    (gain contraction damping currentResidual remainder : ℝ) :
    residualRateEnvelope gain contraction damping
        currentResidual remainder <
      dampedBaselineFactor contraction damping * currentResidual ↔
    remainder <
      nonlinearImprovementBudget gain contraction damping
        currentResidual := by
  unfold residualRateEnvelope nonlinearImprovementBudget
    acceleratedFirstOrderFactor dampedBaselineFactor
  constructor <;> intro comparison <;> nlinarith

theorem residual_lt_baseline_of_rateEnvelope
    {gain contraction damping currentResidual remainder nextResidual : ℝ}
    (next_le_envelope :
      nextResidual ≤
        residualRateEnvelope gain contraction damping
          currentResidual remainder)
    (remainder_lt_budget :
      remainder <
        nonlinearImprovementBudget gain contraction damping
          currentResidual) :
    nextResidual <
      dampedBaselineFactor contraction damping * currentResidual := by
  exact lt_of_le_of_lt next_le_envelope
    ((residualRateEnvelope_lt_baseline_iff gain contraction damping
      currentResidual remainder).2 remainder_lt_budget)

/-- Local radius licensed by a quadratic Taylor-remainder coefficient. -/
def quadraticImprovementRadius
    (gain contraction damping curvature : ℝ) : ℝ :=
  (1 - gain) * dampedBaselineFactor contraction damping / curvature

theorem quadraticRemainder_lt_budget
    {gain contraction damping currentResidual curvature : ℝ}
    (curvature_pos : 0 < curvature)
    (currentResidual_pos : 0 < currentResidual)
    (inside_radius :
      currentResidual <
        quadraticImprovementRadius gain contraction damping curvature) :
    curvature * currentResidual ^ 2 <
      nonlinearImprovementBudget gain contraction damping
        currentResidual := by
  have scaledRadius :=
    (lt_div_iff₀ curvature_pos).mp inside_radius
  unfold nonlinearImprovementBudget
  nlinarith

theorem residual_lt_baseline_of_quadratic_remainder
    {gain contraction damping currentResidual curvature
      remainder nextResidual : ℝ}
    (curvature_pos : 0 < curvature)
    (currentResidual_pos : 0 < currentResidual)
    (inside_radius :
      currentResidual <
        quadraticImprovementRadius gain contraction damping curvature)
    (remainder_le :
      remainder ≤ curvature * currentResidual ^ 2)
    (next_le_envelope :
      nextResidual ≤
        residualRateEnvelope gain contraction damping
          currentResidual remainder) :
    nextResidual <
      dampedBaselineFactor contraction damping * currentResidual := by
  apply residual_lt_baseline_of_rateEnvelope next_le_envelope
  exact lt_of_le_of_lt remainder_le
    (quadraticRemainder_lt_budget curvature_pos currentResidual_pos
      inside_radius)

/-- Sharp boundary: if the remainder spends the entire improvement budget,
the rate envelope is exactly the baseline, not strictly better. -/
theorem fullImprovementBudget_recovers_baseline
    (gain contraction damping currentResidual : ℝ) :
    residualRateEnvelope gain contraction damping currentResidual
        (nonlinearImprovementBudget gain contraction damping
          currentResidual) =
      dampedBaselineFactor contraction damping * currentResidual := by
  unfold residualRateEnvelope nonlinearImprovementBudget
    acceleratedFirstOrderFactor
  ring

/-! ## Scalar affine Anderson is exact -/

/-- Fixed-point residual `g(x) - x`. -/
def scalarResidual (map : ℝ → ℝ) (state : ℝ) : ℝ :=
  map state - state

/-- Depth-one scalar coefficient. -/
def scalarDepthOneCoefficient
    (map : ℝ → ℝ) (previous current : ℝ) : ℝ :=
  scalarResidual map current /
    (scalarResidual map current - scalarResidual map previous)

/-- Undamped scalar depth-one Anderson state, equivalently the secant update
for the residual. -/
def scalarAndersonState
    (map : ℝ → ℝ) (previous current : ℝ) : ℝ :=
  current -
    scalarDepthOneCoefficient map previous current *
      (current - previous)

theorem scalar_optimizedResidual_eq_zero
    (map : ℝ → ℝ) (previous current : ℝ)
    (residualDifference_ne_zero :
      scalarResidual map current - scalarResidual map previous ≠ 0) :
    scalarResidual map current -
        scalarDepthOneCoefficient map previous current *
          (scalarResidual map current - scalarResidual map previous) =
      0 := by
  unfold scalarDepthOneCoefficient
  exact sub_eq_zero.mpr
    (div_mul_cancel₀ _ residualDifference_ne_zero).symm

/-- Scalar affine map with declared fixed point. -/
def scalarAffineFixedPointMap
    (contraction target state : ℝ) : ℝ :=
  target + contraction * (state - target)

@[simp] theorem scalarAffineFixedPointMap_target
    (contraction target : ℝ) :
    scalarAffineFixedPointMap contraction target target = target := by
  simp [scalarAffineFixedPointMap]

@[simp] theorem scalarAffineResidual
    (contraction target state : ℝ) :
    scalarResidual
        (scalarAffineFixedPointMap contraction target) state =
      (contraction - 1) * (state - target) := by
  simp [scalarResidual, scalarAffineFixedPointMap]
  ring

/-- A nonidentity scalar affine map is solved exactly from two distinct
states by one depth-one Anderson/secant update. -/
theorem scalarAffine_depthOneAnderson_eq_target
    (contraction target previous current : ℝ)
    (contraction_ne_one : contraction ≠ 1)
    (states_ne : current ≠ previous) :
    scalarAndersonState
        (scalarAffineFixedPointMap contraction target)
        previous current =
      target := by
  have denominator_ne_zero :
      (contraction - 1) * (current - previous) ≠ 0 :=
    mul_ne_zero
      (sub_ne_zero.mpr contraction_ne_one)
      (sub_ne_zero.mpr states_ne)
  simp only [scalarAndersonState, scalarDepthOneCoefficient,
    scalarAffineResidual]
  have residualDifference :
      (contraction - 1) * (current - target) -
          (contraction - 1) * (previous - target) =
        (contraction - 1) * (current - previous) := by
    ring
  rw [residualDifference]
  field_simp
  ring

theorem halfAffine_fixture_baseline_not_solved :
    scalarAffineFixedPointMap (1 / 2) 3 1 = 2 := by
  norm_num [scalarAffineFixedPointMap]

theorem halfAffine_fixture_anderson_solved :
    scalarAndersonState
        (scalarAffineFixedPointMap (1 / 2) 3) 0 1 =
      3 := by
  norm_num [scalarAndersonState, scalarDepthOneCoefficient,
    scalarResidual, scalarAffineFixedPointMap]

/-- Repeated history has zero residual difference, so totalized division
falls back to coefficient zero and need not reach the fixed point. -/
theorem repeatedHistory_does_not_accelerate :
    scalarAndersonState
        (scalarAffineFixedPointMap (1 / 2) 3) 1 1 =
      1 := by
  norm_num [scalarAndersonState, scalarDepthOneCoefficient,
    scalarResidual, scalarAffineFixedPointMap]

/-- A gain of one half does not by itself improve the rate: a remainder
equal to the saved first-order budget restores the baseline exactly. -/
theorem halfGain_fullRemainder_not_faster :
    residualRateEnvelope (1 / 2) (1 / 2) 1 1 (1 / 4) =
      dampedBaselineFactor (1 / 2) 1 * 1 := by
  norm_num [residualRateEnvelope, acceleratedFirstOrderFactor,
    dampedBaselineFactor]

#print axioms inner_history_optimizedResidual_eq_zero
#print axioms depthOneOptimizedResidual_minimizes
#print axioms depthOneOptimizedResidual_norm_sq
#print axioms depthOneGain_sq
#print axioms residualRateEnvelope_lt_baseline_iff
#print axioms residual_lt_baseline_of_quadratic_remainder
#print axioms fullImprovementBudget_recovers_baseline
#print axioms scalarAffine_depthOneAnderson_eq_target
#print axioms halfAffine_fixture_anderson_solved
#print axioms repeatedHistory_does_not_accelerate
#print axioms halfGain_fullRemainder_not_faster

end

end AndersonGainGeometry

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
