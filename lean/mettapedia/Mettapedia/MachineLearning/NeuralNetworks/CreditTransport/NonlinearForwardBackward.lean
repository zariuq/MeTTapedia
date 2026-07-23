import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NonlinearResolvent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization

/-!
# Nonlinear forward--backward splitting

This file connects monotone implicit resolvents to the existing finite-time
contraction calculus.  The fixed points of a nonlinear forward--backward step
are exactly the zeros of the summed implicit and forward operators.  If the
explicit forward map is contractive, firm nonexpansiveness of the resolvent
preserves that contraction factor, so all initializer, iteration, and
residual-stopping theorems apply without changing the solved fixed point.

The positive fixture combines the nonlinear positive-part resolvent with a
half-step forward map.  The resulting split is globally contractive and is
strictly faster on its positive branch than the explicit forward map alone.
The negative fixture retains the same monotone implicit operator but uses an
anti-monotone forward term; it has many fixed points and admits no global
contraction certificate.  Thus implicit monotonicity alone is not enough.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace NonlinearForwardBackward

open scoped InnerProductSpace
open NonlinearResolvent
open AmortizedInitialization

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-! ## General composition theorem -/

/-- The explicit half of a forward--backward split. -/
def explicitForwardStep (forwardOperator : State → State) (state : State) : State :=
  state - forwardOperator state

/-- Apply the explicit forward step, then the implicit resolvent. -/
def nonlinearForwardBackwardStep
    (resolvent forwardOperator : State → State) (state : State) : State :=
  resolvent (explicitForwardStep forwardOperator state)

/-- Firm nonexpansiveness implies ordinary norm nonexpansiveness. -/
theorem FirmlyNonexpansiveMap.norm_sub_le
    {resolvent : State → State}
    (certificate : FirmlyNonexpansiveMap resolvent)
    (left right : State) :
    ‖resolvent left - resolvent right‖ ≤ ‖left - right‖ := by
  let outputDifference := resolvent left - resolvent right
  let inputDifference := left - right
  have hfirm :
      ⟪outputDifference, outputDifference⟫_ℝ ≤
        ⟪outputDifference, inputDifference⟫_ℝ :=
    certificate left right
  have hcauchy :
      ⟪outputDifference, inputDifference⟫_ℝ ≤
        ‖outputDifference‖ * ‖inputDifference‖ :=
    real_inner_le_norm outputDifference inputDifference
  rw [real_inner_self_eq_norm_sq] at hfirm
  have hsquare :
      ‖outputDifference‖ ^ 2 ≤
        ‖outputDifference‖ * ‖inputDifference‖ :=
    hfirm.trans hcauchy
  by_cases hzero : ‖outputDifference‖ = 0
  · rw [hzero]
    exact norm_nonneg inputDifference
  · have hpositive : 0 < ‖outputDifference‖ :=
      lt_of_le_of_ne (norm_nonneg outputDifference) (Ne.symm hzero)
    nlinarith

/-- Fixed points of a nonlinear forward--backward step are exactly the zeros
of the sum of its implicit and forward operators. -/
theorem fixed_iff_sum_zero_of_monotone_forwardBackward
    {implicitOperator resolvent forwardOperator : State → State}
    (implicitMonotone : MonotoneMap implicitOperator)
    (resolventEquation :
      IsUnitResolventMapOf implicitOperator resolvent)
    (state : State) :
    nonlinearForwardBackwardStep resolvent forwardOperator state = state ↔
      implicitOperator state + forwardOperator state = 0 := by
  constructor
  · intro hfixed
    have hequation := resolventEquation
      (explicitForwardStep forwardOperator state)
    change resolvent (explicitForwardStep forwardOperator state) = state at hfixed
    rw [hfixed] at hequation
    have hequation' :
        state + implicitOperator state = state - forwardOperator state := by
      simpa [explicitForwardStep] using hequation
    calc
      implicitOperator state + forwardOperator state =
          (state + implicitOperator state) -
            (state - forwardOperator state) := by abel
      _ = 0 := by rw [hequation']; simp
  · intro hzero
    apply monotone_shift_solution_unique implicitMonotone
      (resolventEquation (explicitForwardStep forwardOperator state))
    unfold explicitForwardStep
    calc
      state + implicitOperator state =
          (state - forwardOperator state) +
            (implicitOperator state + forwardOperator state) := by abel
      _ = state - forwardOperator state := by rw [hzero, add_zero]

/-- A firmly nonexpansive implicit resolvent cannot worsen the contraction
factor of the explicit forward map. -/
def contractionCertificate_of_firmlyNonexpansive_resolvent
    {implicitOperator resolvent forwardOperator : State → State}
    (implicitMonotone : MonotoneMap implicitOperator)
    (resolventEquation :
      IsUnitResolventMapOf implicitOperator resolvent)
    (forwardCertificate :
      ContractionCertificate (explicitForwardStep forwardOperator)) :
    ContractionCertificate
      (nonlinearForwardBackwardStep resolvent forwardOperator) where
  factor := forwardCertificate.factor
  factor_nonneg := forwardCertificate.factor_nonneg
  factor_lt_one := forwardCertificate.factor_lt_one
  contracts := by
    intro left right
    calc
      ‖nonlinearForwardBackwardStep resolvent forwardOperator left -
          nonlinearForwardBackwardStep resolvent forwardOperator right‖ ≤
          ‖explicitForwardStep forwardOperator left -
            explicitForwardStep forwardOperator right‖ :=
        FirmlyNonexpansiveMap.norm_sub_le
          (firmlyNonexpansive_of_monotone_resolvent
            implicitMonotone resolventEquation) _ _
      _ ≤ forwardCertificate.factor * ‖left - right‖ :=
        forwardCertificate.contracts left right

/-! ## Nonlinear positive fixture -/

/-- Forward operator whose explicit update is multiplication by one half. -/
def halfForwardOperator (state : ℝ) : ℝ := state / 2

theorem explicitHalfForwardStep_eq_halfSolver :
    explicitForwardStep halfForwardOperator = halfSolver := by
  funext state
  simp [explicitForwardStep, halfForwardOperator, halfSolver]
  ring

def explicitHalfForwardCertificate :
    ContractionCertificate (explicitForwardStep halfForwardOperator) where
  factor := 1 / 2
  factor_nonneg := by norm_num
  factor_lt_one := by norm_num
  contracts := by
    intro left right
    rw [show explicitForwardStep halfForwardOperator left -
        explicitForwardStep halfForwardOperator right =
          (left - right) / 2 by
      simp [explicitForwardStep, halfForwardOperator]
      ring]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    norm_num
    have heq : |left - right| / 2 =
        (1 / 2 : ℝ) * |left - right| := by ring
    exact heq.le

/-- A globally nonlinear forward--backward step. -/
def positiveHalfSplit : ℝ → ℝ :=
  nonlinearForwardBackwardStep positivePartResolvent halfForwardOperator

def positiveHalfSplitCertificate :
    ContractionCertificate positiveHalfSplit where
  factor := 1 / 2
  factor_nonneg := by norm_num
  factor_lt_one := by norm_num
  contracts := by
    intro left right
    exact (contractionCertificate_of_firmlyNonexpansive_resolvent
      positivePartOperator_monotone positivePart_resolventEquation
      explicitHalfForwardCertificate).contracts left right

theorem positiveHalfSplit_fixed_iff_sum_zero (state : ℝ) :
    positiveHalfSplit state = state ↔
      positivePartOperator state + halfForwardOperator state = 0 := by
  simpa [positiveHalfSplit] using
    fixed_iff_sum_zero_of_monotone_forwardBackward
      positivePartOperator_monotone positivePart_resolventEquation state

theorem positivePart_add_half_zero_iff (state : ℝ) :
    positivePartOperator state + halfForwardOperator state = 0 ↔
      state = 0 := by
  constructor
  · intro hzero
    by_cases hnonpositive : state ≤ 0
    · rw [positivePartOperator, max_eq_right hnonpositive] at hzero
      simp [halfForwardOperator] at hzero
      linarith
    · have hpositive : 0 < state := lt_of_not_ge hnonpositive
      rw [positivePartOperator, max_eq_left (le_of_lt hpositive)] at hzero
      simp [halfForwardOperator] at hzero
      linarith
  · rintro rfl
    norm_num [positivePartOperator, halfForwardOperator]

theorem positiveHalfSplit_fixed_iff_zero (state : ℝ) :
    positiveHalfSplit state = state ↔ state = 0 := by
  rw [positiveHalfSplit_fixed_iff_sum_zero,
    positivePart_add_half_zero_iff]

theorem positiveHalfSplit_zero_fixed :
    IsFixedPoint positiveHalfSplit 0 := by
  exact positiveHalfSplit_fixed_iff_zero 0 |>.2 rfl

/-- Exact piecewise form of the nonlinear split. -/
theorem positiveHalfSplit_apply (state : ℝ) :
    positiveHalfSplit state = if state ≤ 0 then state / 2 else state / 4 := by
  by_cases hnonpositive : state ≤ 0
  · have hhalf : state - state / 2 ≤ 0 := by linarith
    simp [positiveHalfSplit, nonlinearForwardBackwardStep,
      explicitForwardStep, halfForwardOperator, positivePartResolvent,
      hnonpositive, hhalf]
    ring
  · have hpositive : 0 < state := lt_of_not_ge hnonpositive
    have hhalf : ¬ state - state / 2 ≤ 0 := by linarith
    simp [positiveHalfSplit, nonlinearForwardBackwardStep,
      explicitForwardStep, halfForwardOperator, positivePartResolvent,
      hnonpositive, hhalf]
    ring

/-- The composed step remains genuinely nonlinear. -/
theorem positiveHalfSplit_not_midpointLinear :
    positiveHalfSplit ((-2 + 2) / 2) ≠
      (positiveHalfSplit (-2) + positiveHalfSplit 2) / 2 := by
  rw [positiveHalfSplit_apply, positiveHalfSplit_apply,
    positiveHalfSplit_apply]
  norm_num

/-- The implicit resolvent improves the positive-branch one-step factor from
one half to one quarter. -/
theorem positiveHalfSplit_positive_branch
    {state : ℝ} (hpositive : 0 < state) :
    positiveHalfSplit state = state / 4 ∧
      explicitForwardStep halfForwardOperator state = state / 2 := by
  constructor
  · rw [positiveHalfSplit_apply]
    simp [not_le.mpr hpositive]
  · simp [explicitForwardStep, halfForwardOperator]
    ring

/-- The existing amortized-initializer theorem now supplies the finite-step
settling bound for the nonlinear split. -/
theorem positiveHalfSplit_iterate_to_zero_le
    (initial : ℝ) (steps : ℕ) :
    ‖positiveHalfSplit^[steps] initial - 0‖ ≤
      (1 / 2 : ℝ) ^ steps * ‖initial - 0‖ := by
  simpa [positiveHalfSplitCertificate] using
    iterate_initializer_to_fixedPoint_le positiveHalfSplitCertificate
      0 initial positiveHalfSplit_zero_fixed steps

/-! ## Forward monotonicity is a substantive boundary -/

/-- An anti-monotone forward term. -/
def antiForwardOperator (state : ℝ) : ℝ := -state

def positiveAntiSplit : ℝ → ℝ :=
  nonlinearForwardBackwardStep positivePartResolvent antiForwardOperator

theorem positiveAntiSplit_zero_fixed :
    IsFixedPoint positiveAntiSplit 0 := by
  norm_num [IsFixedPoint, positiveAntiSplit, nonlinearForwardBackwardStep,
    explicitForwardStep, antiForwardOperator, positivePartResolvent]

theorem positiveAntiSplit_one_fixed :
    IsFixedPoint positiveAntiSplit 1 := by
  norm_num [IsFixedPoint, positiveAntiSplit, nonlinearForwardBackwardStep,
    explicitForwardStep, antiForwardOperator, positivePartResolvent]

/-- The same monotone implicit operator does not rescue an anti-monotone
forward term: the split has distinct fixed points and cannot be contractive. -/
theorem positiveAntiSplit_no_globalContractionCertificate :
    ¬ Nonempty (ContractionCertificate positiveAntiSplit) := by
  rintro ⟨certificate⟩
  have hequal := fixedPoint_unique certificate
    positiveAntiSplit_one_fixed positiveAntiSplit_zero_fixed
  norm_num at hequal

#print axioms FirmlyNonexpansiveMap.norm_sub_le
#print axioms fixed_iff_sum_zero_of_monotone_forwardBackward
#print axioms contractionCertificate_of_firmlyNonexpansive_resolvent
#print axioms positiveHalfSplit_fixed_iff_zero
#print axioms positiveHalfSplit_positive_branch
#print axioms positiveHalfSplit_iterate_to_zero_le
#print axioms positiveAntiSplit_no_globalContractionCertificate

end

end NonlinearForwardBackward

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
