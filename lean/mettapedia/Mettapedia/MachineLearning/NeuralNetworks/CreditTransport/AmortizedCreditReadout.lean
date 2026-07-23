import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LocalAmortizedInitialization

/-!
# Residual-certified amortized credit readout

A corrective solver may stop early only when its observable residual controls
the quantity ultimately used for plasticity.  This module composes global and
local contraction certificates with a Lipschitz credit readout.  The resulting
theorems turn solver residual tolerances into explicit credit/update tolerances
without allowing the amortized initializer to own the solved endpoint.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace AmortizedCreditReadout

open AmortizedInitialization
open LocalAmortizedInitialization
open PrimalDualStability

variable {State Credit : Type*}
  [NormedAddCommGroup State] [NormedAddCommGroup Credit]

/-- A credit or parameter-update readout is `K`-Lipschitz about the solver's
declared fixed point. -/
def CreditReadoutLipschitzAt
    (readout : State → Credit) (target : State) (K : ℝ) : Prop :=
  ∀ state,
    ‖readout state - readout target‖ ≤ K * ‖state - target‖

/-! ## Global contraction -/

/-- A contractive corrective solve geometrically suppresses the initializer's
error in the actual credit readout. -/
theorem iterate_creditReadout_to_fixedPoint_le
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (target initial : State) (htarget : IsFixedPoint solver target)
    (readout : State → Credit) (K : ℝ) (hK : 0 ≤ K)
    (hreadout : CreditReadoutLipschitzAt readout target K)
    (steps : ℕ) :
    ‖readout (solver^[steps] initial) - readout target‖ ≤
      K * (certificate.factor ^ steps * ‖initial - target‖) := by
  calc
    ‖readout (solver^[steps] initial) - readout target‖ ≤
        K * ‖solver^[steps] initial - target‖ :=
      hreadout _
    _ ≤ K * (certificate.factor ^ steps * ‖initial - target‖) :=
      mul_le_mul_of_nonneg_left
        (iterate_initializer_to_fixedPoint_le certificate target initial
          htarget steps) hK

/-- The observable solver residual bounds error in the credit readout. -/
theorem creditReadout_distance_le_residual_div
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (target state : State) (htarget : IsFixedPoint solver target)
    (readout : State → Credit) (K : ℝ) (hK : 0 ≤ K)
    (hreadout : CreditReadoutLipschitzAt readout target K) :
    ‖readout state - readout target‖ ≤
      K * (‖state - solver state‖ / (1 - certificate.factor)) := by
  calc
    ‖readout state - readout target‖ ≤ K * ‖state - target‖ :=
      hreadout state
    _ ≤ K * (‖state - solver state‖ / (1 - certificate.factor)) :=
      mul_le_mul_of_nonneg_left
        (fixedPoint_distance_le_residual_div certificate target state htarget)
        hK

/-- A residual threshold scaled by the readout sensitivity certifies the
requested credit tolerance. -/
theorem residual_adaptiveStop_for_creditReadout
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (target state : State) (htarget : IsFixedPoint solver target)
    (readout : State → Credit) (K : ℝ) (hK : 0 ≤ K)
    (hreadout : CreditReadoutLipschitzAt readout target K)
    (creditTolerance : ℝ)
    (hresidual :
      K * ‖state - solver state‖ <
        (1 - certificate.factor) * creditTolerance) :
    ‖readout state - readout target‖ < creditTolerance := by
  have hmargin : 0 < 1 - certificate.factor := by
    linarith [certificate.factor_lt_one]
  have hbound := creditReadout_distance_le_residual_div certificate
    target state htarget readout K hK hreadout
  have hscaled :
      K * (‖state - solver state‖ / (1 - certificate.factor)) <
        creditTolerance := by
    rw [show K * (‖state - solver state‖ /
        (1 - certificate.factor)) =
      (K * ‖state - solver state‖) /
        (1 - certificate.factor) by ring]
    exact (div_lt_iff₀ hmargin).2 (by simpa [mul_comm] using hresidual)
  exact lt_of_le_of_lt hbound hscaled

/-! ## Local invariant-region contraction -/

/-- Inside the declared invariant region, a local corrective solve suppresses
initializer error in the credit readout at the same geometric rate. -/
theorem local_iterate_creditReadout_to_fixedPoint_le
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (target initial : State)
    (htargetMem : InClosedBall center radius target)
    (hinitial : InClosedBall center radius initial)
    (htarget : IsFixedPoint solver target)
    (readout : State → Credit) (K : ℝ) (hK : 0 ≤ K)
    (hreadout : CreditReadoutLipschitzAt readout target K)
    (steps : ℕ) :
    ‖readout (solver^[steps] initial) - readout target‖ ≤
      K * (certificate.factor ^ steps * ‖initial - target‖) := by
  calc
    ‖readout (solver^[steps] initial) - readout target‖ ≤
        K * ‖solver^[steps] initial - target‖ :=
      hreadout _
    _ ≤ K * (certificate.factor ^ steps * ‖initial - target‖) :=
      mul_le_mul_of_nonneg_left
        (LocalAmortizedInitialization.iterate_initializer_to_fixedPoint_le
          certificate target initial htargetMem hinitial htarget steps) hK

/-- Local residual-to-credit bound, valid only while both the target and the
current state remain inside the certified neighborhood. -/
theorem local_creditReadout_distance_le_residual_div
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint solver target)
    (readout : State → Credit) (K : ℝ) (hK : 0 ≤ K)
    (hreadout : CreditReadoutLipschitzAt readout target K) :
    ‖readout state - readout target‖ ≤
      K * (‖state - solver state‖ / (1 - certificate.factor)) := by
  calc
    ‖readout state - readout target‖ ≤ K * ‖state - target‖ :=
      hreadout state
    _ ≤ K * (‖state - solver state‖ / (1 - certificate.factor)) :=
      mul_le_mul_of_nonneg_left
        (LocalAmortizedInitialization.fixedPoint_distance_le_residual_div
          certificate target state htargetMem hstateMem htarget) hK

/-- Local residual stopping certifies credit accuracy only inside the declared
invariant neighborhood. -/
theorem local_residual_adaptiveStop_for_creditReadout
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint solver target)
    (readout : State → Credit) (K : ℝ) (hK : 0 ≤ K)
    (hreadout : CreditReadoutLipschitzAt readout target K)
    (creditTolerance : ℝ)
    (hresidual :
      K * ‖state - solver state‖ <
        (1 - certificate.factor) * creditTolerance) :
    ‖readout state - readout target‖ < creditTolerance := by
  have hmargin : 0 < 1 - certificate.factor := by
    linarith [certificate.factor_lt_one]
  have hbound := local_creditReadout_distance_le_residual_div certificate
    target state htargetMem hstateMem htarget readout K hK hreadout
  have hscaled :
      K * (‖state - solver state‖ / (1 - certificate.factor)) <
        creditTolerance := by
    rw [show K * (‖state - solver state‖ /
        (1 - certificate.factor)) =
      (K * ‖state - solver state‖) /
        (1 - certificate.factor) by ring]
    exact (div_lt_iff₀ hmargin).2 (by simpa [mul_comm] using hresidual)
  exact lt_of_le_of_lt hbound hscaled

/-! ## Executable positive and negative boundaries -/

noncomputable def doubleCreditReadout (state : ℝ) : ℝ := 2 * state

theorem doubleCreditReadout_lipschitzAt_zero :
    CreditReadoutLipschitzAt doubleCreditReadout 0 2 := by
  intro state
  simp [doubleCreditReadout, Real.norm_eq_abs]

/-- A stale initializer at `1/8` may stop after its observable residual is
small enough to certify one-half unit of credit accuracy. -/
theorem halfSolver_eighth_residual_certifies_doubleReadout_half :
    |doubleCreditReadout (1 / 8) - doubleCreditReadout 0| < 1 / 2 := by
  have hresidual :
      (2 : ℝ) * |(1 / 8 : ℝ) - halfSolver (1 / 8)| <
        (1 - halfSolverCertificate.factor) * (1 / 2) := by
    norm_num [halfSolver, halfSolverCertificate]
  simpa [Real.norm_eq_abs] using
    residual_adaptiveStop_for_creditReadout halfSolverCertificate 0 (1 / 8)
      halfSolver_zero_fixed doubleCreditReadout 2 (by norm_num)
      doubleCreditReadout_lipschitzAt_zero (1 / 2) hresidual

/-- A stale direct readout at four does not satisfy the same stopping gate;
amortization alone is not a credit-accuracy certificate. -/
theorem halfSolver_stale_directReadout_fails_half_gate :
    ¬ ((2 : ℝ) * |(4 : ℝ) - halfSolver 4| <
      (1 - halfSolverCertificate.factor) * (1 / 2)) := by
  norm_num [halfSolver, halfSolverCertificate]

/-- The nonlinear local fixture also certifies a concrete credit tolerance
while remaining inside its declared unit neighborhood. -/
theorem localQuadratic_tenth_residual_certifies_doubleReadout_one :
    |doubleCreditReadout (1 / 10) - doubleCreditReadout 0| < 1 := by
  have htargetMem : InClosedBall (0 : ℝ) 1 0 := by
    norm_num [InClosedBall]
  have hstateMem : InClosedBall (0 : ℝ) 1 (1 / 10) := by
    norm_num [InClosedBall, Real.norm_eq_abs]
  have hresidual :
      (2 : ℝ) * |(1 / 10 : ℝ) - localQuadraticErrorMap (1 / 10)| <
        (1 - localQuadraticCertificate.factor) * 1 := by
    norm_num [localQuadraticCertificate, localQuadraticErrorMap,
      scalarQuadraticErrorMap, abs_of_nonneg]
  simpa [Real.norm_eq_abs] using
    local_residual_adaptiveStop_for_creditReadout localQuadraticCertificate
      0 (1 / 10) htargetMem hstateMem localQuadraticErrorMap_zero_fixed
      doubleCreditReadout 2 (by norm_num)
      doubleCreditReadout_lipschitzAt_zero 1 hresidual

#print axioms iterate_creditReadout_to_fixedPoint_le
#print axioms creditReadout_distance_le_residual_div
#print axioms residual_adaptiveStop_for_creditReadout
#print axioms local_iterate_creditReadout_to_fixedPoint_le
#print axioms local_creditReadout_distance_le_residual_div
#print axioms local_residual_adaptiveStop_for_creditReadout
#print axioms halfSolver_eighth_residual_certifies_doubleReadout_half
#print axioms halfSolver_stale_directReadout_fails_half_gate
#print axioms localQuadratic_tenth_residual_certifies_doubleReadout_one

end AmortizedCreditReadout

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
