import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CarrierCutHybridDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.EnergyDecrementStopping
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.JacobianRemainderContraction
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegionalLinearizationCertificate

/-!
# Local contraction and observable admission for carrier-cut settling

The carrier-cut inference map is the damped gradient step used by the trainer:
the task gradient is augmented by a quadratic prediction penalty of precision
`precision`, then scaled by the accepted inference rate.  Around a stationary
center, its effective linearization is

`I - rate * (taskLinearization + precision * I)`.

The local contraction factor below is the operator norm of this map plus a
curvature remainder `rate * curvature * radius`.  This makes the rate,
precision, audited task linearization, curvature bound, and trusted ball
explicit.  A second layer rewrites the solver residual into the final
energy-gradient norm logged by the trainer.  The energy trace is retained as a
separate monotonicity check; it is not allowed to substitute for contraction.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CarrierCutSettlingContraction

open scoped InnerProductSpace
open AmortizedInitialization
open AmortizedCreditReadout
open CarrierCutHybridDescent
open DirectionalTaskDescent
open EnergyDecrementStopping
open JacobianRemainderContraction
open LocalAmortizedInitialization
open ProspectiveResidualSemantics
open RegionalLinearizationCertificate

noncomputable section

variable {State Upstream Head : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]
  [NormedAddCommGroup Upstream] [InnerProductSpace ℝ Upstream]
  [NormedAddCommGroup Head] [InnerProductSpace ℝ Head]

/-! ## The trainer's carrier-cut map and its effective linearization -/

/-- One accepted carrier-cut inference step.  This is a mathematical name for
the existing prospective gradient step, not a second solver semantics. -/
def carrierCutSettleMap
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) : State → State :=
  prospectiveGradientStep prediction precision rate taskGradient

/-- Linearization of one carrier-cut step around a stationary state. -/
noncomputable def effectiveSettleLinearization
    (rate precision : ℝ) (taskLinearization : State →L[ℝ] State) :
    State →L[ℝ] State :=
  ContinuousLinearMap.id ℝ State -
    rate • (taskLinearization +
      precision • ContinuousLinearMap.id ℝ State)

/-- Nonlinear task-gradient remainder after paying the accepted inference
rate.  The quadratic prediction penalty is already represented exactly in the
effective linearization. -/
def settledTaskRemainder
    (rate : ℝ) (taskGradient : State → State) (center : State)
    (taskLinearization : State →L[ℝ] State) (state : State) : State :=
  -(rate • gradientLinearizationRemainder
    taskGradient center taskLinearization state)

/-- Auditable local data for the actual carrier-cut settle map.  The nonlinear
task-gradient remainder is bounded by `curvature * radius` on the declared
ball; after multiplying by the inference rate, the complete contraction factor
is the effective-linearization norm plus `rate * curvature * radius`. -/
structure SettlingLinearizationCertificate
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) (center : State) (radius : ℝ)
    (taskLinearization : State →L[ℝ] State) where
  radius_nonneg : 0 ≤ radius
  rate_nonneg : 0 ≤ rate
  curvature : ℝ
  curvature_nonneg : 0 ≤ curvature
  center_stationary :
    prospectiveEnergyGradient prediction precision taskGradient center = 0
  taskRemainder_pair_bound : ∀ left right,
    InClosedBall center radius left → InClosedBall center radius right →
    ‖gradientLinearizationRemainder taskGradient center taskLinearization left -
        gradientLinearizationRemainder taskGradient center taskLinearization right‖ ≤
      curvature * radius * ‖left - right‖
  contractionFactor_lt_one :
    ‖effectiveSettleLinearization rate precision taskLinearization‖ +
      rate * curvature * radius < 1

/-- The factor exposed to the stopping rule and timing pilot. -/
def settlingContractionFactor
    {prediction : State} {precision rate : ℝ}
    {taskGradient : State → State} {center : State} {radius : ℝ}
    {taskLinearization : State →L[ℝ] State}
    (certificate : SettlingLinearizationCertificate prediction precision rate
      taskGradient center radius taskLinearization) : ℝ :=
  ‖effectiveSettleLinearization rate precision taskLinearization‖ +
    rate * certificate.curvature * radius

theorem settledTaskRemainder_center_zero
    (rate : ℝ) (taskGradient : State → State) (center : State)
    (taskLinearization : State →L[ℝ] State) :
    settledTaskRemainder rate taskGradient center taskLinearization center = 0 := by
  simp [settledTaskRemainder, gradientLinearizationRemainder]

/-- At a stationary center, the trainer's nonlinear step is exactly the
linearized map plus the paid nonlinear remainder. -/
theorem carrierCutSettleMap_eq_linearRemainderSolver
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) (center : State)
    (taskLinearization : State →L[ℝ] State)
    (hstationary :
      prospectiveEnergyGradient prediction precision taskGradient center = 0) :
    carrierCutSettleMap prediction precision rate taskGradient =
      linearRemainderSolver center
        (effectiveSettleLinearization rate precision taskLinearization)
        (settledTaskRemainder rate taskGradient center taskLinearization) := by
  funext state
  have hcenter :
      taskGradient center + precision • (center - prediction) = 0 := by
    simpa [prospectiveEnergyGradient] using hstationary
  simp only [carrierCutSettleMap, prospectiveGradientStep,
    prospectiveEnergyGradient, linearRemainderSolver,
    effectiveSettleLinearization, settledTaskRemainder,
    gradientLinearizationRemainder, sub_apply,
    smul_apply, add_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [eq_neg_of_add_eq_zero_left hcenter]
  module

/-- The explicit operator norm and curvature budget produce the generic
linear-plus-remainder certificate. -/
noncomputable def SettlingLinearizationCertificate.toLinearRemainderBudget
    {prediction : State} {precision rate : ℝ}
    {taskGradient : State → State} {center : State} {radius : ℝ}
    {taskLinearization : State →L[ℝ] State}
    (certificate : SettlingLinearizationCertificate prediction precision rate
      taskGradient center radius taskLinearization) :
    LinearRemainderBudget
      (effectiveSettleLinearization rate precision taskLinearization)
      (settledTaskRemainder rate taskGradient center taskLinearization)
      center radius where
  linearFactor := ‖effectiveSettleLinearization rate precision taskLinearization‖
  remainderFactor := rate * certificate.curvature * radius
  linearFactor_nonneg := norm_nonneg _
  remainderFactor_nonneg :=
    mul_nonneg (mul_nonneg certificate.rate_nonneg
      certificate.curvature_nonneg) certificate.radius_nonneg
  radius_nonneg := certificate.radius_nonneg
  totalFactor_lt_one := certificate.contractionFactor_lt_one
  linear_bound :=
    (effectiveSettleLinearization rate precision taskLinearization).le_opNorm
  remainder_center_zero :=
    settledTaskRemainder_center_zero rate taskGradient center taskLinearization
  remainder_pair_bound := by
    intro left right hleft hright
    have htask := certificate.taskRemainder_pair_bound left right hleft hright
    have hrewrite :
        settledTaskRemainder rate taskGradient center taskLinearization left -
            settledTaskRemainder rate taskGradient center taskLinearization right =
          -(rate •
            (gradientLinearizationRemainder taskGradient center taskLinearization left -
              gradientLinearizationRemainder taskGradient center taskLinearization right)) := by
      simp only [settledTaskRemainder]
      module
    rw [hrewrite, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg certificate.rate_nonneg]
    calc
      rate *
          ‖gradientLinearizationRemainder taskGradient center taskLinearization left -
            gradientLinearizationRemainder taskGradient center taskLinearization right‖ ≤
          rate * (certificate.curvature * radius * ‖left - right‖) :=
        mul_le_mul_of_nonneg_left htask certificate.rate_nonneg
      _ = (rate * certificate.curvature * radius) * ‖left - right‖ := by ring

/-- The carrier-cut settle map contracts and preserves the stated ball with
factor `‖I - rate * (J + precision * I)‖ + rate * curvature * radius`. -/
noncomputable def SettlingLinearizationCertificate.toLocalContractionCertificate
    {prediction : State} {precision rate : ℝ}
    {taskGradient : State → State} {center : State} {radius : ℝ}
    {taskLinearization : State →L[ℝ] State}
    (certificate : SettlingLinearizationCertificate prediction precision rate
      taskGradient center radius taskLinearization) :
    LocalContractionCertificate
      (carrierCutSettleMap prediction precision rate taskGradient)
      center radius where
  factor := ‖effectiveSettleLinearization rate precision taskLinearization‖ +
    rate * certificate.curvature * radius
  factor_nonneg := add_nonneg (norm_nonneg _)
    (mul_nonneg (mul_nonneg certificate.rate_nonneg
      certificate.curvature_nonneg) certificate.radius_nonneg)
  factor_lt_one := certificate.contractionFactor_lt_one
  radius_nonneg := certificate.radius_nonneg
  maps_ball := by
    intro state hstate
    rw [carrierCutSettleMap_eq_linearRemainderSolver prediction precision rate
      taskGradient center taskLinearization certificate.center_stationary]
    exact certificate.toLinearRemainderBudget.toLocalContractionCertificate.maps_ball
      state hstate
  contracts_on_ball := by
    intro left right hleft hright
    rw [carrierCutSettleMap_eq_linearRemainderSolver prediction precision rate
      taskGradient center taskLinearization certificate.center_stationary]
    exact certificate.toLinearRemainderBudget.toLocalContractionCertificate.contracts_on_ball
      left right hleft hright

@[simp] theorem SettlingLinearizationCertificate.local_factor
    {prediction : State} {precision rate : ℝ}
    {taskGradient : State → State} {center : State} {radius : ℝ}
    {taskLinearization : State →L[ℝ] State}
    (certificate : SettlingLinearizationCertificate prediction precision rate
      taskGradient center radius taskLinearization) :
    certificate.toLocalContractionCertificate.factor =
      settlingContractionFactor certificate := by
  rfl

/-! ## Trainer-observable stopping admission -/

/-- The two quantities emitted by the settle loop which enter the admission
check.  Configuration constants such as rate and the certified contraction
factor remain part of the frozen solver configuration. -/
structure SettlingObservables where
  energySequence : List ℝ
  finalGradientNorm : ℝ

/-- The energy sequence is a sanity check in the same temporal order used by
the trainer: every later energy is no greater than each earlier entry. -/
def SettlingObservables.EnergyNonincreasing
    (observables : SettlingObservables) : Prop :=
  observables.energySequence.Pairwise (fun earlier later => later ≤ earlier)

/-- Purely numeric upstream-error budget computed from the logged final
energy-gradient norm and the certified local contraction factor. -/
def loggedUpstreamErrorBudget
    (factor rate finalGradientNorm sensitivity equilibriumMismatch : ℝ) : ℝ :=
  sensitivity * (rate * finalGradientNorm / (1 - factor)) +
    equilibriumMismatch

/-- Pure residual contribution when the exact-equilibrium readout is certified
to equal the upstream task gradient.  Every run-dependent input is one of the
two fields of `SettlingObservables`; factor, rate, and sensitivity are frozen
certificate/configuration constants. -/
def loggedResidualCreditError
    (factor rate finalGradientNorm sensitivity : ℝ) : ℝ :=
  sensitivity * (rate * finalGradientNorm / (1 - factor))

/-- Lookup-style inference admission.  The trace must be monotone as a sanity
check and the certified residual error computed from the logged final gradient
norm must fit under the frozen tolerance. -/
def ObservableSettlingAdmission
    (observables : SettlingObservables)
    (factor rate sensitivity tolerance : ℝ) : Prop :=
  observables.EnergyNonincreasing ∧
  0 ≤ observables.finalGradientNorm ∧
  loggedResidualCreditError factor rate observables.finalGradientNorm
    sensitivity ≤ tolerance

/-- Result-blind admission predicate: energy monotonicity is checked, the
logged norm must be nonnegative, and the downstream task-step margin must
remain positive after paying the observable upstream-error budget. -/
def ObservableHybridAdmission
    (observables : SettlingObservables)
    (factor rate sensitivity equilibriumMismatch taskStep taskCurvature : ℝ)
    (upstreamGradient : Upstream) (headGradient : Head) : Prop :=
  observables.EnergyNonincreasing ∧
  0 ≤ observables.finalGradientNorm ∧
  taskStep * taskCurvature / 2 <
    ‖upstreamGradient‖ *
      (‖upstreamGradient‖ -
        loggedUpstreamErrorBudget factor rate observables.finalGradientNorm
          sensitivity equilibriumMismatch) +
      ‖headGradient‖ ^ 2

/-- The norm of the actual settle-map residual is exactly the configured rate
times the final energy-gradient norm. -/
theorem norm_settleResidual_eq_rate_mul_gradientNorm
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) (state : State)
    (hrate : 0 ≤ rate) :
    ‖state - carrierCutSettleMap prediction precision rate taskGradient state‖ =
      rate * ‖prospectiveEnergyGradient prediction precision taskGradient state‖ := by
  rw [show state - carrierCutSettleMap prediction precision rate taskGradient state =
      rate • prospectiveEnergyGradient prediction precision taskGradient state by
    exact prospectiveGradientStep_displacement prediction precision rate
      taskGradient state]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrate]

omit [InnerProductSpace ℝ Upstream] in
/-- The local residual budget is exactly the numeric budget shown to the
trainer once the logged final norm and equilibrium mismatch are bound to their
mathematical values. -/
theorem localResidualUpstreamErrorBudget_eq_logged
    {prediction : State} {precision rate : ℝ}
    {taskGradient : State → State} {center : State} {radius : ℝ}
    {taskLinearization : State →L[ℝ] State}
    (certificate : SettlingLinearizationCertificate prediction precision rate
      taskGradient center radius taskLinearization)
    (target state : State) (readout : State → Upstream)
    (upstreamGradient : Upstream) (sensitivity : ℝ)
    (observables : SettlingObservables)
    (hgradient : observables.finalGradientNorm =
      ‖prospectiveEnergyGradient prediction precision taskGradient state‖) :
    localResidualUpstreamErrorBudget certificate.toLocalContractionCertificate
        target state readout upstreamGradient sensitivity =
      loggedUpstreamErrorBudget (settlingContractionFactor certificate) rate
        observables.finalGradientNorm sensitivity
        ‖readout target - upstreamGradient‖ := by
  unfold localResidualUpstreamErrorBudget loggedUpstreamErrorBudget
  rw [certificate.local_factor,
    norm_settleResidual_eq_rate_mul_gradientNorm prediction precision rate
      taskGradient state certificate.rate_nonneg, hgradient]

omit [InnerProductSpace ℝ Upstream] in
/-- The logged final-gradient norm bounds upstream credit error after the A1
ball certificate has supplied the missing contraction premise. -/
theorem upstreamCreditError_le_loggedSettlingBudget
    {prediction : State} {precision rate : ℝ}
    {taskGradient : State → State} {center : State} {radius : ℝ}
    {taskLinearization : State →L[ℝ] State}
    (certificate : SettlingLinearizationCertificate prediction precision rate
      taskGradient center radius taskLinearization)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint
      (carrierCutSettleMap prediction precision rate taskGradient) target)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (sensitivity : ℝ) (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout target sensitivity)
    (observables : SettlingObservables)
    (hgradient : observables.finalGradientNorm =
      ‖prospectiveEnergyGradient prediction precision taskGradient state‖) :
    ‖readout state - upstreamGradient‖ ≤
      loggedUpstreamErrorBudget (settlingContractionFactor certificate) rate
        observables.finalGradientNorm sensitivity
        ‖readout target - upstreamGradient‖ := by
  have hbound := upstreamCreditError_le_localResidualBudget
    certificate.toLocalContractionCertificate target state htargetMem hstateMem
    htarget readout upstreamGradient sensitivity hsensitivity hreadout
  rw [localResidualUpstreamErrorBudget_eq_logged certificate target state
    readout upstreamGradient sensitivity observables hgradient] at hbound
  exact hbound

omit [InnerProductSpace ℝ Upstream] in
/-- With exact equilibrium readout, no hidden fixed-point distance or
equilibrium mismatch occurs in the runtime admission bound. -/
theorem upstreamCreditError_le_loggedResidual
    {prediction : State} {precision rate : ℝ}
    {taskGradient : State → State} {center : State} {radius : ℝ}
    {taskLinearization : State →L[ℝ] State}
    (certificate : SettlingLinearizationCertificate prediction precision rate
      taskGradient center radius taskLinearization)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint
      (carrierCutSettleMap prediction precision rate taskGradient) target)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (htargetReadout : readout target = upstreamGradient)
    (sensitivity : ℝ) (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout target sensitivity)
    (observables : SettlingObservables)
    (hgradient : observables.finalGradientNorm =
      ‖prospectiveEnergyGradient prediction precision taskGradient state‖) :
    ‖readout state - upstreamGradient‖ ≤
      loggedResidualCreditError (settlingContractionFactor certificate) rate
        observables.finalGradientNorm sensitivity := by
  have hbound := upstreamCreditError_le_loggedSettlingBudget certificate
    target state htargetMem hstateMem htarget readout upstreamGradient
    sensitivity hsensitivity hreadout observables hgradient
  simpa [loggedUpstreamErrorBudget, loggedResidualCreditError,
    htargetReadout] using hbound

/-- The pure lookup admission implies task descent once its chosen tolerance
fits inside the independent parameter-step curvature margin. -/
theorem observableSettlingAdmission_strictTaskDescent
    {prediction : State} {precision rate : ℝ}
    {taskGradient : State → State} {center : State} {radius : ℝ}
    {taskLinearization : State →L[ℝ] State}
    (certificate : SettlingLinearizationCertificate prediction precision rate
      taskGradient center radius taskLinearization)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint
      (carrierCutSettleMap prediction precision rate taskGradient) target)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (headGradient : Head)
    (htargetReadout : readout target = upstreamGradient)
    (sensitivity : ℝ) (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout target sensitivity)
    (observables : SettlingObservables)
    (hgradient : observables.finalGradientNorm =
      ‖prospectiveEnergyGradient prediction precision taskGradient state‖)
    (tolerance : ℝ)
    (hadmission : ObservableSettlingAdmission observables
      (settlingContractionFactor certificate) rate sensitivity tolerance)
    {loss : ProductParameter Upstream Head → ℝ}
    {parameter : ProductParameter Upstream Head}
    {taskCurvature taskStep : ℝ}
    (taskCertificate : HasDirectionalTaskUpperModelAt loss parameter
      (productTaskGradient upstreamGradient headGradient)
      (hybridDirection (readout state) headGradient) taskCurvature)
    (htaskStep : 0 < taskStep)
    (htrust : taskStep * taskCurvature / 2 <
      ‖upstreamGradient‖ * (‖upstreamGradient‖ - tolerance) +
        ‖headGradient‖ ^ 2) :
    loss (parameter - taskStep • hybridDirection (readout state) headGradient) <
      loss parameter := by
  apply hybrid_strictTaskDescent_of_upstream_error taskCertificate
    (le_trans
      (upstreamCreditError_le_loggedResidual certificate target state
        htargetMem hstateMem htarget readout upstreamGradient htargetReadout
        sensitivity hsensitivity hreadout observables hgradient)
      hadmission.2.2)
    htaskStep htrust

/-- Inside the certified ball, the pure logged-observable admission inequality
feeds the existing hybrid task-descent theorem verbatim. -/
theorem observableCertifiedHybrid_strictTaskDescent
    {prediction : State} {precision rate : ℝ}
    {taskGradient : State → State} {center : State} {radius : ℝ}
    {taskLinearization : State →L[ℝ] State}
    (certificate : SettlingLinearizationCertificate prediction precision rate
      taskGradient center radius taskLinearization)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint
      (carrierCutSettleMap prediction precision rate taskGradient) target)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (headGradient : Head) (sensitivity : ℝ)
    (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout target sensitivity)
    (observables : SettlingObservables)
    (hgradient : observables.finalGradientNorm =
      ‖prospectiveEnergyGradient prediction precision taskGradient state‖)
    {loss : ProductParameter Upstream Head → ℝ}
    {parameter : ProductParameter Upstream Head}
    {taskCurvature taskStep : ℝ}
    (taskCertificate : HasDirectionalTaskUpperModelAt loss parameter
      (productTaskGradient upstreamGradient headGradient)
      (hybridDirection (readout state) headGradient) taskCurvature)
    (htaskStep : 0 < taskStep)
    (hadmission : ObservableHybridAdmission observables
      (settlingContractionFactor certificate) rate sensitivity
      ‖readout target - upstreamGradient‖ taskStep taskCurvature
      upstreamGradient headGradient) :
    loss (parameter - taskStep • hybridDirection (readout state) headGradient) <
      loss parameter := by
  apply hybrid_strictTaskDescent_of_upstream_error taskCertificate
    (upstreamCreditError_le_loggedSettlingBudget certificate target state
      htargetMem hstateMem htarget readout upstreamGradient sensitivity
      hsensitivity hreadout observables hgradient)
    htaskStep
  exact hadmission.2.2

/-! ## Positive and negative ignition boundaries -/

noncomputable def scalarIdentityLinearization : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.id ℝ ℝ

def scalarIdentityTaskGradient (state : ℝ) : ℝ := state

theorem effectiveSettleLinearization_quarter_identity :
    effectiveSettleLinearization (1 / 4 : ℝ) 1
      scalarIdentityLinearization =
        (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro state
  simp [effectiveSettleLinearization, scalarIdentityLinearization]
  ring

/-- Positive fixture: on the unit ball, unit precision and quarter-rate
settling for the identity task gradient contracts by exactly one half. -/
noncomputable def scalarIdentitySettlingCertificate :
    SettlingLinearizationCertificate (State := ℝ)
      0 1 (1 / 4) scalarIdentityTaskGradient 0 1
      scalarIdentityLinearization where
  radius_nonneg := by norm_num
  rate_nonneg := by norm_num
  curvature := 0
  curvature_nonneg := by norm_num
  center_stationary := by
    norm_num [prospectiveEnergyGradient, scalarIdentityTaskGradient]
  taskRemainder_pair_bound := by
    intro left right _ _
    simp [gradientLinearizationRemainder, scalarIdentityTaskGradient,
      scalarIdentityLinearization]
  contractionFactor_lt_one := by
    rw [effectiveSettleLinearization_quarter_identity]
    rw [norm_smul, ContinuousLinearMap.norm_id]
    norm_num

theorem scalarIdentity_settleMap_eq_half (state : ℝ) :
    carrierCutSettleMap 0 1 (1 / 4) scalarIdentityTaskGradient state =
      state / 2 := by
  simp [carrierCutSettleMap, prospectiveGradientStep,
    prospectiveEnergyGradient, scalarIdentityTaskGradient]
  ring

theorem scalarIdentity_settling_factor_eq_half :
    settlingContractionFactor scalarIdentitySettlingCertificate = 1 / 2 := by
  unfold settlingContractionFactor
  rw [effectiveSettleLinearization_quarter_identity, norm_smul,
    ContinuousLinearMap.norm_id]
  norm_num [scalarIdentitySettlingCertificate]

/-- Affine task field whose unit-rate, unit-precision settle map is expansive.
The first step still satisfies the exact BP ignition identity. -/
def expansiveAffineTaskGradient (state : ℝ) : ℝ := 2 * state + 1

theorem expansiveAffine_settleMap (state : ℝ) :
    carrierCutSettleMap 0 1 1 expansiveAffineTaskGradient state =
      -2 * state - 1 := by
  simp [carrierCutSettleMap, prospectiveGradientStep,
    prospectiveEnergyGradient, expansiveAffineTaskGradient]
  ring

theorem expansiveAffine_expands_unit_pair :
    ‖carrierCutSettleMap 0 1 1 expansiveAffineTaskGradient 1 -
        carrierCutSettleMap 0 1 1 expansiveAffineTaskGradient 0‖ =
      2 * ‖(1 : ℝ) - 0‖ := by
  norm_num [expansiveAffine_settleMap]

/-- Explicit ignition boundary: one step gives the true gradient `1`, whereas
two expansive steps give prospective credit `-1`, whose inner product with the
true gradient is negative. -/
theorem expansiveAffine_secondStep_credit_antialigns :
    let first := carrierCutSettleMap 0 1 1 expansiveAffineTaskGradient 0
    let second := carrierCutSettleMap 0 1 1 expansiveAffineTaskGradient first
    (1 : ℝ) • (0 - first) = expansiveAffineTaskGradient 0 ∧
      ⟪expansiveAffineTaskGradient 0, (1 : ℝ) • (0 - second)⟫_ℝ < 0 := by
  norm_num [expansiveAffine_settleMap, expansiveAffineTaskGradient]

/-- A strictly decreasing energy trace is not a contraction certificate: the
translation solver decreases affine energy everywhere while expanding no
distances at all and having no fixed point. -/
theorem monotoneEnergy_does_not_supply_contraction :
    (∀ state : ℝ,
      descendingAffineEnergy (shiftSolver state) < descendingAffineEnergy state) ∧
      ¬ Nonempty (ContractionCertificate shiftSolver) := by
  exact ⟨shiftSolver_strictly_decreases_energy,
    shiftSolver_has_no_contractionCertificate⟩

/-- Concrete positive trace for the observable monotonicity convention. -/
theorem decreasingEnergyTrace_is_nonincreasing :
    ({ energySequence := [3, 2, 1]
       finalGradientNorm := 1 / 10 } : SettlingObservables).EnergyNonincreasing := by
  norm_num [SettlingObservables.EnergyNonincreasing]

#print axioms carrierCutSettleMap_eq_linearRemainderSolver
#print axioms SettlingLinearizationCertificate.toLocalContractionCertificate
#print axioms upstreamCreditError_le_loggedSettlingBudget
#print axioms upstreamCreditError_le_loggedResidual
#print axioms observableSettlingAdmission_strictTaskDescent
#print axioms observableCertifiedHybrid_strictTaskDescent
#print axioms scalarIdentitySettlingCertificate
#print axioms expansiveAffine_secondStep_credit_antialigns
#print axioms monotoneEnergy_does_not_supply_contraction

end

end CarrierCutSettlingContraction

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
