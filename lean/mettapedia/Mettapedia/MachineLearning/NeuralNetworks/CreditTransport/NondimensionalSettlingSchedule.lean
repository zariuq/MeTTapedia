import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SettledCreditClosedForm
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PreconditionedBranchStableContraction

/-!
# Nondimensional predictive-coding settling schedules

An Euler state update written with a time increment `dt` and time constant
`tau` depends on those two quantities only through `dt / tau`, provided the
preconditioner and vector field are unchanged.  The dimensionless rate alone
is not a stability constant: stability is controlled by its product with the
preconditioned curvature operator.

This file connects that observation to the finite-depth credit theory.  It
also records the exact scalar residual schedules used by the Unified and
staged AC experiments.  The AC registration preserves
`precision * rate * sweeps = 1` at every stage, but the exact Euler response is
`1 - (1 - precision * rate)^sweeps`; consequently neither the finite endpoint
nor the finite credit is invariant across those stages.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace NondimensionalSettlingSchedule

open scoped InnerProductSpace
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open CarrierOutputPC
open ProspectiveResidualSemantics
open SettledCreditClosedForm
open PreconditionedBranchStableContraction
open LocalAmortizedInitialization

noncomputable section

/-! ## Euler clocks and finite-trajectory equivalence -/

/-- A source-facing Euler clock.  Neither field scaling nor a preconditioner
is hidden inside this record. -/
structure EulerClock where
  dt : ℝ
  tau : ℝ

/-- Dimensionless Euler rate. -/
def EulerClock.rate (clock : EulerClock) : ℝ :=
  clock.dt / clock.tau

variable {State : Type*} [AddCommGroup State] [Module ℝ State]

/-- One explicit Euler step for a fixed vector field. -/
def eulerStep (clock : EulerClock) (field : State → State)
    (state : State) : State :=
  state - clock.rate • field state

/-- Two clocks with the same ratio define the same one-step map when the
vector field is unchanged. -/
theorem eulerStep_eq_of_rate_eq
    (left right : EulerClock) (field : State → State)
    (hrate : left.rate = right.rate) :
    eulerStep left field = eulerStep right field := by
  funext state
  simp only [eulerStep, hrate]

/-- Ratio equality therefore preserves every finite Euler trajectory, not
merely a stationary set or a continuous-time limit. -/
theorem eulerIterate_eq_of_rate_eq
    (left right : EulerClock) (field : State → State)
    (hrate : left.rate = right.rate) (steps : ℕ) :
    (eulerStep left field)^[steps] = (eulerStep right field)^[steps] := by
  rw [eulerStep_eq_of_rate_eq left right field hrate]

/-- A common nonzero rescaling of `dt` and `tau` leaves the dimensionless
rate unchanged. -/
theorem EulerClock.rate_scale_both
    (clock : EulerClock) (scale : ℝ) (hscale : scale ≠ 0) :
    ({ dt := scale * clock.dt, tau := scale * clock.tau } : EulerClock).rate =
      clock.rate := by
  simp only [EulerClock.rate]
  rw [mul_div_mul_left _ _ hscale]

/-! ## Preconditioned clocks and row-mass cancellation -/

section Preconditioned

variable {HState : Type*}
  [NormedAddCommGroup HState] [InnerProductSpace ℝ HState]

/-- The clock form of the implementation's preconditioned Euler proposal. -/
def preconditionedEulerStep
    (clock : EulerClock) (preconditioner : HState →L[ℝ] HState)
    (gradient : HState → HState) : HState → HState :=
  eulerStep clock (preconditionedField preconditioner gradient)

theorem preconditionedEulerStep_eq_preconditionedStep
    (clock : EulerClock) (preconditioner : HState →L[ℝ] HState)
    (gradient : HState → HState) :
    preconditionedEulerStep clock preconditioner gradient =
      preconditionedStep preconditioner clock.rate gradient := by
  rfl

/-- Gradient shape for a row-mass-weighted residual energy. -/
def massWeightedResidualGradient
    (mass : HState →L[ℝ] HState) (prediction : HState) (precision : ℝ)
    (taskGradient : HState → HState) (state : HState) : HState :=
  taskGradient state + precision • mass (state - prediction)

/-- An exact inverse-mass preconditioner cancels the row masses in the
residual term, while leaving precision and the preconditioned task gradient
visible.  Thus inverse row mass does not cancel residual precision. -/
theorem preconditioned_massWeightedResidualGradient
    (mass inverseMass : HState →L[ℝ] HState)
    (inverse_left : ∀ displacement, inverseMass (mass displacement) = displacement)
    (prediction : HState) (precision : ℝ)
    (taskGradient : HState → HState) (state : HState) :
    preconditionedField inverseMass
        (massWeightedResidualGradient mass prediction precision taskGradient)
        state =
      inverseMass (taskGradient state) + precision • (state - prediction) := by
  simp [preconditionedField, massWeightedResidualGradient, map_add, map_smul,
    inverse_left]

/-- Regional spectral stability expressed directly in clock units.  The
coercivity and Lipschitz constants concern the preconditioned Jacobian, so the
condition is on `(dt/tau) * L^2`, not on `dt/tau` alone. -/
noncomputable def nondimensionalPreconditionedLocalCertificate
    (clock : EulerClock)
    (preconditioner : HState →L[ℝ] HState)
    (gradient : HState → HState) (center : HState) (radius : ℝ)
    (enclosure : PreconditionedJacobianEnclosure
      preconditioner gradient center radius)
    (hrate : 0 < clock.rate)
    (hstable :
      clock.rate *
          (‖preconditioner.comp (fderiv ℝ gradient center)‖ +
            ‖preconditioner‖ * enclosure.rawJacobianVariation) ^ 2 <
        2 * (enclosure.linearModulus -
          ‖preconditioner‖ * enclosure.rawJacobianVariation))
    (hadmission :
      ‖preconditionedEulerStep clock preconditioner gradient center - center‖ ≤
        (1 - hilbertSettlingContraction
          (enclosure.linearModulus -
            ‖preconditioner‖ * enclosure.rawJacobianVariation)
          (‖preconditioner.comp (fderiv ℝ gradient center)‖ +
            ‖preconditioner‖ * enclosure.rawJacobianVariation)
          clock.rate) * radius) :
    LocalContractionCertificate
      (preconditionedEulerStep clock preconditioner gradient) center radius := by
  rw [preconditionedEulerStep_eq_preconditionedStep] at hadmission ⊢
  exact enclosure.toLocalContractionCertificate hrate hstable hadmission

end Preconditioned

/-! ## Exact scalar finite schedules -/

/-- A constant-rate residual-only settling schedule. -/
structure ScalarResidualSchedule where
  rate : ℝ
  precision : ℝ
  sweeps : ℕ

/-- The linear exposure used by the AC registration. -/
def ScalarResidualSchedule.nominalExposure
    (schedule : ScalarResidualSchedule) : ℝ :=
  schedule.precision * schedule.rate * schedule.sweeps

/-- One-step signed residual multiplier. -/
def ScalarResidualSchedule.residualFactor
    (schedule : ScalarResidualSchedule) : ℝ :=
  1 - schedule.rate * schedule.precision

/-- Exact finite response of local residual credit to a constant source
credit in the zero-task-curvature affine model. -/
def ScalarResidualSchedule.finiteResponse
    (schedule : ScalarResidualSchedule) : ℝ :=
  1 - schedule.residualFactor ^ schedule.sweeps

/-- Exact remaining residual magnitude multiplier. -/
def ScalarResidualSchedule.residualRemainder
    (schedule : ScalarResidualSchedule) : ℝ :=
  |schedule.residualFactor| ^ schedule.sweeps

/-- Exact scalar endpoint around a target. -/
def ScalarResidualSchedule.endpoint
    (schedule : ScalarResidualSchedule) (target initial : ℝ) : ℝ :=
  (quadraticSettlingStep schedule.rate schedule.precision target)^[schedule.sweeps]
    initial

theorem ScalarResidualSchedule.endpoint_eq
    (schedule : ScalarResidualSchedule) (target initial : ℝ) :
    schedule.endpoint target initial =
      target + schedule.residualFactor ^ schedule.sweeps * (initial - target) := by
  exact quadraticSettlingStep_iterate_exact schedule.rate schedule.precision
    target initial schedule.sweeps

theorem ScalarResidualSchedule.endpoint_residual_abs_eq
    (schedule : ScalarResidualSchedule) (target initial : ℝ) :
    |schedule.endpoint target initial - target| =
      schedule.residualRemainder * |initial - target| := by
  exact quadraticSettlingStep_residual_exact schedule.rate schedule.precision
    target initial schedule.sweeps

/-- The geometric settle sum and the exact finite response are the same
quantity. -/
theorem ScalarResidualSchedule.finiteResponse_eq_creditScale
    (schedule : ScalarResidualSchedule) :
    schedule.finiteResponse =
      schedule.precision *
        (schedule.rate * settleSum schedule.precision schedule.rate 0
          schedule.sweeps) := by
  let factor : ℝ := schedule.residualFactor
  have hgeom := geom_sum_mul factor schedule.sweeps
  have hfactor : 1 - factor = schedule.precision * schedule.rate := by
    simp only [factor, ScalarResidualSchedule.residualFactor]
    ring
  calc
    schedule.finiteResponse = 1 - factor ^ schedule.sweeps := by
      rfl
    _ = (1 - factor) * (∑ k ∈ Finset.range schedule.sweeps, factor ^ k) := by
      rw [show (1 - factor) * (∑ k ∈ Finset.range schedule.sweeps, factor ^ k) =
          -((∑ k ∈ Finset.range schedule.sweeps, factor ^ k) *
            (factor - 1)) by ring, hgeom]
      ring
    _ = schedule.precision *
        (schedule.rate * settleSum schedule.precision schedule.rate 0
          schedule.sweeps) := by
      rw [hfactor]
      simp only [settleSum, contractionFactor, factor,
        ScalarResidualSchedule.residualFactor]
      ring_nf

/-- Existing affine settled-credit semantics, restated using the exact finite
response rather than a geometric sum. -/
theorem settledCredit_eq_finiteResponse_smul_carrierBPCredit
    {CreditState : Type*}
    [NormedAddCommGroup CreditState] [InnerProductSpace ℝ CreditState]
    {Parameter : Type*} [NormedAddCommGroup Parameter]
    [NormedSpace ℝ Parameter]
    (pullback : CreditState →ₗ[ℝ] Parameter)
    (prediction bpCredit : CreditState) (schedule : ScalarResidualSchedule) :
    carrierLocalCredit pullback prediction
        (settleIterate prediction schedule.precision schedule.rate
          (scalarCurvatureField prediction 0 bpCredit) schedule.sweeps)
        schedule.precision =
      schedule.finiteResponse •
        carrierBPCredit pullback
          (scalarCurvatureField prediction 0 bpCredit) prediction := by
  rw [settledCredit_eq_smul_carrierBPCredit]
  rw [schedule.finiteResponse_eq_creditScale]

/-! ## Stability and fixed-point boundaries -/

/-- Exact scalar stability interval. -/
theorem settlingContraction_lt_one_iff
    (rate curvature : ℝ) :
    settlingContraction rate curvature < 1 ↔
      0 < rate * curvature ∧ rate * curvature < 2 := by
  rw [settlingContraction, abs_lt]
  constructor
  · rintro ⟨lower, upper⟩
    constructor <;> linarith
  · rintro ⟨positive, below⟩
    constructor <;> linarith

/-- Every nonzero scalar Euler load has exactly the intended fixed point. -/
theorem quadraticSettlingStep_fixed_iff
    (rate curvature target state : ℝ) (hload : rate * curvature ≠ 0) :
    quadraticSettlingStep rate curvature target state = state ↔
      state = target := by
  constructor
  · intro hstep
    have hzero : (rate * curvature) * (state - target) = 0 := by
      calc
        (rate * curvature) * (state - target) =
            state - quadraticSettlingStep rate curvature target state := by
          simp only [quadraticSettlingStep]
          ring
        _ = 0 := by rw [hstep]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hload)
  · rintro rfl
    simp [quadraticSettlingStep]

/-! ## Equal exposure does not imply an equal finite treatment -/

def halfRateTwoSweep : ScalarResidualSchedule :=
  { rate := 1 / 2, precision := 1, sweeps := 2 }

def fullRateOneSweep : ScalarResidualSchedule :=
  { rate := 1, precision := 1, sweeps := 1 }

/-- Equal `precision * rate * sweeps` does not preserve an Euler endpoint. -/
theorem equal_nominalExposure_not_equal_endpoint :
    halfRateTwoSweep.nominalExposure = fullRateOneSweep.nominalExposure ∧
      halfRateTwoSweep.endpoint 0 1 ≠ fullRateOneSweep.endpoint 0 1 := by
  constructor
  · norm_num [ScalarResidualSchedule.nominalExposure, halfRateTwoSweep,
      fullRateOneSweep]
  · norm_num [ScalarResidualSchedule.endpoint,
      quadraticSettlingStep, halfRateTwoSweep, fullRateOneSweep,
      Function.iterate_succ_apply']

/-- The preceding schedules have the same unique stationary target despite
their different finite endpoints. -/
theorem equal_stationary_set_not_equal_finite_treatment :
    (∀ state : ℝ,
      quadraticSettlingStep halfRateTwoSweep.rate halfRateTwoSweep.precision 0 state =
          state ↔
        quadraticSettlingStep fullRateOneSweep.rate fullRateOneSweep.precision 0 state =
          state) ∧
      halfRateTwoSweep.endpoint 0 1 ≠ fullRateOneSweep.endpoint 0 1 := by
  constructor
  · intro state
    rw [quadraticSettlingStep_fixed_iff _ _ _ _ (by norm_num [halfRateTwoSweep])]
    rw [quadraticSettlingStep_fixed_iff _ _ _ _ (by norm_num [fullRateOneSweep])]
  · exact equal_nominalExposure_not_equal_endpoint.2

/-! ## Registered Unified and staged AC fixtures -/

/-- The five registered Round-1 AC settling regimes. -/
inductive ACStage
  | ignition
  | twoStep
  | fourStep
  | fiveStep
  | eightStep
  deriving DecidableEq

/-- Exact training-update endpoint of each registered AC stage. -/
def ACStage.endUpdate : ACStage → ℕ
  | .ignition => 6333
  | .twoStep => 6750
  | .fourStep => 7167
  | .fiveStep => 9500
  | .eightStep => 10000

/-- Exact rational reconstruction of the registered floating-point stage
constants. -/
def ACStage.schedule : ACStage → ScalarResidualSchedule
  | .ignition => { rate := 3 / 10000, precision := 10000 / 3, sweeps := 1 }
  | .twoStep => { rate := 1 / 1000, precision := 500, sweeps := 2 }
  | .fourStep => { rate := 1 / 1000, precision := 250, sweeps := 4 }
  | .fiveStep => { rate := 1 / 1000, precision := 200, sweeps := 5 }
  | .eightStep => { rate := 1 / 1000, precision := 125, sweeps := 8 }

/-- Exact response expected from each AC residual-only stage. -/
def ACStage.expectedResponse : ACStage → ℝ
  | .ignition => 1
  | .twoStep => 3 / 4
  | .fourStep => 175 / 256
  | .fiveStep => 2101 / 3125
  | .eightStep => 11012415 / 16777216

theorem acStage_endUpdates_strict :
    ACStage.ignition.endUpdate < ACStage.twoStep.endUpdate ∧
      ACStage.twoStep.endUpdate < ACStage.fourStep.endUpdate ∧
      ACStage.fourStep.endUpdate < ACStage.fiveStep.endUpdate ∧
      ACStage.fiveStep.endUpdate < ACStage.eightStep.endUpdate := by
  norm_num [ACStage.endUpdate]

/-- The registration's declared exposure invariant is exact in every stage. -/
theorem ACStage.nominalExposure_eq_one (stage : ACStage) :
    stage.schedule.nominalExposure = 1 := by
  cases stage <;>
    norm_num [ACStage.schedule, ScalarResidualSchedule.nominalExposure]

/-- Exact residual-only finite response for every registered stage. -/
theorem ACStage.finiteResponse_eq_expected (stage : ACStage) :
    stage.schedule.finiteResponse = stage.expectedResponse := by
  cases stage <;>
    norm_num [ACStage.schedule, ACStage.expectedResponse,
      ScalarResidualSchedule.finiteResponse,
      ScalarResidualSchedule.residualFactor]

/-- Exact registered response values decrease strictly as the staged depth
grows, despite the invariant nominal exposure. -/
theorem acStage_expectedResponses_strictly_decrease :
    ACStage.twoStep.expectedResponse < ACStage.ignition.expectedResponse ∧
      ACStage.fourStep.expectedResponse < ACStage.twoStep.expectedResponse ∧
      ACStage.fiveStep.expectedResponse < ACStage.fourStep.expectedResponse ∧
      ACStage.eightStep.expectedResponse < ACStage.fiveStep.expectedResponse := by
  norm_num [ACStage.expectedResponse]

/-- The exact stage response transports directly to the local parameter
credit in the scalar-curvature boundary model. -/
theorem ACStage.settledCredit_eq_expected_smul_carrierBPCredit
    {CreditState : Type*}
    [NormedAddCommGroup CreditState] [InnerProductSpace ℝ CreditState]
    {Parameter : Type*} [NormedAddCommGroup Parameter]
    [NormedSpace ℝ Parameter]
    (stage : ACStage) (pullback : CreditState →ₗ[ℝ] Parameter)
    (prediction bpCredit : CreditState) :
    carrierLocalCredit pullback prediction
        (settleIterate prediction stage.schedule.precision stage.schedule.rate
          (scalarCurvatureField prediction 0 bpCredit) stage.schedule.sweeps)
        stage.schedule.precision =
      stage.expectedResponse •
        carrierBPCredit pullback
          (scalarCurvatureField prediction 0 bpCredit) prediction := by
  rw [settledCredit_eq_finiteResponse_smul_carrierBPCredit]
  rw [stage.finiteResponse_eq_expected]

/-- The exposure invariant is not a finite-credit invariant: the first and
last AC stages both have nominal exposure one but different exact responses. -/
theorem ac_exposure_invariant_not_finiteResponse_invariant :
    ACStage.ignition.schedule.nominalExposure =
        ACStage.eightStep.schedule.nominalExposure ∧
      ACStage.ignition.schedule.finiteResponse ≠
        ACStage.eightStep.schedule.finiteResponse := by
  constructor
  · rw [ACStage.nominalExposure_eq_one, ACStage.nominalExposure_eq_one]
  · rw [ACStage.finiteResponse_eq_expected, ACStage.finiteResponse_eq_expected]
    norm_num [ACStage.expectedResponse]

/-- Unified's registered residual-only schedule. -/
def unifiedSchedule : ScalarResidualSchedule :=
  { rate := 1 / 40, precision := 20, sweeps := 8 }

theorem unifiedSchedule_nominalExposure :
    unifiedSchedule.nominalExposure = 4 := by
  norm_num [unifiedSchedule, ScalarResidualSchedule.nominalExposure]

theorem unifiedSchedule_finiteResponse :
    unifiedSchedule.finiteResponse = 255 / 256 := by
  norm_num [unifiedSchedule, ScalarResidualSchedule.finiteResponse,
    ScalarResidualSchedule.residualFactor]

theorem unified_settledCredit_eq_response_smul_carrierBPCredit
    {CreditState : Type*}
    [NormedAddCommGroup CreditState] [InnerProductSpace ℝ CreditState]
    {Parameter : Type*} [NormedAddCommGroup Parameter]
    [NormedSpace ℝ Parameter]
    (pullback : CreditState →ₗ[ℝ] Parameter)
    (prediction bpCredit : CreditState) :
    carrierLocalCredit pullback prediction
        (settleIterate prediction unifiedSchedule.precision unifiedSchedule.rate
          (scalarCurvatureField prediction 0 bpCredit) unifiedSchedule.sweeps)
        unifiedSchedule.precision =
      (255 / 256 : ℝ) •
        carrierBPCredit pullback
          (scalarCurvatureField prediction 0 bpCredit) prediction := by
  rw [settledCredit_eq_finiteResponse_smul_carrierBPCredit]
  rw [unifiedSchedule_finiteResponse]

theorem unifiedSchedule_residualRemainder :
    unifiedSchedule.residualRemainder = 1 / 256 := by
  norm_num [unifiedSchedule, ScalarResidualSchedule.residualRemainder,
    ScalarResidualSchedule.residualFactor]

theorem acEightSchedule_residualRemainder :
    ACStage.eightStep.schedule.residualRemainder = 5764801 / 16777216 := by
  norm_num [ACStage.schedule, ScalarResidualSchedule.residualRemainder,
    ScalarResidualSchedule.residualFactor]

/-- In the residual-only scalar comparison, Unified's registered eight sweeps
settle much closer than AC's registered eight sweeps. -/
theorem unified_residualRemainder_lt_acEight :
    unifiedSchedule.residualRemainder <
      ACStage.eightStep.schedule.residualRemainder := by
  rw [unifiedSchedule_residualRemainder, acEightSchedule_residualRemainder]
  norm_num

/-- The same comparison transported to exact first-order finite credit. -/
theorem acEight_finiteResponse_lt_unified :
    ACStage.eightStep.schedule.finiteResponse < unifiedSchedule.finiteResponse := by
  rw [ACStage.finiteResponse_eq_expected, unifiedSchedule_finiteResponse]
  norm_num [ACStage.expectedResponse]

/-! ## The `0.05` cross-normalization counterexample -/

/-- A clock corresponding to `dt = 1`, `tau = 20`. -/
def oneTwentiethClock : EulerClock := { dt := 1, tau := 20 }

theorem oneTwentiethClock_rate : oneTwentiethClock.rate = 1 / 20 := by
  norm_num [oneTwentiethClock, EulerClock.rate]

/-- The same raw `0.05` rate annihilates a residual of curvature `20` in one
step but expands a residual of curvature `125` by `21/4`. -/
theorem oneTwentieth_stable_for_twenty_unstable_for_oneTwentyFive :
    settlingContraction oneTwentiethClock.rate 20 = 0 ∧
      settlingContraction oneTwentiethClock.rate 125 = 21 / 4 ∧
      1 < settlingContraction oneTwentiethClock.rate 125 := by
  rw [oneTwentiethClock_rate]
  norm_num [settlingContraction]

/-- Concrete catastrophic endpoint: importing the same raw rate into the AC
residual normalization maps unit error to `-21/4` in one step. -/
theorem oneTwentieth_acResidual_oneStep_expands :
    quadraticSettlingStep oneTwentiethClock.rate 125 0 1 = -(21 / 4) ∧
      |quadraticSettlingStep oneTwentiethClock.rate 125 0 1| = 21 / 4 := by
  rw [oneTwentiethClock_rate]
  norm_num [quadraticSettlingStep]

/-! ## Outer-learning-rate transport -/

section OuterUpdate

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- A plain outer parameter update driven by the finite PC credit. -/
def parameterUpdate (learningRate : ℝ) (credit parameter : Parameter) : Parameter :=
  parameter - learningRate • credit

/-- The outer learning rate scales the finite-credit difference exactly. -/
theorem parameterUpdate_sub_parameterUpdate
    (learningRate : ℝ) (leftCredit rightCredit parameter : Parameter) :
    parameterUpdate learningRate leftCredit parameter -
        parameterUpdate learningRate rightCredit parameter =
      (-learningRate) • (leftCredit - rightCredit) := by
  simp only [parameterUpdate]
  module

theorem norm_parameterUpdate_sub_parameterUpdate
    (learningRate : ℝ) (leftCredit rightCredit parameter : Parameter) :
    ‖parameterUpdate learningRate leftCredit parameter -
        parameterUpdate learningRate rightCredit parameter‖ =
      |learningRate| * ‖leftCredit - rightCredit‖ := by
  rw [parameterUpdate_sub_parameterUpdate, norm_smul, Real.norm_eq_abs, abs_neg]

/-- A nonzero outer learning rate preserves every genuine finite-credit
difference as a genuine parameter-update difference. -/
theorem parameterUpdate_ne_of_credit_ne
    (learningRate : ℝ) (leftCredit rightCredit parameter : Parameter)
    (learningRate_ne : learningRate ≠ 0)
    (credit_ne : leftCredit ≠ rightCredit) :
    parameterUpdate learningRate leftCredit parameter ≠
      parameterUpdate learningRate rightCredit parameter := by
  intro updates_eq
  have difference_zero :
      parameterUpdate learningRate leftCredit parameter -
          parameterUpdate learningRate rightCredit parameter = 0 :=
    sub_eq_zero.mpr updates_eq
  rw [parameterUpdate_sub_parameterUpdate] at difference_zero
  rcases smul_eq_zero.mp difference_zero with rate_zero | credit_difference_zero
  · exact learningRate_ne (neg_eq_zero.mp rate_zero)
  · exact credit_ne (sub_eq_zero.mp credit_difference_zero)

end OuterUpdate

/-- Consequently, the registered first and last AC stages induce different
outer updates at every nonzero scalar learning rate in the unit-credit
fixture. -/
theorem ac_first_last_parameterUpdates_differ
    (learningRate : ℝ) (learningRate_ne : learningRate ≠ 0) :
    parameterUpdate learningRate ACStage.ignition.expectedResponse 0 ≠
      parameterUpdate learningRate ACStage.eightStep.expectedResponse 0 := by
  apply parameterUpdate_ne_of_credit_ne learningRate _ _ 0 learningRate_ne
  norm_num [ACStage.expectedResponse]

/-! ## A clock-form finite-credit corollary -/

/-- The existing finite-settling credit bound expressed with a clock.  This
makes explicit that changing `dt/tau` or `sweeps` changes the finite credit
budget even when the equilibrium is unchanged. -/
theorem clockFiniteSettlingGradientGap_zeroMismatch
    (clock : EulerClock) (curvature target initial K bpGradient : ℝ)
    (gradientReadout : ℝ → ℝ) (sweeps : ℕ)
    (hLipschitz : GradientReadoutLipschitzAt gradientReadout target K)
    (hequilibrium : gradientReadout target = bpGradient) :
    |gradientReadout
          ((quadraticSettlingStep clock.rate curvature target)^[sweeps] initial) -
        bpGradient| ≤
      K * settlingContraction clock.rate curvature ^ sweeps *
        |initial - target| := by
  exact finiteSettlingGradientGap_zeroMismatch clock.rate curvature target
    initial K bpGradient gradientReadout sweeps hLipschitz hequilibrium

#print axioms eulerIterate_eq_of_rate_eq
#print axioms EulerClock.rate_scale_both
#print axioms preconditioned_massWeightedResidualGradient
#print axioms nondimensionalPreconditionedLocalCertificate
#print axioms ScalarResidualSchedule.finiteResponse_eq_creditScale
#print axioms settledCredit_eq_finiteResponse_smul_carrierBPCredit
#print axioms settlingContraction_lt_one_iff
#print axioms quadraticSettlingStep_fixed_iff
#print axioms equal_nominalExposure_not_equal_endpoint
#print axioms equal_stationary_set_not_equal_finite_treatment
#print axioms ACStage.nominalExposure_eq_one
#print axioms ACStage.finiteResponse_eq_expected
#print axioms acStage_expectedResponses_strictly_decrease
#print axioms ACStage.settledCredit_eq_expected_smul_carrierBPCredit
#print axioms ac_exposure_invariant_not_finiteResponse_invariant
#print axioms unifiedSchedule_finiteResponse
#print axioms unified_settledCredit_eq_response_smul_carrierBPCredit
#print axioms unified_residualRemainder_lt_acEight
#print axioms acEight_finiteResponse_lt_unified
#print axioms oneTwentieth_stable_for_twenty_unstable_for_oneTwentyFive
#print axioms oneTwentieth_acResidual_oneStep_expands
#print axioms norm_parameterUpdate_sub_parameterUpdate
#print axioms parameterUpdate_ne_of_credit_ne
#print axioms ac_first_last_parameterUpdates_differ
#print axioms clockFiniteSettlingGradientGap_zeroMismatch

end

end NondimensionalSettlingSchedule

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
