import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.Regime

/-!
# Error-coordinate rescue and its exact boundary

The nonlinear ePC state/error maps are exact inverses, preserve the pulled-back
energy, preserve critical points under an invertible Jacobian, and give the
same local weight update at corresponding states.  Those facts are imported
from `ErrorStateReparameterization` and restated here as the positive result.

They do **not** imply that ordinary Euclidean gradient flows are conjugate.
A non-orthogonal coordinate map changes a Euclidean gradient by a metric
factor.  The two-dimensional shear below is the smallest explicit
counterexample: energies and equilibria correspond exactly, while the
pushforward of error-coordinate gradient flow differs from state-coordinate
gradient flow by the positive-definite `J Jᵀ` preconditioner.  This is the
mathematical boundary reported in Appendix C of the ePC analysis, where the
trajectories are explicitly allowed to differ.

All numerical underflow and finite-precision behavior remains a reproduction
target rather than a proposition about real arithmetic.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Exact nonlinear ePC coordinate laws -/

/-- Frontier lift of the exact error-after-state inverse law. -/
theorem epc_error_after_state_exact
    (layer : ℕ → ℝ → ℝ) (input : ℝ) (error : ℕ → ℝ) :
    spcErrorStream layer (epcStateStream layer input error) = error :=
  spcErrorStream_epcStateStream layer input error

/-- Frontier lift of the exact state-after-error inverse law. -/
theorem epc_state_after_error_exact
    (layer : ℕ → ℝ → ℝ) (input : ℝ) (state : ℕ → ℝ)
    (hinput : state 0 = input) :
    epcStateStream layer input (spcErrorStream layer state) = state :=
  epcStateStream_spcErrorStream layer input state hinput

/-- Frontier lift of exact energy transport under the nonlinear coordinates. -/
theorem epc_energy_transport_exact
    (depth : ℕ) (layer : ℕ → ℝ → ℝ) (input : ℝ)
    (error : ℕ → ℝ) (terminalLoss : ℝ → ℝ) :
    epcPrefixEnergy depth layer input error terminalLoss =
      spcPrefixEnergy depth layer (epcStateStream layer input error)
        terminalLoss :=
  epcPrefixEnergy_eq_spcPrefixEnergy depth layer input error terminalLoss

/-- Frontier lift: corresponding state/error residuals give identical local
parameter updates at every layer, without a linearity assumption. -/
theorem epc_weight_update_transport_exact
    (layer : ℕ → ℝ → ℝ) (input : ℝ) (error : ℕ → ℝ)
    (predictionJacobian : ℕ → ℝ) (index : ℕ) :
    pcLocalParameterUpdate (predictionJacobian index) (error index) =
      pcLocalParameterUpdate (predictionJacobian index)
        (spcErrorStream layer (epcStateStream layer input error) index) :=
  epcLocalParameterUpdate_eq_spcLocalParameterUpdate
    layer input error predictionJacobian index

/-- Frontier lift of the exact critical-differential equivalence.  The right
inverse hypothesis is the finite-dimensional statement that the coordinate
Jacobian is invertible in the direction needed to reflect criticality. -/
theorem epc_critical_differential_equivalence
    {State Error : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Error] [NormedSpace ℝ Error]
    (spcDifferential : State →L[ℝ] ℝ)
    (jacobian : Error →L[ℝ] State)
    (inverseJacobian : State →L[ℝ] Error)
    (hright : jacobian ∘L inverseJacobian =
      ContinuousLinearMap.id ℝ State) :
    spcDifferential ∘L jacobian = 0 ↔ spcDifferential = 0 :=
  epcCriticalDifferential_iff_spcCriticalDifferential
    spcDifferential jacobian inverseJacobian hright

/-! ## An exact non-conjugacy witness -/

/-- A non-orthogonal error-to-state shear. -/
def shearToState (error : ℝ × ℝ) : ℝ × ℝ :=
  (error.1, error.1 + error.2)

/-- Exact inverse of `shearToState`. -/
def shearToError (state : ℝ × ℝ) : ℝ × ℝ :=
  (state.1, state.2 - state.1)

@[simp] theorem shearToError_shearToState (error : ℝ × ℝ) :
    shearToError (shearToState error) = error := by
  rcases error with ⟨error₁, error₂⟩
  simp [shearToError, shearToState]

@[simp] theorem shearToState_shearToError (state : ℝ × ℝ) :
    shearToState (shearToError state) = state := by
  rcases state with ⟨state₁, state₂⟩
  simp [shearToError, shearToState]

/-- State-coordinate energy whose residual coordinates are the shear errors. -/
noncomputable def shearStateEnergy (state : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * (state.1 ^ 2 + (state.2 - state.1) ^ 2)

/-- The pulled-back energy in error coordinates. -/
noncomputable def shearErrorEnergy (error : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * (error.1 ^ 2 + error.2 ^ 2)

/-- The shear preserves the energy exactly. -/
theorem shear_energy_transport_exact (error : ℝ × ℝ) :
    shearStateEnergy (shearToState error) = shearErrorEnergy error := by
  rcases error with ⟨error₁, error₂⟩
  simp [shearStateEnergy, shearErrorEnergy, shearToState]

/-- Negative state-energy gradient in ordinary Euclidean state coordinates. -/
def shearStateGradientFlow (state : ℝ × ℝ) : ℝ × ℝ :=
  (state.2 - 2 * state.1, state.1 - state.2)

/-- Negative error-energy gradient in ordinary Euclidean error coordinates. -/
def shearErrorGradientFlow (error : ℝ × ℝ) : ℝ × ℝ :=
  (-error.1, -error.2)

/-- Exact first-coordinate energy increment.  Its linear coefficient is the
negative of the first flow component, so the formula certifies the stated
Euclidean gradient without relying on an unexpanded derivative oracle. -/
theorem shearStateEnergy_first_increment_exact
    (state₁ state₂ increment : ℝ) :
    shearStateEnergy (state₁ + increment, state₂) -
        shearStateEnergy (state₁, state₂) =
      increment * (-(shearStateGradientFlow (state₁, state₂)).1) +
        increment ^ 2 := by
  simp [shearStateEnergy, shearStateGradientFlow]
  ring

/-- Exact second-coordinate energy increment.  Its linear coefficient is the
negative of the second flow component. -/
theorem shearStateEnergy_second_increment_exact
    (state₁ state₂ increment : ℝ) :
    shearStateEnergy (state₁, state₂ + increment) -
        shearStateEnergy (state₁, state₂) =
      increment * (-(shearStateGradientFlow (state₁, state₂)).2) +
        (1 / 2 : ℝ) * increment ^ 2 := by
  simp [shearStateEnergy, shearStateGradientFlow]
  ring

/-- Differential of the linear shear applied to a tangent vector. -/
def shearPushforward (velocity : ℝ × ℝ) : ℝ × ℝ :=
  (velocity.1, velocity.1 + velocity.2)

/-- Action of `J Jᵀ` for the shear Jacobian
`J = [[1,0],[1,1]]`. -/
def shearJJtApply (velocity : ℝ × ℝ) : ℝ × ℝ :=
  (velocity.1 + velocity.2, velocity.1 + 2 * velocity.2)

/-- The shear preconditioner is positive definite.  Its quadratic form is
`(v₁+v₂)²+v₂²`, which is strictly positive away from zero. -/
theorem shearJJtApply_quadratic_pos
    (velocity : ℝ × ℝ) (hvelocity : velocity ≠ (0, 0)) :
    0 < velocity.1 * (shearJJtApply velocity).1 +
      velocity.2 * (shearJJtApply velocity).2 := by
  rcases velocity with ⟨velocity₁, velocity₂⟩
  simp only [shearJJtApply]
  rw [show
    velocity₁ * (velocity₁ + velocity₂) +
        velocity₂ * (velocity₁ + 2 * velocity₂) =
      (velocity₁ + velocity₂) ^ 2 + velocity₂ ^ 2 by ring]
  by_cases h₂ : velocity₂ = 0
  · have h₁ : velocity₁ ≠ 0 := by
      intro h₁
      apply hvelocity
      simp [h₁, h₂]
    simp [h₂, sq_pos_of_ne_zero h₁]
  · nlinarith [sq_nonneg (velocity₁ + velocity₂), sq_pos_of_ne_zero h₂]

/-- Exact ePC Appendix-C relation for the shear: pushing the Euclidean error
flow into state coordinates gives the `J Jᵀ`-preconditioned state flow.  This
is the correct replacement for the false unpreconditioned conjugacy claim. -/
theorem shear_error_flow_pushforward_eq_preconditioned_state_flow
    (error : ℝ × ℝ) :
    shearPushforward (shearErrorGradientFlow error) =
      shearJJtApply (shearStateGradientFlow (shearToState error)) := by
  rcases error with ⟨error₁, error₂⟩
  ext <;>
    simp [shearPushforward, shearErrorGradientFlow, shearJJtApply,
      shearStateGradientFlow, shearToState] <;>
    ring

/-- Both Euclidean flows have exactly the origin as equilibrium. -/
theorem shear_error_equilibrium_iff (error : ℝ × ℝ) :
    shearErrorGradientFlow error = (0, 0) ↔ error = (0, 0) := by
  rcases error with ⟨error₁, error₂⟩
  simp [shearErrorGradientFlow]

theorem shear_state_equilibrium_iff (state : ℝ × ℝ) :
    shearStateGradientFlow state = (0, 0) ↔ state = (0, 0) := by
  rcases state with ⟨state₁, state₂⟩
  simp only [shearStateGradientFlow, Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- Equilibria correspond exactly under the shear. -/
theorem shear_equilibria_correspond (error : ℝ × ℝ) :
    shearErrorGradientFlow error = (0, 0) ↔
      shearStateGradientFlow (shearToState error) = (0, 0) := by
  rw [shear_error_equilibrium_iff, shear_state_equilibrium_iff]
  rcases error with ⟨error₁, error₂⟩
  simp only [shearToState, Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith

/-- Concrete refutation of Euclidean-flow conjugacy.  At `(1,0)`, pushing the
error flow through the coordinate Jacobian gives `(-1,-1)`, while the state
Euclidean gradient flow at the corresponding state is `(-1,0)`. -/
theorem shear_euclidean_gradient_flows_not_conjugate :
    shearPushforward (shearErrorGradientFlow (1, 0)) ≠
      shearStateGradientFlow (shearToState (1, 0)) := by
  norm_num [shearPushforward, shearErrorGradientFlow,
    shearStateGradientFlow, shearToState]

/-! ## Depth signal and numerical boundary -/

/-- Exact absolute-value attenuation formula for state-coordinate wavefronts. -/
theorem state_wavefront_attenuation_bound
    (learningRate outputGradient : ℝ) (distance : ℕ) :
    |spcWavefrontSignal learningRate outputGradient distance| ≤
      |learningRate| ^ distance * |outputGradient| := by
  rw [spcWavefrontSignal_closedForm, abs_mul, abs_pow]

/-- In the stable state-coordinate regime, the exact recurrence eventually
falls below every positive detection tolerance.  This is the scoped
exponential-decay consequence of the preceding closed form. -/
theorem state_wavefront_eventually_below_tolerance
    (learningRate outputGradient tolerance : ℝ)
    (hstable : |learningRate| < 1) (htolerance : 0 < tolerance) :
    ∃ distance,
      BelowDetectionTolerance tolerance
        (spcWavefrontSignal learningRate outputGradient distance) :=
  spcWavefront_eventually_below_tolerance
    learningRate outputGradient tolerance hstable htolerance

/-- An ePC first step has no depth recurrence: adding any nominal depth leaves
the explicitly represented output error unchanged. -/
theorem error_coordinate_first_step_depth_invariant
    (learningRate lossGradient : ℝ) (depth₁ depth₂ : ℕ) :
    (fun _depth : ℕ => epcOneStepError learningRate lossGradient) depth₁ =
      (fun _depth : ℕ => epcOneStepError learningRate lossGradient) depth₂ := by
  rfl

/-- Status labels for statements outside real-arithmetic formalization. -/
inductive NumericalClaimStatus
  | exactRealTheorem
  | floatingPointReproductionTarget
  deriving DecidableEq, Repr

/-- Machine-readable boundary record; its prose is data, not a hidden theorem. -/
structure NumericalBoundaryClaim where
  description : String
  status : NumericalClaimStatus
  deriving DecidableEq, Repr

/-- Underflow and implementation-speed claims require a pinned floating-point
reproduction and are not propositions about the exact real model. -/
def epcFloatingPointBoundary : NumericalBoundaryClaim where
  description := "state-coordinate underflow and ePC implementation speed"
  status := .floatingPointReproductionTarget

/-- Positive status fixture. -/
theorem epcFloatingPointBoundary_is_reproduction_target :
    epcFloatingPointBoundary.status = .floatingPointReproductionTarget := by
  rfl

/-- Negative status fixture: finite-precision underflow is not promoted to an
exact-real theorem. -/
theorem epcFloatingPointBoundary_not_exactReal :
    epcFloatingPointBoundary.status ≠ .exactRealTheorem := by
  decide

#print axioms epc_critical_differential_equivalence
#print axioms shear_error_flow_pushforward_eq_preconditioned_state_flow
#print axioms shear_euclidean_gradient_flows_not_conjugate
#print axioms state_wavefront_eventually_below_tolerance

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
