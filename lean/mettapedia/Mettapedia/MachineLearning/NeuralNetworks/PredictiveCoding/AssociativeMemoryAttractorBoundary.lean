import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Predictive-coding associative memory: the attractor boundary

Salvatori et al., *Associative Memories via Predictive Coding* (2021),
Equations (1)--(5) and Section 3, use the nonnegative sum of squared
prediction errors as the generative-PC energy.  The source then describes a
zero-energy trained pattern as an attractor of inference and repeatedly
applies the reconstruction map to a corrupted cue.

This file separates the exact algebraic conclusion from the additional
dynamical hypotheses:

* zero prediction errors give a global energy minimum;
* a zero-energy sensory residual makes the stored pattern a fixed point of
  the reconstruction map;
* contraction promotes that fixed point to a unique attracting memory, with
  an explicit finite retrieval bound;
* an approximately stored pattern has a geometric cue term plus a finite
  residual floor;
* zero energy alone does not imply attraction, and even a strict quadratic
  minimum fails to attract under the critical period-two inference step.

The positive theorem is global because it assumes a global contraction.
Local basins require a separately certified invariant region and local
contraction.  No empirical storage capacity or image-retrieval result is
inferred here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

namespace AssociativeMemoryAttractorBoundary

open Filter
open scoped Topology
open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
open AmortizedInitialization

noncomputable section

/-! ## Source energy and exact storage -/

/-- The source's global prediction-error energy at one network state. -/
def generativePCEnergy {ErrorSite : Type*} [Fintype ErrorSite]
    (predictionError : ErrorSite → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ site, (predictionError site) ^ 2

theorem generativePCEnergy_nonnegative
    {ErrorSite : Type*} [Fintype ErrorSite]
    (predictionError : ErrorSite → ℝ) :
    0 ≤ generativePCEnergy predictionError := by
  unfold generativePCEnergy
  positivity

/-- The sum-of-squares energy is zero exactly when every prediction error is
zero. -/
theorem generativePCEnergy_eq_zero_iff
    {ErrorSite : Type*} [Fintype ErrorSite]
    (predictionError : ErrorSite → ℝ) :
    generativePCEnergy predictionError = 0 ↔
      ∀ site, predictionError site = 0 := by
  constructor
  · intro energyZero site
    have sumZero : ∑ index, (predictionError index) ^ 2 = 0 := by
      unfold generativePCEnergy at energyZero
      linarith
    have siteBound :
        (predictionError site) ^ 2 ≤
          ∑ index, (predictionError index) ^ 2 := by
      exact Finset.single_le_sum
        (fun index _ ↦ sq_nonneg (predictionError index))
        (Finset.mem_univ site)
    rw [sumZero] at siteBound
    nlinarith [sq_nonneg (predictionError site)]
  · intro errorsZero
    simp [generativePCEnergy, errorsZero]

/-- A state with zero prediction error is a global energy minimizer. -/
theorem zero_errors_global_minimum
    {State ErrorSite : Type*} [Fintype ErrorSite]
    (predictionError : State → ErrorSite → ℝ)
    (stored : State)
    (storedErrorsZero : ∀ site, predictionError stored site = 0) :
    ∀ state,
      generativePCEnergy (predictionError stored) ≤
        generativePCEnergy (predictionError state) := by
  intro state
  rw [(generativePCEnergy_eq_zero_iff
    (predictionError stored)).2 storedErrorsZero]
  exact generativePCEnergy_nonnegative _

/-- If the sensory prediction error is `stored - reconstruction stored`, then
zero sensory error makes the stored pattern a fixed point. -/
theorem zero_sensory_error_is_fixed
    {State : Type*} [AddGroup State]
    (reconstruction : State → State) (stored : State)
    (sensoryErrorZero : stored - reconstruction stored = 0) :
    IsFixedPoint reconstruction stored := by
  unfold IsFixedPoint
  exact (sub_eq_zero.mp sensoryErrorZero).symm

/-! ## Approximate storage under contractive retrieval -/

/-- Finite retrieval from an approximately stored pattern.  The first term is
the corrupted-cue error.  The second is the exact geometric accumulation of
the pattern's one-step reconstruction residual. -/
theorem approximateStored_iterate_le
    {State : Type*} [NormedAddCommGroup State]
    {reconstruction : State → State}
    (certificate : ContractionCertificate reconstruction)
    (stored cue : State) (storageResidual : ℝ)
    (storedApproximately :
      ‖reconstruction stored - stored‖ ≤ storageResidual) :
    ∀ steps,
      ‖reconstruction^[steps] cue - stored‖ ≤
        certificate.factor ^ steps * ‖cue - stored‖ +
          storageResidual *
            (1 - certificate.factor ^ steps) /
              (1 - certificate.factor) := by
  intro steps
  induction steps with
  | zero =>
      simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      have triangle :
          ‖reconstruction (reconstruction^[steps] cue) - stored‖ ≤
            ‖reconstruction (reconstruction^[steps] cue) -
                reconstruction stored‖ +
              ‖reconstruction stored - stored‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le
            (reconstruction (reconstruction^[steps] cue) -
              reconstruction stored)
            (reconstruction stored - stored)
      have contracted :
          ‖reconstruction (reconstruction^[steps] cue) -
              reconstruction stored‖ ≤
            certificate.factor *
              ‖reconstruction^[steps] cue - stored‖ :=
        certificate.contracts _ _
      have scaledInduction :
          certificate.factor *
              ‖reconstruction^[steps] cue - stored‖ ≤
            certificate.factor *
              (certificate.factor ^ steps * ‖cue - stored‖ +
                storageResidual *
                  (1 - certificate.factor ^ steps) /
                    (1 - certificate.factor)) :=
        mul_le_mul_of_nonneg_left inductionHypothesis
          certificate.factor_nonneg
      calc
        ‖reconstruction (reconstruction^[steps] cue) - stored‖ ≤
            ‖reconstruction (reconstruction^[steps] cue) -
                reconstruction stored‖ +
              ‖reconstruction stored - stored‖ := triangle
        _ ≤ certificate.factor *
              ‖reconstruction^[steps] cue - stored‖ +
            storageResidual :=
          add_le_add contracted storedApproximately
        _ ≤ certificate.factor *
              (certificate.factor ^ steps * ‖cue - stored‖ +
                storageResidual *
                  (1 - certificate.factor ^ steps) /
                    (1 - certificate.factor)) +
            storageResidual :=
          by
            simpa [add_comm] using
              add_le_add_right scaledInduction storageResidual
        _ = certificate.factor ^ steps.succ * ‖cue - stored‖ +
              storageResidual *
                (1 - certificate.factor ^ steps.succ) /
                  (1 - certificate.factor) := by
          have factor_ne_one : certificate.factor ≠ 1 :=
            ne_of_lt certificate.factor_lt_one
          rw [pow_succ]
          field_simp [factor_ne_one]
          ring

/-- Exact storage removes the residual floor and recovers geometric cue
suppression. -/
theorem exactStored_iterate_le
    {State : Type*} [NormedAddCommGroup State]
    {reconstruction : State → State}
    (certificate : ContractionCertificate reconstruction)
    (stored cue : State)
    (storedFixed : IsFixedPoint reconstruction stored)
    (steps : ℕ) :
    ‖reconstruction^[steps] cue - stored‖ ≤
      certificate.factor ^ steps * ‖cue - stored‖ := by
  exact iterate_initializer_to_fixedPoint_le
    certificate stored cue storedFixed steps

/-- A contractive reconstruction with an exactly stored pattern retrieves that
pattern from every cue. -/
theorem exactStored_tendsto
    {State : Type*} [NormedAddCommGroup State]
    {reconstruction : State → State}
    (certificate : ContractionCertificate reconstruction)
    (stored cue : State)
    (storedFixed : IsFixedPoint reconstruction stored) :
    Tendsto (fun steps ↦ reconstruction^[steps] cue) atTop (𝓝 stored) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
  · exact fun _ ↦ norm_nonneg _
  · exact fun steps ↦
      exactStored_iterate_le certificate stored cue storedFixed steps
  · have factorAbs :
        |certificate.factor| < 1 := by
      rw [abs_of_nonneg certificate.factor_nonneg]
      exact certificate.factor_lt_one
    have factorPower :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one factorAbs
    simpa using factorPower.mul_const ‖cue - stored‖

/-- Under contraction, an exactly stored pattern is the only fixed memory. -/
theorem exactStored_unique
    {State : Type*} [NormedAddCommGroup State]
    {reconstruction : State → State}
    (certificate : ContractionCertificate reconstruction)
    {stored other : State}
    (storedFixed : IsFixedPoint reconstruction stored)
    (otherFixed : IsFixedPoint reconstruction other) :
    other = stored :=
  fixedPoint_unique certificate otherFixed storedFixed

/-! ## Boundaries: minima are not automatically attractors -/

/-- A completely flat one-site PC error field. -/
def flatPredictionError (_state : ℝ) (_site : Fin 1) : ℝ := 0

theorem flatPredictionEnergy_zero (state : ℝ) :
    generativePCEnergy (flatPredictionError state) = 0 := by
  simp [generativePCEnergy, flatPredictionError]

/-- Flat zero energy at every state does not make a chosen stored state an
attractor: identity retrieval leaves a distinct cue unchanged forever. -/
theorem zero_energy_does_not_imply_attraction :
    (∀ state : ℝ,
      generativePCEnergy (flatPredictionError 0) ≤
        generativePCEnergy (flatPredictionError state)) ∧
    ¬Tendsto (fun steps ↦ (id^[steps]) (1 : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro state
    simp [flatPredictionEnergy_zero]
  · intro convergesToZero
    have convergesToOne :
        Tendsto (fun steps ↦ (id^[steps]) (1 : ℝ)) atTop (𝓝 1) := by
      simp
    have : (1 : ℝ) = 0 :=
      tendsto_nhds_unique convergesToOne convergesToZero
    norm_num at this

/-- Scalar strict quadratic energy, the simplest local PC energy near an
isolated trained pattern. -/
def scalarQuadraticEnergy (state : ℝ) : ℝ := state ^ 2 / 2

/-- Gradient step on the scalar quadratic. -/
def scalarQuadraticInferenceStep (rate state : ℝ) : ℝ :=
  (1 - rate) * state

theorem scalarQuadratic_zero_strict_minimum
    {state : ℝ} (state_ne_zero : state ≠ 0) :
    scalarQuadraticEnergy 0 < scalarQuadraticEnergy state := by
  unfold scalarQuadraticEnergy
  have squarePositive : 0 < state ^ 2 := sq_pos_of_ne_zero state_ne_zero
  nlinarith

theorem scalarQuadraticInferenceStep_two
    (state : ℝ) :
    scalarQuadraticInferenceStep 2 state = -state := by
  unfold scalarQuadraticInferenceStep
  ring

theorem scalarQuadratic_rate_two_preserves_energy
    (state : ℝ) :
    scalarQuadraticEnergy (scalarQuadraticInferenceStep 2 state) =
      scalarQuadraticEnergy state := by
  unfold scalarQuadraticEnergy scalarQuadraticInferenceStep
  ring

theorem scalarQuadraticInferenceStep_iterate
    (rate state : ℝ) (steps : ℕ) :
    (scalarQuadraticInferenceStep rate)^[steps] state =
      (1 - rate) ^ steps * state := by
  induction steps with
  | zero =>
      simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis]
      unfold scalarQuadraticInferenceStep
      rw [pow_succ]
      ring

/-- Even an isolated strict global minimum is not an attractor when the
inference step is at the critical period-two boundary. -/
theorem strict_minimum_does_not_imply_attraction_at_rate_two :
    ¬Tendsto
      (fun steps ↦ (scalarQuadraticInferenceStep 2)^[steps] (1 : ℝ))
      atTop (𝓝 0) := by
  intro convergesToZero
  have evenSubsequence :
      ∀ steps,
        (scalarQuadraticInferenceStep 2)^[2 * steps] (1 : ℝ) = 1 := by
    intro steps
    rw [scalarQuadraticInferenceStep_iterate]
    norm_num [pow_mul]
  have evenIndicesTendsto :
      Tendsto (fun steps : ℕ ↦ 2 * steps) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro bound
    filter_upwards [Filter.eventually_ge_atTop bound] with step step_ge
    omega
  have convergesEvenToZero :
      Tendsto
        (fun steps ↦
          (scalarQuadraticInferenceStep 2)^[2 * steps] (1 : ℝ))
        atTop (𝓝 0) := by
    exact convergesToZero.comp evenIndicesTendsto
  have convergesEvenToOne :
      Tendsto
        (fun steps ↦
          (scalarQuadraticInferenceStep 2)^[2 * steps] (1 : ℝ))
        atTop (𝓝 1) := by
    simp [evenSubsequence]
  have : (1 : ℝ) = 0 :=
    tendsto_nhds_unique convergesEvenToOne convergesEvenToZero
  norm_num at this

#print axioms generativePCEnergy_eq_zero_iff
#print axioms zero_errors_global_minimum
#print axioms zero_sensory_error_is_fixed
#print axioms approximateStored_iterate_le
#print axioms exactStored_tendsto
#print axioms exactStored_unique
#print axioms zero_energy_does_not_imply_attraction
#print axioms strict_minimum_does_not_imply_attraction_at_rate_two

end

end AssociativeMemoryAttractorBoundary

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
