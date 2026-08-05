import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.CoupledDynamics

/-!
# Discrete prediction-step stability

Frieder and Lukasiewicz, *Non-Convergence Results for Predictive Coding
Networks* (2022), Equation (5), treat predictive-coding inference as a
discrete dynamical system.  At zero weights their prediction map reduces to
scalar relaxation by `1 - step`, so the open stability interval is
`0 < step < 2`.  The endpoint `step = 2` is a genuine period-two boundary,
not convergence inherited from the corresponding continuous gradient flow.

This file records the exact source map for the paper's two-node example,
proves its zero-weight reduction, and develops the resulting stability theory
for an arbitrary real normed vector space.  It includes convergence inside
the sharp interval, a nonconvergent period-two endpoint, and norm divergence
above the interval.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Filter Topology

/-- Equation (5) of Frieder--Lukasiewicz for the two non-input nodes.  The
activation derivative is supplied separately so that the discrete map itself
does not hide a differentiability oracle. -/
noncomputable def twoNodePredictionStep
    (activation activationDerivative : ℝ → ℝ)
    (input firstWeight secondWeight step : ℝ) :
    ℝ × ℝ → ℝ × ℝ :=
  fun state =>
    (state.1 -
        step *
          (state.1 - firstWeight * activation input -
            activationDerivative state.1 * secondWeight *
              (state.2 - secondWeight * activation state.1)),
      state.2 -
        step * (state.2 - secondWeight * activation state.1))

/-- Isotropic explicit relaxation around zero. -/
noncomputable def predictionRelaxationStep
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (step : ℝ) (state : State) : State :=
  (1 - step) • state

/-- Exact source recovery: setting both weights to zero in the two-node PCN
map gives isotropic relaxation, independently of the activation and input. -/
theorem twoNodePredictionStep_zeroWeights
    (activation activationDerivative : ℝ → ℝ)
    (input step : ℝ) (state : ℝ × ℝ) :
    twoNodePredictionStep activation activationDerivative
        input 0 0 step state =
      predictionRelaxationStep step state := by
  ext <;>
    simp [twoNodePredictionStep, predictionRelaxationStep] <;>
    ring

variable {State : Type*}
  [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Exact finite trajectory of the zero-weight prediction map. -/
theorem predictionRelaxationStep_iterate
    (step : ℝ) (state : State) (iterations : ℕ) :
    Nat.iterate (predictionRelaxationStep step) iterations state =
      (1 - step) ^ iterations • state := by
  induction iterations with
  | zero =>
      simp
  | succ iterations inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis]
      simp only [predictionRelaxationStep, smul_smul, pow_succ]
      congr 1
      ring

/-- Exact norm trajectory. -/
theorem norm_predictionRelaxationStep_iterate
    (step : ℝ) (state : State) (iterations : ℕ) :
    ‖Nat.iterate (predictionRelaxationStep step) iterations state‖ =
      |1 - step| ^ iterations * ‖state‖ := by
  rw [predictionRelaxationStep_iterate, norm_smul, Real.norm_eq_abs,
    abs_pow]

/-- The source's open interval is sufficient for convergence from every
initial state. -/
theorem predictionRelaxation_converges_of_step_mem_openInterval
    (step : ℝ) (state : State)
    (positive : 0 < step) (belowTwo : step < 2) :
    Tendsto
      (fun iterations =>
        Nat.iterate (predictionRelaxationStep step) iterations state)
      atTop (nhds 0) := by
  have multiplierConverges :
      Tendsto (fun iterations : ℕ => (1 - step) ^ iterations)
        atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      ((abs_one_sub_lt_one_iff step).2 ⟨positive, belowTwo⟩)
  simpa only [predictionRelaxationStep_iterate, zero_smul] using
    multiplierConverges.smul_const state

/-- At the upper endpoint, one relaxation step negates the state. -/
theorem predictionRelaxationStep_two
    (state : State) :
    predictionRelaxationStep 2 state = -state := by
  rw [predictionRelaxationStep]
  norm_num

/-- The upper endpoint has an exact period dividing two. -/
theorem predictionRelaxationStep_two_twoCycle
    (state : State) :
    Nat.iterate (predictionRelaxationStep 2) 2 state = state := by
  rw [predictionRelaxationStep_iterate]
  norm_num

/-- Every endpoint iterate preserves the initial norm. -/
theorem norm_predictionRelaxationStep_two_iterate
    (state : State) (iterations : ℕ) :
    ‖Nat.iterate (predictionRelaxationStep 2) iterations state‖ =
      ‖state‖ := by
  rw [norm_predictionRelaxationStep_iterate]
  norm_num

/-- A nonzero period-two orbit cannot converge to the fixed point. -/
theorem predictionRelaxationStep_two_not_tendsto_zero
    (state : State) (stateNonzero : state ≠ 0) :
    ¬ Tendsto
      (fun iterations =>
        Nat.iterate (predictionRelaxationStep 2) iterations state)
      atTop (nhds 0) := by
  intro trajectoryConverges
  have normConverges :
      Tendsto
        (fun iterations =>
          ‖Nat.iterate (predictionRelaxationStep 2) iterations state‖)
        atTop (nhds 0) := by
    simpa using trajectoryConverges.norm
  have constantNormConverges :
      Tendsto (fun _ : ℕ => ‖state‖) atTop (nhds ‖state‖) :=
    tendsto_const_nhds
  have constantNormConvergesToZero :
      Tendsto (fun _ : ℕ => ‖state‖) atTop (nhds 0) := by
    simpa only [norm_predictionRelaxationStep_two_iterate] using normConverges
  have normZero : ‖state‖ = 0 :=
    tendsto_nhds_unique constantNormConverges constantNormConvergesToZero
  exact stateNonzero (norm_eq_zero.mp normZero)

/-- Above the upper endpoint, every nonzero initial state's norm diverges. -/
theorem predictionRelaxation_diverges_of_two_lt_step
    (step : ℝ) (state : State)
    (aboveTwo : 2 < step) (stateNonzero : state ≠ 0) :
    Tendsto
      (fun iterations =>
        ‖Nat.iterate (predictionRelaxationStep step) iterations state‖)
      atTop atTop := by
  have multiplierAboveOne : 1 < |1 - step| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have powerDiverges :
      Tendsto (fun iterations : ℕ => |1 - step| ^ iterations)
        atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt multiplierAboveOne
  have normPositive : 0 < ‖state‖ :=
    norm_pos_iff.mpr stateNonzero
  simpa only [norm_predictionRelaxationStep_iterate] using
    powerDiverges.atTop_mul_const normPositive

/-! ## Source-level positive and negative fixtures -/

theorem zeroWeight_halfStep_prediction_converges
    (activation activationDerivative : ℝ → ℝ) (input : ℝ)
    (state : ℝ × ℝ) :
    Tendsto
      (fun iterations =>
        Nat.iterate
          (twoNodePredictionStep activation activationDerivative
            input 0 0 (1 / 2))
          iterations state)
      atTop (nhds 0) := by
  have stepEquality :
      twoNodePredictionStep activation activationDerivative
          input 0 0 (1 / 2) =
        predictionRelaxationStep (1 / 2) := by
    funext current
    exact twoNodePredictionStep_zeroWeights
      activation activationDerivative input (1 / 2) current
  rw [stepEquality]
  exact predictionRelaxation_converges_of_step_mem_openInterval
    (1 / 2) state (by norm_num) (by norm_num)

theorem zeroWeight_stepTwo_prediction_not_convergent :
    ¬ Tendsto
      (fun iterations =>
        Nat.iterate
          (twoNodePredictionStep (fun value => value ^ 2)
            (fun value => 2 * value) 1 0 0 2)
          iterations (1, 0))
      atTop (nhds 0) := by
  have stepEquality :
      twoNodePredictionStep (fun value => value ^ 2)
          (fun value => 2 * value) 1 0 0 2 =
        predictionRelaxationStep 2 := by
    funext current
    exact twoNodePredictionStep_zeroWeights
      (fun value => value ^ 2) (fun value => 2 * value) 1 2 current
  rw [stepEquality]
  exact predictionRelaxationStep_two_not_tendsto_zero
    (1, 0) (by norm_num)

#print axioms twoNodePredictionStep_zeroWeights
#print axioms predictionRelaxationStep_iterate
#print axioms predictionRelaxation_converges_of_step_mem_openInterval
#print axioms predictionRelaxationStep_two_twoCycle
#print axioms predictionRelaxationStep_two_not_tendsto_zero
#print axioms predictionRelaxation_diverges_of_two_lt_step
#print axioms zeroWeight_halfStep_prediction_converges
#print axioms zeroWeight_stepTwo_prediction_not_convergent

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
