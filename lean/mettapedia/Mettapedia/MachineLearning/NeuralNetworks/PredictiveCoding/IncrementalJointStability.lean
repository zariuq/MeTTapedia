import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.Predictive
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.PredictionStepStability

/-!
# Simultaneous state--parameter stability for incremental predictive coding

Salvatori et al., *Incremental Predictive Coding: A Parallel and Fully
Automatic Learning Algorithm* (ICLR 2024), Algorithm 1 and Equations (6)--(7),
update latent states and parameters at every time step from the same
pre-update snapshot.  This file isolates that synchronous joint-update
semantics and studies a nontrivial coupled quadratic free energy.

The quadratic has two exact modes.  Its common mode is multiplied by
`1 - rate`, while its disagreement mode is multiplied by `1 - 3 * rate`.
Consequently the sharp open stability interval for a common state/parameter
rate is `0 < rate < 2 / 3`.  At `rate = 2 / 3` the disagreement mode has a
period-two orbit, and above that boundary every nonzero disagreement diverges.

The distinction between synchronous and sequential scheduling is explicit.
The existing scalar credit-transport fixture performs a latent update before
reading the parameter gradient; the source equations instead read both
gradients from one snapshot.  A concrete counterexample prevents these
schedules from being identified.

The paper's serial-matrix-multiplication complexity result requires a hardware
refinement proving that all layerwise operations in a phase execute in
parallel.  The dynamical theorems below do not assume that refinement or turn
abstract critical-path counts into wall-clock claims.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open Filter Topology

/-! ## Source-shaped simultaneous update -/

/-- One scalar latent and one scalar plastic parameter. -/
abbrev IncrementalJointState := ℝ × ℝ

/-- The snapshot-synchronous form of Equations (6)--(7): both new coordinates
read gradients at the same old state and parameter. -/
noncomputable def synchronousIncrementalStep
    (stateRate parameterRate : ℝ)
    (stateGradient parameterGradient : ℝ → ℝ → ℝ) :
    IncrementalJointState → IncrementalJointState :=
  fun current =>
    (current.1 -
        stateRate * stateGradient current.1 current.2,
      current.2 -
        parameterRate * parameterGradient current.1 current.2)

/-- A sequential latent-then-parameter schedule over the same two gradients.
This is a distinct execution semantics, not a spelling of the synchronous
source update. -/
noncomputable def sequentialIncrementalStep
    (stateRate parameterRate : ℝ)
    (stateGradient parameterGradient : ℝ → ℝ → ℝ) :
    IncrementalJointState → IncrementalJointState :=
  fun current =>
    let nextState :=
      current.1 - stateRate * stateGradient current.1 current.2
    (nextState,
      current.2 -
        parameterRate * parameterGradient nextState current.2)

/-- A coupled sum-of-squared-errors energy with rational modal spectrum. -/
noncomputable def coupledIncrementalEnergy
    (state parameter : ℝ) : ℝ :=
  ((state + parameter) ^ 2 + 3 * (state - parameter) ^ 2) / 4

/-- Latent-state gradient of `coupledIncrementalEnergy`. -/
noncomputable def coupledStateGradient
    (state parameter : ℝ) : ℝ :=
  2 * state - parameter

/-- Plastic-parameter gradient of `coupledIncrementalEnergy`. -/
noncomputable def coupledParameterGradient
    (state parameter : ℝ) : ℝ :=
  2 * parameter - state

theorem coupledIncrementalEnergy_eq_expanded
    (state parameter : ℝ) :
    coupledIncrementalEnergy state parameter =
      state ^ 2 - state * parameter + parameter ^ 2 := by
  unfold coupledIncrementalEnergy
  ring

theorem coupledIncrementalEnergy_nonnegative
    (state parameter : ℝ) :
    0 ≤ coupledIncrementalEnergy state parameter := by
  unfold coupledIncrementalEnergy
  positivity

/-- The declared state signal really is the partial derivative of the energy. -/
theorem coupledIncrementalEnergy_hasDerivAt_state
    (state parameter : ℝ) :
    HasDerivAt
      (fun candidate => coupledIncrementalEnergy candidate parameter)
      (coupledStateGradient state parameter) state := by
  unfold coupledIncrementalEnergy coupledStateGradient
  have hsum :=
    ((hasDerivAt_id state).add_const parameter).pow 2
  have hdifference :=
    ((hasDerivAt_id state).sub_const parameter).pow 2
  convert (hsum.add (hdifference.const_mul 3)).div_const 4 using 1
  all_goals
    try rfl
    try simp
    try ring

/-- The declared plasticity signal really is the other partial derivative. -/
theorem coupledIncrementalEnergy_hasDerivAt_parameter
    (state parameter : ℝ) :
    HasDerivAt
      (fun candidate => coupledIncrementalEnergy state candidate)
      (coupledParameterGradient state parameter) parameter := by
  unfold coupledIncrementalEnergy coupledParameterGradient
  have hsum :=
    ((hasDerivAt_id parameter).const_add state).pow 2
  have hdifference :=
    ((hasDerivAt_id parameter).neg.const_add state).pow 2
  convert (hsum.add (hdifference.const_mul 3)).div_const 4 using 1
  all_goals
    try rfl
    try simp
    try ring

/-- The source-synchronous iPC step on the coupled quadratic. -/
noncomputable def coupledIncrementalStep
    (rate : ℝ) : IncrementalJointState → IncrementalJointState :=
  synchronousIncrementalStep rate rate
    coupledStateGradient coupledParameterGradient

theorem coupledIncrementalStep_apply
    (rate : ℝ) (current : IncrementalJointState) :
    coupledIncrementalStep rate current =
      ((1 - 2 * rate) * current.1 + rate * current.2,
        rate * current.1 + (1 - 2 * rate) * current.2) := by
  simp [coupledIncrementalStep, synchronousIncrementalStep,
    coupledStateGradient, coupledParameterGradient]
  constructor <;> ring

/-- Turning off plasticity exactly recovers a state-only gradient step. -/
theorem synchronousIncrementalStep_zero_parameterRate
    (stateRate : ℝ) (stateGradient parameterGradient : ℝ → ℝ → ℝ)
    (current : IncrementalJointState) :
    synchronousIncrementalStep stateRate 0
        stateGradient parameterGradient current =
      (current.1 -
          stateRate * stateGradient current.1 current.2,
        current.2) := by
  simp [synchronousIncrementalStep]

/-- Turning off state inference exactly recovers a parameter-only step. -/
theorem synchronousIncrementalStep_zero_stateRate
    (parameterRate : ℝ)
    (stateGradient parameterGradient : ℝ → ℝ → ℝ)
    (current : IncrementalJointState) :
    synchronousIncrementalStep 0 parameterRate
        stateGradient parameterGradient current =
      (current.1,
        current.2 -
          parameterRate * parameterGradient current.1 current.2) := by
  simp [synchronousIncrementalStep]

/-- Concrete scheduling boundary: snapshot-synchronous and latent-first
updates disagree even when they use the same energy, gradients, and rates. -/
theorem synchronous_ne_sequential_incremental :
    synchronousIncrementalStep (1 / 2) (1 / 2)
        coupledStateGradient coupledParameterGradient (1, 0) ≠
      sequentialIncrementalStep (1 / 2) (1 / 2)
        coupledStateGradient coupledParameterGradient (1, 0) := by
  norm_num [synchronousIncrementalStep, sequentialIncrementalStep,
    coupledStateGradient, coupledParameterGradient]

/-! ## Exact modal dynamics -/

/-- Common-mode coordinate. -/
noncomputable def incrementalCommon
    (current : IncrementalJointState) : ℝ :=
  current.1 + current.2

/-- State--parameter disagreement coordinate. -/
noncomputable def incrementalDisagreement
    (current : IncrementalJointState) : ℝ :=
  current.1 - current.2

theorem incrementalCommon_step
    (rate : ℝ) (current : IncrementalJointState) :
    incrementalCommon (coupledIncrementalStep rate current) =
      (1 - rate) * incrementalCommon current := by
  rw [coupledIncrementalStep_apply]
  simp [incrementalCommon]
  ring

theorem incrementalDisagreement_step
    (rate : ℝ) (current : IncrementalJointState) :
    incrementalDisagreement (coupledIncrementalStep rate current) =
      (1 - 3 * rate) * incrementalDisagreement current := by
  rw [coupledIncrementalStep_apply]
  simp [incrementalDisagreement]
  ring

theorem incrementalCommon_iterate
    (rate : ℝ) (current : IncrementalJointState) (steps : ℕ) :
    incrementalCommon
        (Nat.iterate (coupledIncrementalStep rate) steps current) =
      (1 - rate) ^ steps * incrementalCommon current := by
  induction steps with
  | zero =>
      simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', incrementalCommon_step,
        inductionHypothesis, pow_succ]
      ring

theorem incrementalDisagreement_iterate
    (rate : ℝ) (current : IncrementalJointState) (steps : ℕ) :
    incrementalDisagreement
        (Nat.iterate (coupledIncrementalStep rate) steps current) =
      (1 - 3 * rate) ^ steps * incrementalDisagreement current := by
  induction steps with
  | zero =>
      simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', incrementalDisagreement_step,
        inductionHypothesis, pow_succ]
      ring

/-- Exact reconstruction of every finite synchronous iPC trajectory. -/
theorem coupledIncrementalStep_iterate
    (rate : ℝ) (current : IncrementalJointState) (steps : ℕ) :
    Nat.iterate (coupledIncrementalStep rate) steps current =
      (((1 - rate) ^ steps * incrementalCommon current +
          (1 - 3 * rate) ^ steps * incrementalDisagreement current) / 2,
        ((1 - rate) ^ steps * incrementalCommon current -
          (1 - 3 * rate) ^ steps * incrementalDisagreement current) / 2) := by
  induction steps with
  | zero =>
      ext <;> simp [incrementalCommon, incrementalDisagreement]
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis,
        coupledIncrementalStep_apply]
      ext <;>
        simp [incrementalCommon, incrementalDisagreement, pow_succ] <;>
        ring

/-- The energy is exactly the weighted squared norm of the two modes. -/
theorem coupledIncrementalEnergy_eq_modes
    (current : IncrementalJointState) :
    coupledIncrementalEnergy current.1 current.2 =
      (incrementalCommon current ^ 2 +
        3 * incrementalDisagreement current ^ 2) / 4 := by
  rfl

/-- Exact one-step energy transport. -/
theorem coupledIncrementalEnergy_step
    (rate : ℝ) (current : IncrementalJointState) :
    coupledIncrementalEnergy
        (coupledIncrementalStep rate current).1
        (coupledIncrementalStep rate current).2 =
      (((1 - rate) ^ 2 * incrementalCommon current ^ 2) +
        3 * ((1 - 3 * rate) ^ 2 *
          incrementalDisagreement current ^ 2)) / 4 := by
  rw [coupledIncrementalEnergy_eq_modes, incrementalCommon_step,
    incrementalDisagreement_step]
  ring

private theorem common_or_disagreement_ne_zero
    (current : IncrementalJointState) (currentNonzero : current ≠ 0) :
    incrementalCommon current ≠ 0 ∨
      incrementalDisagreement current ≠ 0 := by
  by_contra neither
  simp only [not_or, not_ne_iff] at neither
  apply currentNonzero
  apply Prod.ext <;>
    simp only [Prod.fst_zero, Prod.snd_zero]
  · have := neither.1
    have := neither.2
    simp only [incrementalCommon, incrementalDisagreement] at *
    linarith
  · have := neither.1
    have := neither.2
    simp only [incrementalCommon, incrementalDisagreement] at *
    linarith

/-- Inside the sharp modal interval, every nonzero joint state strictly
decreases the coupled free energy in one synchronous update. -/
theorem coupledIncrementalEnergy_strictly_decreases
    (rate : ℝ) (current : IncrementalJointState)
    (ratePositive : 0 < rate) (rateBelow : rate < 2 / 3)
    (currentNonzero : current ≠ 0) :
    coupledIncrementalEnergy
        (coupledIncrementalStep rate current).1
        (coupledIncrementalStep rate current).2 <
      coupledIncrementalEnergy current.1 current.2 := by
  rw [coupledIncrementalEnergy_step,
    coupledIncrementalEnergy_eq_modes]
  have hcommonCoefficient : 0 < 1 - (1 - rate) ^ 2 := by
    nlinarith
  have hdisagreementCoefficient :
      0 < 1 - (1 - 3 * rate) ^ 2 := by
    nlinarith
  rcases common_or_disagreement_ne_zero current currentNonzero with
    hcommon | hdisagreement
  · have hcommonSq : 0 < incrementalCommon current ^ 2 :=
      sq_pos_of_ne_zero hcommon
    have hdisagreementSq :
        0 ≤ incrementalDisagreement current ^ 2 :=
      sq_nonneg _
    nlinarith
  · have hcommonSq : 0 ≤ incrementalCommon current ^ 2 :=
      sq_nonneg _
    have hdisagreementSq :
        0 < incrementalDisagreement current ^ 2 :=
      sq_pos_of_ne_zero hdisagreement
    nlinarith

/-! ## Sharp stability and failure boundaries -/

/-- Every trajectory converges to the joint optimum in the sharp open
interval. -/
theorem coupledIncremental_converges
    (rate : ℝ) (current : IncrementalJointState)
    (ratePositive : 0 < rate) (rateBelow : rate < 2 / 3) :
    Tendsto
      (fun steps =>
        Nat.iterate (coupledIncrementalStep rate) steps current)
      atTop (nhds (0 : IncrementalJointState)) := by
  have hcommonMultiplier : |1 - rate| < 1 :=
    (abs_one_sub_lt_one_iff rate).2
      ⟨ratePositive, by linarith⟩
  have hdisagreementMultiplier : |1 - 3 * rate| < 1 := by
    have : 0 < 3 * rate ∧ 3 * rate < 2 := by
      constructor <;> nlinarith
    exact (abs_one_sub_lt_one_iff (3 * rate)).2 this
  have hcommon :
      Tendsto
        (fun steps : ℕ =>
          (1 - rate) ^ steps * incrementalCommon current)
        atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        hcommonMultiplier).mul_const (incrementalCommon current)
  have hdisagreement :
      Tendsto
        (fun steps : ℕ =>
          (1 - 3 * rate) ^ steps * incrementalDisagreement current)
        atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        hdisagreementMultiplier).mul_const
          (incrementalDisagreement current)
  have hfirst :
      Tendsto
        (fun steps : ℕ =>
          (((1 - rate) ^ steps * incrementalCommon current +
            (1 - 3 * rate) ^ steps *
              incrementalDisagreement current) / 2))
        atTop (nhds 0) := by
    simpa only [zero_add, zero_div] using
      (hcommon.add hdisagreement).div_const 2
  have hsecond :
      Tendsto
        (fun steps : ℕ =>
          (((1 - rate) ^ steps * incrementalCommon current -
            (1 - 3 * rate) ^ steps *
              incrementalDisagreement current) / 2))
        atTop (nhds 0) := by
    simpa only [zero_sub, neg_zero, zero_div] using
      (hcommon.sub hdisagreement).div_const 2
  have hpair :
      Tendsto
        (fun steps : ℕ =>
          (((1 - rate) ^ steps * incrementalCommon current +
              (1 - 3 * rate) ^ steps *
                incrementalDisagreement current) / 2,
            ((1 - rate) ^ steps * incrementalCommon current -
              (1 - 3 * rate) ^ steps *
                incrementalDisagreement current) / 2))
        atTop (nhds (0 : IncrementalJointState)) :=
    (Prod.tendsto_iff _ _).2 ⟨hfirst, hsecond⟩
  exact hpair.congr' (Filter.Eventually.of_forall fun steps =>
    (coupledIncrementalStep_iterate rate current steps).symm)

/-- At the upper endpoint, the pure disagreement mode changes sign. -/
theorem coupledIncremental_twoThird_pureDisagreement
    (value : ℝ) :
    coupledIncrementalStep (2 / 3) (value, -value) =
      (-value, value) := by
  rw [coupledIncrementalStep_apply]
  norm_num
  constructor <;> ring

/-- The endpoint therefore has an exact period-two orbit. -/
theorem coupledIncremental_twoThird_twoCycle
    (value : ℝ) :
    Nat.iterate (coupledIncrementalStep (2 / 3)) 2
        (value, -value) =
      (value, -value) := by
  change coupledIncrementalStep (2 / 3)
      (coupledIncrementalStep (2 / 3) (value, -value)) =
    (value, -value)
  rw [coupledIncremental_twoThird_pureDisagreement]
  simpa only [neg_neg] using
    coupledIncremental_twoThird_pureDisagreement (-value)

/-- A concrete endpoint orbit is nonconstant. -/
theorem coupledIncremental_twoThird_not_fixed :
    coupledIncrementalStep (2 / 3) (1, -1) ≠ (1, -1) := by
  rw [coupledIncremental_twoThird_pureDisagreement]
  norm_num

/-- Every iterate of the concrete endpoint orbit has unit product norm. -/
theorem norm_coupledIncremental_twoThird_iterate
    (steps : ℕ) :
    ‖Nat.iterate (coupledIncrementalStep (2 / 3)) steps (1, -1)‖ =
      1 := by
  rw [coupledIncrementalStep_iterate]
  norm_num [incrementalCommon, incrementalDisagreement, Prod.norm_def]

/-- Thus the endpoint orbit does not converge to the joint optimum. -/
theorem coupledIncremental_twoThird_not_tendsto_zero :
    ¬ Tendsto
      (fun steps =>
        Nat.iterate (coupledIncrementalStep (2 / 3)) steps (1, -1))
      atTop (nhds (0 : IncrementalJointState)) := by
  intro trajectoryConverges
  have normConverges :
      Tendsto
        (fun steps =>
          ‖Nat.iterate
            (coupledIncrementalStep (2 / 3)) steps (1, -1)‖)
        atTop (nhds 0) := by
    simpa using trajectoryConverges.norm
  have oneConvergesToZero :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    simpa only [norm_coupledIncremental_twoThird_iterate] using
      normConverges
  have oneConvergesToOne :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have : (0 : ℝ) = 1 :=
    tendsto_nhds_unique oneConvergesToZero oneConvergesToOne
  norm_num at this

theorem abs_incrementalDisagreement_iterate
    (rate : ℝ) (current : IncrementalJointState) (steps : ℕ) :
    |incrementalDisagreement
        (Nat.iterate (coupledIncrementalStep rate) steps current)| =
      |1 - 3 * rate| ^ steps *
        |incrementalDisagreement current| := by
  rw [incrementalDisagreement_iterate, abs_mul, abs_pow]

/-- Above the sharp endpoint, every trajectory with nonzero disagreement has
diverging disagreement magnitude. -/
theorem coupledIncremental_disagreement_diverges
    (rate : ℝ) (current : IncrementalJointState)
    (rateAbove : 2 / 3 < rate)
    (disagreementNonzero : incrementalDisagreement current ≠ 0) :
    Tendsto
      (fun steps =>
        |incrementalDisagreement
          (Nat.iterate (coupledIncrementalStep rate) steps current)|)
      atTop atTop := by
  have multiplierAboveOne : 1 < |1 - 3 * rate| := by
    rw [abs_of_neg (by nlinarith)]
    nlinarith
  have powerDiverges :
      Tendsto (fun steps : ℕ => |1 - 3 * rate| ^ steps)
        atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt multiplierAboveOne
  have disagreementPositive :
      0 < |incrementalDisagreement current| :=
    abs_pos.mpr disagreementNonzero
  simpa only [abs_incrementalDisagreement_iterate] using
    powerDiverges.atTop_mul_const disagreementPositive

/-! ## Source/implementation scheduling boundary -/

/-- The current scalar credit-transport fixture is explicitly latent-first:
its plasticity signal is evaluated at the newly settled latent. -/
theorem scalarIncrementalTransition_is_sequential
    (problem : CreditTransport.Instances.ScalarPCProblem)
    (prediction : CreditTransport.Instances.ScalarPCParameter)
    (current : CreditTransport.Instances.IncrementalPCState) :
    let stateGradient : ℝ → ℝ → ℝ :=
      fun latent working =>
        -(problem.target - latent +
          problem.penalty * (working - latent))
    let parameterGradient : ℝ → ℝ → ℝ :=
      fun latent working =>
        problem.penalty * (working - latent)
    let next :=
      sequentialIncrementalStep problem.settlingRate
        problem.plasticityRate stateGradient parameterGradient
        (current.latent, current.workingPrediction)
    let transitioned :=
      CreditTransport.Instances.incrementalPCTransition
        problem prediction
        CreditTransport.Instances.IncrementalPCEvent.settleAndPlasticity
        current
    (transitioned.latent, transitioned.workingPrediction) = next := by
  dsimp [CreditTransport.Instances.incrementalPCTransition,
    sequentialIncrementalStep]
  apply Prod.ext <;> dsimp <;> ring

#print axioms coupledIncrementalEnergy_hasDerivAt_state
#print axioms coupledIncrementalEnergy_hasDerivAt_parameter
#print axioms synchronous_ne_sequential_incremental
#print axioms coupledIncrementalStep_iterate
#print axioms coupledIncrementalEnergy_strictly_decreases
#print axioms coupledIncremental_converges
#print axioms coupledIncremental_twoThird_twoCycle
#print axioms coupledIncremental_twoThird_not_tendsto_zero
#print axioms coupledIncremental_disagreement_diverges
#print axioms scalarIncrementalTransition_is_sequential

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
