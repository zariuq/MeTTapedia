import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActionMemoryLocalPC

/-!
# A genuine local predictive-coding energy for routed action memory

The forward reasoner and the learning rule are deliberately separate.  This
module freezes the reasoner's slow parameters, introduces active/evidence
states as local inference variables, and defines a precision-weighted residual
energy with a supervised readout term.  State inference descends this energy.
After finite settling, parameter credit is the partial derivative of the same
energy with the states detached.  It is therefore not reverse-mode
differentiation through the finite inference unroll.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace ActionMemoryLocalPC

noncomputable section

local instance (priority := 2000) realEnergyModule : Module ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toModule

/-- Real derivative proposition using the canonical real inner-product module.
This pins the same definitional instance used by the imported nonlinear
derivative rules. -/
abbrev RealEnergyHasDerivAt (function : ℝ → ℝ)
    (derivative point : ℝ) : Prop :=
  @HasDerivAt ℝ inferInstance ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule inferInstance inferInstance
    function derivative point

/-- Scalar restriction of one independently coupled hidden coordinate and one
task readout.  The Python runtime applies this construction to all hidden
coordinates and aggregates the resulting parameter gradients. -/
structure ScalarPCProblem where
  activeDrive : ℝ
  evidenceDrive : ℝ
  activeCoupling : ℝ
  evidenceCoupling : ℝ
  readoutWeight : ℝ
  target : ℝ
  residualPrecision : ℝ
  taskPrecision : ℝ

def ScalarPCProblem.activePrediction
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  Real.tanh (problem.activeDrive + problem.activeCoupling * state.evidence)

def ScalarPCProblem.evidencePrediction
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  Real.tanh (problem.evidenceDrive + problem.evidenceCoupling * state.active)

def ScalarPCProblem.activeResidual
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  state.active + -problem.activePrediction state

def ScalarPCProblem.evidenceResidual
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  state.evidence + -problem.evidencePrediction state

def ScalarPCProblem.taskResidual
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  problem.readoutWeight * state.active - problem.target

/-- Residual PC energy on the actual two-node state plus the local supervised
readout. -/
def ScalarPCProblem.energy
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  problem.residualPrecision / 2 *
      (problem.activeResidual state ^ 2 + problem.evidenceResidual state ^ 2) +
    problem.taskPrecision / 2 * problem.taskResidual state ^ 2

/-- The factorial contains two genuinely different residual graphs.  The
feedforward graph freezes the active parent used by the evidence node at its
direct drive.  The equilibrium graph uses the live active state and therefore
contains the two-node cycle. -/
inductive ReasonerDynamics where
  | feedforward
  | equilibrium
deriving DecidableEq, Repr

def ScalarPCProblem.feedforwardEvidencePrediction
    (problem : ScalarPCProblem) : ℝ :=
  Real.tanh
    (problem.evidenceDrive +
      problem.evidenceCoupling * Real.tanh problem.activeDrive)

def ScalarPCProblem.feedforwardEvidenceResidual
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  state.evidence - problem.feedforwardEvidencePrediction

def ScalarPCProblem.evidenceResidualFor
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (state : TwoNodeState) : ℝ :=
  match dynamics with
  | .feedforward => problem.feedforwardEvidenceResidual state
  | .equilibrium => problem.evidenceResidual state

/-- The dynamics-indexed local PC energy used by the factorial.  Both cells
share the active residual and task term; only the evidence parent graph changes. -/
def ScalarPCProblem.energyFor
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (state : TwoNodeState) : ℝ :=
  problem.residualPrecision / 2 *
      (problem.activeResidual state ^ 2 +
        problem.evidenceResidualFor dynamics state ^ 2) +
    problem.taskPrecision / 2 * problem.taskResidual state ^ 2

@[simp] theorem ScalarPCProblem.energyFor_equilibrium
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    problem.energyFor .equilibrium state = problem.energy state := rfl

theorem ScalarPCProblem.energyFor_eq_of_evidenceCoupling_zero
    (problem : ScalarPCProblem) (state : TwoNodeState)
    (hzero : problem.evidenceCoupling = 0) :
    problem.energyFor .feedforward state =
      problem.energyFor .equilibrium state := by
  have hresidual :
      problem.feedforwardEvidenceResidual state =
        problem.evidenceResidual state := by
    simp [ScalarPCProblem.feedforwardEvidenceResidual,
      ScalarPCProblem.feedforwardEvidencePrediction,
      ScalarPCProblem.evidenceResidual, ScalarPCProblem.evidencePrediction,
      hzero, sub_eq_add_neg]
  simp [ScalarPCProblem.energyFor, ScalarPCProblem.evidenceResidualFor,
    hresidual]

/-- Negative fixture: equal dimensions and parameter storage do not identify
the learning objective when one graph freezes the evidence parent and the
other closes the cycle. -/
theorem feedforward_and_equilibrium_energy_can_differ :
    let problem : ScalarPCProblem :=
      { activeDrive := 0, evidenceDrive := 0
        activeCoupling := 0, evidenceCoupling := 1
        readoutWeight := 0, target := 0
        residualPrecision := 1, taskPrecision := 0 }
    let state : TwoNodeState := { active := 1, evidence := 0 }
    problem.energyFor .feedforward state ≠
      problem.energyFor .equilibrium state := by
  dsimp
  intro equality
  have htanhNe : Real.tanh (1 : ℝ) ≠ 0 := by
    intro hzero
    have hzero' : Real.tanh (1 : ℝ) = Real.tanh (0 : ℝ) := by
      simpa using hzero
    have harg := Real.tanh_injective hzero'
    norm_num at harg
  have htanhSqPos : 0 < Real.tanh (1 : ℝ) ^ 2 := sq_pos_of_ne_zero htanhNe
  simp [ScalarPCProblem.energyFor, ScalarPCProblem.evidenceResidualFor,
    ScalarPCProblem.feedforwardEvidenceResidual,
    ScalarPCProblem.feedforwardEvidencePrediction,
    ScalarPCProblem.activeResidual, ScalarPCProblem.activePrediction,
    ScalarPCProblem.energy, ScalarPCProblem.evidenceResidual,
    ScalarPCProblem.evidencePrediction, ScalarPCProblem.taskResidual] at equality
  nlinarith

/-- Active-coordinate path written as an explicit sum of functions, matching
the derivative combinator's definitional representation. -/
def ScalarPCProblem.activeEnergyPath
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ → ℝ :=
  (fun value => problem.residualPrecision / 2 *
      (((fun active => problem.activeResidual
          { active := active, evidence := state.evidence }) ^ 2 +
        (fun active => problem.evidenceResidual
          { active := active, evidence := state.evidence }) ^ 2) value)) +
    (fun value => problem.taskPrecision / 2 *
      ((fun active => problem.taskResidual
        { active := active, evidence := state.evidence }) ^ 2) value)

@[simp] theorem ScalarPCProblem.activeEnergyPath_apply
    (problem : ScalarPCProblem) (state : TwoNodeState) (active : ℝ) :
    problem.activeEnergyPath state active =
      problem.energy { active := active, evidence := state.evidence } := rfl

/-- Evidence-coordinate path in the same explicit function representation. -/
def ScalarPCProblem.evidenceEnergyPath
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ → ℝ :=
  (fun value => problem.residualPrecision / 2 *
      (((fun evidence => problem.activeResidual
          { active := state.active, evidence := evidence }) ^ 2 +
        (fun evidence => problem.evidenceResidual
          { active := state.active, evidence := evidence }) ^ 2) value)) +
    (fun value => problem.taskPrecision / 2 *
      ((fun evidence => problem.taskResidual
        { active := state.active, evidence := evidence }) ^ 2) value)

@[simp] theorem ScalarPCProblem.evidenceEnergyPath_apply
    (problem : ScalarPCProblem) (state : TwoNodeState) (evidence : ℝ) :
    problem.evidenceEnergyPath state evidence =
      problem.energy { active := state.active, evidence := evidence } := rfl

def tanhSlope (input : ℝ) : ℝ := 1 / Real.cosh input ^ 2

private theorem hasDerivAt_tanh_localEnergy (input : ℝ) :
    HasDerivAt Real.tanh (tanhSlope input) input := by
  have hquotient := (Real.hasDerivAt_sinh input).div
    (Real.hasDerivAt_cosh input) (Real.cosh_pos input).ne'
  have hfunction : Real.tanh = Real.sinh / Real.cosh := by
    funext value
    simpa only [Pi.div_apply] using Real.tanh_eq_sinh_div_cosh value
  rw [hfunction]
  apply hquotient.congr_deriv
  simp only [tanhSlope]
  field_simp [(Real.cosh_pos input).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq input]

theorem tanhSlope_nonneg (input : ℝ) : 0 ≤ tanhSlope input := by
  exact div_nonneg (by norm_num) (sq_nonneg _)

theorem tanhSlope_le_one (input : ℝ) : tanhSlope input ≤ 1 := by
  simpa [tanhSlope, abs_of_nonneg (tanhSlope_nonneg input)] using
    abs_tanh_derivative_le_one input

/-- Exact active-state partial derivative of the local PC energy. -/
def ScalarPCProblem.activeStateGradient
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  problem.residualPrecision / 2 *
      (2 * problem.activeResidual
          { active := state.active, evidence := state.evidence } +
        2 * problem.evidenceResidual
            { active := state.active, evidence := state.evidence } *
          (-problem.evidenceCoupling *
            tanhSlope
              (problem.evidenceDrive + problem.evidenceCoupling * state.active))) +
    problem.taskPrecision / 2 *
      (2 * problem.taskResidual
        { active := state.active, evidence := state.evidence } *
          problem.readoutWeight)

/-- Exact evidence-state partial derivative of the local PC energy. -/
def ScalarPCProblem.evidenceStateGradient
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  problem.residualPrecision / 2 *
    (2 * problem.activeResidual
        { active := state.active, evidence := state.evidence } *
        (-problem.activeCoupling *
          tanhSlope
            (problem.activeDrive + problem.activeCoupling * state.evidence)) +
      2 * problem.evidenceResidual
        { active := state.active, evidence := state.evidence })

theorem ScalarPCProblem.activeStateGradient_localForm
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    problem.activeStateGradient state =
      problem.residualPrecision *
          (problem.activeResidual state -
            problem.evidenceResidual state * problem.evidenceCoupling *
              tanhSlope
                (problem.evidenceDrive +
                  problem.evidenceCoupling * state.active)) +
        problem.taskPrecision * problem.readoutWeight *
          problem.taskResidual state := by
  have hstate :
      ({ active := state.active, evidence := state.evidence } : TwoNodeState) =
        state := by cases state; rfl
  simp [ScalarPCProblem.activeStateGradient]
  rw [hstate]
  ring

theorem ScalarPCProblem.evidenceStateGradient_localForm
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    problem.evidenceStateGradient state =
      problem.residualPrecision *
        (problem.evidenceResidual state -
          problem.activeResidual state * problem.activeCoupling *
            tanhSlope
              (problem.activeDrive +
                problem.activeCoupling * state.evidence)) := by
  have hstate :
      ({ active := state.active, evidence := state.evidence } : TwoNodeState) =
        state := by cases state; rfl
  simp [ScalarPCProblem.evidenceStateGradient]
  rw [hstate]
  ring

/-- Exact active-state field for the acyclic feedforward residual graph.  The
evidence residual contributes no active-state derivative because its active
parent was frozen at the direct drive. -/
def ScalarPCProblem.feedforwardActiveStateGradient
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  problem.residualPrecision / 2 *
      (2 * problem.activeResidual state +
        2 * problem.feedforwardEvidenceResidual state * 0) +
    problem.taskPrecision / 2 *
      (2 * problem.taskResidual state * problem.readoutWeight)

/-- Exact evidence-state field for the acyclic feedforward residual graph. -/
def ScalarPCProblem.feedforwardEvidenceStateGradient
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ :=
  problem.residualPrecision / 2 *
    (2 * problem.activeResidual state *
        (-problem.activeCoupling *
          tanhSlope
            (problem.activeDrive + problem.activeCoupling * state.evidence)) +
      2 * problem.feedforwardEvidenceResidual state) +
    problem.taskPrecision / 2 * (2 * problem.taskResidual state * 0)

theorem ScalarPCProblem.feedforwardActiveStateGradient_localForm
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    problem.feedforwardActiveStateGradient state =
      problem.residualPrecision * problem.activeResidual state +
        problem.taskPrecision * problem.readoutWeight *
          problem.taskResidual state := by
  simp [ScalarPCProblem.feedforwardActiveStateGradient]
  ring

theorem ScalarPCProblem.feedforwardEvidenceStateGradient_localForm
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    problem.feedforwardEvidenceStateGradient state =
      problem.residualPrecision *
        (problem.feedforwardEvidenceResidual state -
          problem.activeResidual state * problem.activeCoupling *
            tanhSlope
              (problem.activeDrive + problem.activeCoupling * state.evidence)) := by
  simp [ScalarPCProblem.feedforwardEvidenceStateGradient]
  ring

def ScalarPCProblem.feedforwardActiveEnergyPath
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ → ℝ :=
  (fun value => problem.residualPrecision / 2 *
      (((fun active => problem.activeResidual
          { active := active, evidence := state.evidence }) ^ 2 +
        (fun active => problem.feedforwardEvidenceResidual
          { active := active, evidence := state.evidence }) ^ 2) value)) +
    (fun value => problem.taskPrecision / 2 *
      ((fun active => problem.taskResidual
        { active := active, evidence := state.evidence }) ^ 2) value)

def ScalarPCProblem.feedforwardEvidenceEnergyPath
    (problem : ScalarPCProblem) (state : TwoNodeState) : ℝ → ℝ :=
  (fun value => problem.residualPrecision / 2 *
      (((fun evidence => problem.activeResidual
          { active := state.active, evidence := evidence }) ^ 2 +
        (fun evidence => problem.feedforwardEvidenceResidual
          { active := state.active, evidence := evidence }) ^ 2) value)) +
    (fun value => problem.taskPrecision / 2 *
      ((fun evidence => problem.taskResidual
        { active := state.active, evidence := evidence }) ^ 2) value)

private theorem hasDerivAt_activeResidual_activePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    HasDerivAt
      (fun active => problem.activeResidual
        { active := active, evidence := state.evidence })
      1 state.active := by
  simpa [ScalarPCProblem.activeResidual,
    ScalarPCProblem.activePrediction] using
    (hasDerivAt_id state.active).sub_const
      (Real.tanh
        (problem.activeDrive + problem.activeCoupling * state.evidence))

private theorem hasDerivAt_evidenceResidual_activePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    HasDerivAt
      (fun active => problem.evidenceResidual
        { active := active, evidence := state.evidence })
      (-problem.evidenceCoupling *
        tanhSlope
          (problem.evidenceDrive + problem.evidenceCoupling * state.active))
      state.active := by
  have hinner : HasDerivAt
      (fun active => problem.evidenceDrive + problem.evidenceCoupling * active)
      problem.evidenceCoupling state.active := by
    simpa [add_comm] using
      ((hasDerivAt_id state.active).const_mul
        problem.evidenceCoupling).const_add problem.evidenceDrive
  have htanh := (hasDerivAt_tanh_localEnergy
    (problem.evidenceDrive + problem.evidenceCoupling * state.active)).comp
      state.active hinner
  have htanh' : HasDerivAt
      (Real.tanh ∘
        fun active => problem.evidenceDrive + problem.evidenceCoupling * active)
      (problem.evidenceCoupling *
        tanhSlope
          (problem.evidenceDrive + problem.evidenceCoupling * state.active))
      state.active :=
    htanh.congr_deriv (by simp [tanhSlope]; ring)
  simpa [ScalarPCProblem.evidenceResidual,
    ScalarPCProblem.evidencePrediction, Function.comp_def, add_comm] using
    htanh'.neg.const_add state.evidence

private theorem hasDerivAt_taskResidual_activePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    HasDerivAt
      (fun active => problem.taskResidual
        { active := active, evidence := state.evidence })
      problem.readoutWeight state.active := by
  simpa [ScalarPCProblem.taskResidual] using
    ((hasDerivAt_id state.active).const_mul
      problem.readoutWeight).sub_const problem.target

/-- The declared active-state field is the derivative of the declared energy,
not an independently posited update. -/
theorem ScalarPCProblem.hasDerivAt_energy_activePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.activeEnergyPath state)
      (problem.activeStateGradient state) state.active := by
  have hactive := hasDerivAt_activeResidual_activePath problem state
  have hevidence := hasDerivAt_evidenceResidual_activePath problem state
  have htask := hasDerivAt_taskResidual_activePath problem state
  have hresidual :=
    ((hactive.pow 2).add (hevidence.pow 2)).const_mul
      (problem.residualPrecision / 2)
  have hsupervised := (htask.pow 2).const_mul (problem.taskPrecision / 2)
  have hstate :
      ({ active := state.active, evidence := state.evidence } : TwoNodeState) =
        state := by
    cases state
    rfl
  simpa only [ScalarPCProblem.activeEnergyPath,
    ScalarPCProblem.activeStateGradient, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSubDiff, pow_one, mul_one, hstate] using
    hresidual.add hsupervised

private theorem hasDerivAt_activeResidual_evidencePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    HasDerivAt
      (fun evidence => problem.activeResidual
        { active := state.active, evidence := evidence })
      (-problem.activeCoupling *
        tanhSlope
          (problem.activeDrive + problem.activeCoupling * state.evidence))
      state.evidence := by
  have hinner : HasDerivAt
      (fun evidence => problem.activeDrive + problem.activeCoupling * evidence)
      problem.activeCoupling state.evidence := by
    simpa [add_comm] using
      ((hasDerivAt_id state.evidence).const_mul
        problem.activeCoupling).const_add problem.activeDrive
  have htanh := (hasDerivAt_tanh_localEnergy
    (problem.activeDrive + problem.activeCoupling * state.evidence)).comp
      state.evidence hinner
  have htanh' : HasDerivAt
      (Real.tanh ∘
        fun evidence => problem.activeDrive + problem.activeCoupling * evidence)
      (problem.activeCoupling *
        tanhSlope
          (problem.activeDrive + problem.activeCoupling * state.evidence))
      state.evidence :=
    htanh.congr_deriv (by simp [tanhSlope]; ring)
  simpa [ScalarPCProblem.activeResidual, ScalarPCProblem.activePrediction,
    Function.comp_def, add_comm] using
    htanh'.neg.const_add state.active

private theorem hasDerivAt_evidenceResidual_evidencePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    HasDerivAt
      (fun evidence => problem.evidenceResidual
        { active := state.active, evidence := evidence })
      1 state.evidence := by
  simpa [ScalarPCProblem.evidenceResidual,
    ScalarPCProblem.evidencePrediction] using
    (hasDerivAt_id state.evidence).sub_const
      (Real.tanh
        (problem.evidenceDrive + problem.evidenceCoupling * state.active))

/-- The declared evidence-state field is likewise the exact energy partial
derivative. -/
theorem ScalarPCProblem.hasDerivAt_energy_evidencePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.evidenceEnergyPath state)
      (problem.evidenceStateGradient state) state.evidence := by
  have hactive := hasDerivAt_activeResidual_evidencePath problem state
  have hevidence := hasDerivAt_evidenceResidual_evidencePath problem state
  have htask : HasDerivAt
      (fun _evidence : ℝ => problem.taskResidual state) 0 state.evidence :=
    hasDerivAt_const state.evidence _
  have hresidual :=
    ((hactive.pow 2).add (hevidence.pow 2)).const_mul
      (problem.residualPrecision / 2)
  have hsupervised := (htask.pow 2).const_mul (problem.taskPrecision / 2)
  have hstate :
      ({ active := state.active, evidence := state.evidence } : TwoNodeState) =
        state := by
    cases state
    rfl
  simpa only [ScalarPCProblem.evidenceEnergyPath,
    ScalarPCProblem.evidenceStateGradient, ScalarPCProblem.taskResidual,
    Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSubDiff, pow_one, mul_one, mul_zero, add_zero, hstate] using
    hresidual.add hsupervised

/-- The feedforward active field is the derivative of the feedforward energy,
not the recurrent field reused under another treatment label. -/
theorem ScalarPCProblem.hasDerivAt_feedforwardEnergy_activePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.feedforwardActiveEnergyPath state)
      (problem.feedforwardActiveStateGradient state) state.active := by
  have hactive := hasDerivAt_activeResidual_activePath problem state
  have hevidence : HasDerivAt
      (fun active => problem.feedforwardEvidenceResidual
        { active := active, evidence := state.evidence })
      0 state.active := by
    simpa only [ScalarPCProblem.feedforwardEvidenceResidual] using
      (hasDerivAt_const state.active
        (state.evidence - problem.feedforwardEvidencePrediction))
  have htask := hasDerivAt_taskResidual_activePath problem state
  have hresidual :=
    ((hactive.pow 2).add (hevidence.pow 2)).const_mul
      (problem.residualPrecision / 2)
  have hsupervised := (htask.pow 2).const_mul (problem.taskPrecision / 2)
  have hstate :
      ({ active := state.active, evidence := state.evidence } : TwoNodeState) =
        state := by
    cases state
    rfl
  simpa only [ScalarPCProblem.feedforwardActiveEnergyPath,
    ScalarPCProblem.feedforwardActiveStateGradient, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_one, hstate] using
    hresidual.add hsupervised

/-- The feedforward evidence field is likewise the exact energy partial. -/
theorem ScalarPCProblem.hasDerivAt_feedforwardEnergy_evidencePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.feedforwardEvidenceEnergyPath state)
      (problem.feedforwardEvidenceStateGradient state) state.evidence := by
  have hactive := hasDerivAt_activeResidual_evidencePath problem state
  have hevidence : HasDerivAt
      (fun evidence => problem.feedforwardEvidenceResidual
        { active := state.active, evidence := evidence })
      1 state.evidence := by
    simpa [ScalarPCProblem.feedforwardEvidenceResidual] using
      (hasDerivAt_id state.evidence).sub_const
        problem.feedforwardEvidencePrediction
  have htask : HasDerivAt
      (fun _evidence : ℝ => problem.taskResidual state) 0 state.evidence :=
    hasDerivAt_const state.evidence _
  have hresidual :=
    ((hactive.pow 2).add (hevidence.pow 2)).const_mul
      (problem.residualPrecision / 2)
  have hsupervised := (htask.pow 2).const_mul (problem.taskPrecision / 2)
  have hstate :
      ({ active := state.active, evidence := state.evidence } : TwoNodeState) =
        state := by
    cases state
    rfl
  simpa only [ScalarPCProblem.feedforwardEvidenceEnergyPath,
    ScalarPCProblem.feedforwardEvidenceStateGradient,
    ScalarPCProblem.taskResidual, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSubDiff, pow_one, mul_one, mul_zero, add_zero, hstate] using
    hresidual.add hsupervised

/-- One simultaneous local inference step.  Slow parameters are not modified
inside this map. -/
def ScalarPCProblem.inferenceStep
    (problem : ScalarPCProblem) (rate : ℝ) (state : TwoNodeState) : TwoNodeState where
  active := state.active - rate * problem.activeStateGradient state
  evidence := state.evidence - rate * problem.evidenceStateGradient state

def ScalarPCProblem.stateGradientFor
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (state : TwoNodeState) : TwoNodeState :=
  match dynamics with
  | .feedforward =>
      { active := problem.feedforwardActiveStateGradient state
        evidence := problem.feedforwardEvidenceStateGradient state }
  | .equilibrium =>
      { active := problem.activeStateGradient state
        evidence := problem.evidenceStateGradient state }

/-- Source-level update used by both factorial cells.  Treatment selection
changes the energy field before the Euler step; it is not metadata attached to
one shared update. -/
def ScalarPCProblem.inferenceStepFor
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (rate : ℝ) (state : TwoNodeState) : TwoNodeState :=
  let gradient := problem.stateGradientFor dynamics state
  { active := state.active - rate * gradient.active
    evidence := state.evidence - rate * gradient.evidence }

@[simp] theorem ScalarPCProblem.inferenceStepFor_equilibrium
    (problem : ScalarPCProblem) (rate : ℝ) (state : TwoNodeState) :
    problem.inferenceStepFor .equilibrium rate state =
      problem.inferenceStep rate state := rfl

/-- Detached partial derivatives with respect to the five trainable scalar
families represented by this coordinate. -/
structure LocalParameterGradient where
  activeDrive : ℝ
  evidenceDrive : ℝ
  activeCoupling : ℝ
  evidenceCoupling : ℝ
  readoutWeight : ℝ
deriving DecidableEq

def ScalarPCProblem.detachedParameterGradient
    (problem : ScalarPCProblem) (state : TwoNodeState) : LocalParameterGradient where
  activeDrive := -problem.residualPrecision * problem.activeResidual state *
    tanhSlope (problem.activeDrive + problem.activeCoupling * state.evidence)
  evidenceDrive := -problem.residualPrecision * problem.evidenceResidual state *
    tanhSlope (problem.evidenceDrive + problem.evidenceCoupling * state.active)
  activeCoupling := -problem.residualPrecision * problem.activeResidual state *
    tanhSlope (problem.activeDrive + problem.activeCoupling * state.evidence) *
      state.evidence
  evidenceCoupling := -problem.residualPrecision * problem.evidenceResidual state *
    tanhSlope (problem.evidenceDrive + problem.evidenceCoupling * state.active) *
      state.active
  readoutWeight := problem.taskPrecision * problem.taskResidual state * state.active

/-- Detached parameter credit for the acyclic residual graph.  The active
drive has a second local path through the frozen parent of the evidence node;
that term is absent in the recurrent formula, where the live active state is
detached during parameter differentiation. -/
def ScalarPCProblem.feedforwardDetachedParameterGradient
    (problem : ScalarPCProblem) (state : TwoNodeState) : LocalParameterGradient where
  activeDrive :=
    -problem.residualPrecision * problem.activeResidual state *
        tanhSlope (problem.activeDrive + problem.activeCoupling * state.evidence) -
      problem.residualPrecision * problem.feedforwardEvidenceResidual state *
        tanhSlope
          (problem.evidenceDrive +
            problem.evidenceCoupling * Real.tanh problem.activeDrive) *
        problem.evidenceCoupling * tanhSlope problem.activeDrive
  evidenceDrive :=
    -problem.residualPrecision * problem.feedforwardEvidenceResidual state *
      tanhSlope
        (problem.evidenceDrive +
          problem.evidenceCoupling * Real.tanh problem.activeDrive)
  activeCoupling :=
    -problem.residualPrecision * problem.activeResidual state *
      tanhSlope (problem.activeDrive + problem.activeCoupling * state.evidence) *
        state.evidence
  evidenceCoupling :=
    -problem.residualPrecision * problem.feedforwardEvidenceResidual state *
      tanhSlope
        (problem.evidenceDrive +
          problem.evidenceCoupling * Real.tanh problem.activeDrive) *
        Real.tanh problem.activeDrive
  readoutWeight := problem.taskPrecision * problem.taskResidual state * state.active

def ScalarPCProblem.detachedParameterGradientFor
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (state : TwoNodeState) : LocalParameterGradient :=
  match dynamics with
  | .feedforward => problem.feedforwardDetachedParameterGradient state
  | .equilibrium => problem.detachedParameterGradient state

@[simp] theorem ScalarPCProblem.detachedParameterGradientFor_equilibrium
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    problem.detachedParameterGradientFor .equilibrium state =
      problem.detachedParameterGradient state := rfl

def ScalarPCProblem.activeDriveEnergyPath
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (state : TwoNodeState) : ℝ → ℝ :=
  match dynamics with
  | .feedforward => fun value =>
      problem.residualPrecision / 2 *
        ((state.active - Real.tanh
            (value + problem.activeCoupling * state.evidence)) ^ 2 +
          (state.evidence - Real.tanh
            (problem.evidenceDrive +
              problem.evidenceCoupling * Real.tanh value)) ^ 2) +
        problem.taskPrecision / 2 * problem.taskResidual state ^ 2
  | .equilibrium => fun value =>
      problem.residualPrecision / 2 *
          (((fun activeDrive => state.active - Real.tanh
              (activeDrive + problem.activeCoupling * state.evidence)) ^ 2 +
            (fun _activeDrive : ℝ => problem.evidenceResidual state) ^ 2) value) +
        problem.taskPrecision / 2 *
          ((fun _activeDrive : ℝ => problem.taskResidual state) ^ 2) value

def ScalarPCProblem.evidenceDriveEnergyPath
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (state : TwoNodeState) : ℝ → ℝ :=
  fun value =>
    problem.residualPrecision / 2 *
      (problem.activeResidual state ^ 2 +
        (state.evidence - Real.tanh
          (value + problem.evidenceCoupling *
            (match dynamics with
             | .feedforward => Real.tanh problem.activeDrive
             | .equilibrium => state.active))) ^ 2) +
      problem.taskPrecision / 2 * problem.taskResidual state ^ 2

def ScalarPCProblem.activeCouplingEnergyPath
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (state : TwoNodeState) : ℝ → ℝ :=
  fun value =>
    problem.residualPrecision / 2 *
      ((state.active - Real.tanh
          (problem.activeDrive + value * state.evidence)) ^ 2 +
        problem.evidenceResidualFor dynamics state ^ 2) +
      problem.taskPrecision / 2 * problem.taskResidual state ^ 2

def ScalarPCProblem.evidenceCouplingEnergyPath
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (state : TwoNodeState) : ℝ → ℝ :=
  fun value =>
    problem.residualPrecision / 2 *
      (problem.activeResidual state ^ 2 +
        (state.evidence - Real.tanh
          (problem.evidenceDrive + value *
            (match dynamics with
             | .feedforward => Real.tanh problem.activeDrive
             | .equilibrium => state.active))) ^ 2) +
      problem.taskPrecision / 2 * problem.taskResidual state ^ 2

def ScalarPCProblem.readoutWeightEnergyPath
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (state : TwoNodeState) : ℝ → ℝ :=
  fun value =>
    problem.residualPrecision / 2 *
      (problem.activeResidual state ^ 2 +
        problem.evidenceResidualFor dynamics state ^ 2) +
      problem.taskPrecision / 2 *
        (value * state.active - problem.target) ^ 2

/-- Reusable derivative rule for the three-term local energy.  This is the
single algebraic bridge used by all five parameter-coordinate certificates. -/
theorem hasDerivAt_weightedResidualEnergy
    (residualPrecision taskPrecision point : ℝ)
    (activeResidual evidenceResidual taskResidual : ℝ → ℝ)
    (activeDerivative evidenceDerivative taskDerivative : ℝ)
    (hactive : HasDerivAt activeResidual activeDerivative point)
    (hevidence : HasDerivAt evidenceResidual evidenceDerivative point)
    (htask : HasDerivAt taskResidual taskDerivative point) :
    RealEnergyHasDerivAt
      (fun value => residualPrecision / 2 *
          (activeResidual value ^ 2 + evidenceResidual value ^ 2) +
        taskPrecision / 2 * taskResidual value ^ 2)
      (residualPrecision *
          (activeResidual point * activeDerivative +
            evidenceResidual point * evidenceDerivative) +
        taskPrecision * taskResidual point * taskDerivative)
      point := by
  have henergy :=
    (((hactive.pow 2).add (hevidence.pow 2)).const_mul
      (residualPrecision / 2)).add
        ((htask.pow 2).const_mul (taskPrecision / 2))
  apply henergy.congr_deriv
  simp
  ring

/-- The equilibrium active-drive credit is the exact detached energy partial. -/
theorem ScalarPCProblem.hasDerivAt_equilibriumEnergy_activeDrivePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.activeDriveEnergyPath .equilibrium state)
      (problem.detachedParameterGradient state).activeDrive
      problem.activeDrive := by
  have hinner : HasDerivAt
      (fun value => value + problem.activeCoupling * state.evidence)
      1 problem.activeDrive :=
    (hasDerivAt_id problem.activeDrive).add_const _
  have htanh := (hasDerivAt_tanh_localEnergy
    (problem.activeDrive + problem.activeCoupling * state.evidence)).comp
      problem.activeDrive hinner
  have htanh' : HasDerivAt
      (fun value => Real.tanh
        (value + problem.activeCoupling * state.evidence))
      (tanhSlope
        (problem.activeDrive + problem.activeCoupling * state.evidence))
      problem.activeDrive := by
    simpa [Function.comp_def] using
      htanh.congr_deriv (by ring)
  have hactive : HasDerivAt
      (fun value => state.active -
        Real.tanh (value + problem.activeCoupling * state.evidence))
      (-tanhSlope
        (problem.activeDrive + problem.activeCoupling * state.evidence))
      problem.activeDrive := by
    simpa [sub_eq_add_neg] using htanh'.neg.const_add state.active
  have hevidence : HasDerivAt
      (fun _value : ℝ => problem.evidenceResidual state) 0
      problem.activeDrive := hasDerivAt_const _ _
  have htask : HasDerivAt
      (fun _value : ℝ => problem.taskResidual state) 0
      problem.activeDrive := hasDerivAt_const _ _
  have henergy :=
    (((hactive.pow 2).add (hevidence.pow 2)).const_mul
      (problem.residualPrecision / 2)).add
        ((htask.pow 2).const_mul (problem.taskPrecision / 2))
  have henergy' : RealEnergyHasDerivAt
      ((fun y => problem.residualPrecision / 2 *
          ((fun value => state.active - Real.tanh
              (value + problem.activeCoupling * state.evidence)) ^ 2 +
            (fun _value : ℝ => problem.evidenceResidual state) ^ 2) y) +
        fun y => problem.taskPrecision / 2 *
          ((fun _value : ℝ => problem.taskResidual state) ^ 2) y)
      (problem.detachedParameterGradient state).activeDrive
      problem.activeDrive := by
    apply henergy.congr_deriv
    simp [ScalarPCProblem.detachedParameterGradient,
      ScalarPCProblem.activeResidual, ScalarPCProblem.activePrediction]
    ring
  apply henergy'.congr_of_eventuallyEq
  filter_upwards with value
  rfl

theorem ScalarPCProblem.hasDerivAt_equilibriumEnergy_evidenceDrivePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.evidenceDriveEnergyPath .equilibrium state)
      (problem.detachedParameterGradient state).evidenceDrive
      problem.evidenceDrive := by
  have hinner : HasDerivAt
      (fun value => value + problem.evidenceCoupling * state.active)
      1 problem.evidenceDrive :=
    (hasDerivAt_id problem.evidenceDrive).add_const _
  have htanh := (hasDerivAt_tanh_localEnergy
    (problem.evidenceDrive + problem.evidenceCoupling * state.active)).comp
      problem.evidenceDrive hinner
  have htanh' : HasDerivAt
      (fun value => Real.tanh
        (value + problem.evidenceCoupling * state.active))
      (tanhSlope
        (problem.evidenceDrive + problem.evidenceCoupling * state.active))
      problem.evidenceDrive := by
    simpa [Function.comp_def] using htanh.congr_deriv (by ring)
  have hevidence : HasDerivAt
      (fun value => state.evidence -
        Real.tanh (value + problem.evidenceCoupling * state.active))
      (-tanhSlope
        (problem.evidenceDrive + problem.evidenceCoupling * state.active))
      problem.evidenceDrive := by
    simpa [sub_eq_add_neg] using htanh'.neg.const_add state.evidence
  have henergy := hasDerivAt_weightedResidualEnergy
    problem.residualPrecision problem.taskPrecision problem.evidenceDrive
    (fun _value => problem.activeResidual state)
    (fun value => state.evidence -
      Real.tanh (value + problem.evidenceCoupling * state.active))
    (fun _value => problem.taskResidual state)
    0 (-tanhSlope
      (problem.evidenceDrive + problem.evidenceCoupling * state.active)) 0
    (hasDerivAt_const _ _) hevidence (hasDerivAt_const _ _)
  convert henergy using 1
  · rfl
  · simp [ScalarPCProblem.detachedParameterGradient,
      ScalarPCProblem.evidenceResidual, ScalarPCProblem.evidencePrediction]
    ring

theorem ScalarPCProblem.hasDerivAt_equilibriumEnergy_activeCouplingPath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.activeCouplingEnergyPath .equilibrium state)
      (problem.detachedParameterGradient state).activeCoupling
      problem.activeCoupling := by
  have hinner : HasDerivAt
      (fun value => problem.activeDrive + value * state.evidence)
      state.evidence problem.activeCoupling := by
    simpa [add_comm] using
      ((hasDerivAt_id problem.activeCoupling).mul_const
        state.evidence).const_add problem.activeDrive
  have htanh := (hasDerivAt_tanh_localEnergy
    (problem.activeDrive + problem.activeCoupling * state.evidence)).comp
      problem.activeCoupling hinner
  have htanh' : HasDerivAt
      (fun value => Real.tanh
        (problem.activeDrive + value * state.evidence))
      (tanhSlope
          (problem.activeDrive + problem.activeCoupling * state.evidence) *
        state.evidence) problem.activeCoupling := by
    simpa [Function.comp_def] using htanh
  have hactive : HasDerivAt
      (fun value => state.active -
        Real.tanh (problem.activeDrive + value * state.evidence))
      (-(tanhSlope
          (problem.activeDrive + problem.activeCoupling * state.evidence) *
        state.evidence)) problem.activeCoupling := by
    simpa [sub_eq_add_neg] using htanh'.neg.const_add state.active
  have henergy := hasDerivAt_weightedResidualEnergy
    problem.residualPrecision problem.taskPrecision problem.activeCoupling
    (fun value => state.active -
      Real.tanh (problem.activeDrive + value * state.evidence))
    (fun _value => problem.evidenceResidual state)
    (fun _value => problem.taskResidual state)
    (-(tanhSlope
        (problem.activeDrive + problem.activeCoupling * state.evidence) *
      state.evidence)) 0 0 hactive (hasDerivAt_const _ _)
      (hasDerivAt_const _ _)
  convert henergy using 1
  · rfl
  · simp [ScalarPCProblem.detachedParameterGradient,
      ScalarPCProblem.activeResidual, ScalarPCProblem.activePrediction]
    ring

theorem ScalarPCProblem.hasDerivAt_equilibriumEnergy_evidenceCouplingPath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.evidenceCouplingEnergyPath .equilibrium state)
      (problem.detachedParameterGradient state).evidenceCoupling
      problem.evidenceCoupling := by
  have hinner : HasDerivAt
      (fun value => problem.evidenceDrive + value * state.active)
      state.active problem.evidenceCoupling := by
    simpa [add_comm] using
      ((hasDerivAt_id problem.evidenceCoupling).mul_const
        state.active).const_add problem.evidenceDrive
  have htanh := (hasDerivAt_tanh_localEnergy
    (problem.evidenceDrive + problem.evidenceCoupling * state.active)).comp
      problem.evidenceCoupling hinner
  have htanh' : HasDerivAt
      (fun value => Real.tanh
        (problem.evidenceDrive + value * state.active))
      (tanhSlope
          (problem.evidenceDrive + problem.evidenceCoupling * state.active) *
        state.active) problem.evidenceCoupling := by
    simpa [Function.comp_def] using htanh
  have hevidence : HasDerivAt
      (fun value => state.evidence -
        Real.tanh (problem.evidenceDrive + value * state.active))
      (-(tanhSlope
          (problem.evidenceDrive + problem.evidenceCoupling * state.active) *
        state.active)) problem.evidenceCoupling := by
    simpa [sub_eq_add_neg] using htanh'.neg.const_add state.evidence
  have henergy := hasDerivAt_weightedResidualEnergy
    problem.residualPrecision problem.taskPrecision problem.evidenceCoupling
    (fun _value => problem.activeResidual state)
    (fun value => state.evidence -
      Real.tanh (problem.evidenceDrive + value * state.active))
    (fun _value => problem.taskResidual state)
    0 (-(tanhSlope
      (problem.evidenceDrive + problem.evidenceCoupling * state.active) *
      state.active)) 0 (hasDerivAt_const _ _) hevidence
      (hasDerivAt_const _ _)
  convert henergy using 1
  · rfl
  · simp [ScalarPCProblem.detachedParameterGradient,
      ScalarPCProblem.evidenceResidual, ScalarPCProblem.evidencePrediction]
    ring

theorem ScalarPCProblem.hasDerivAt_equilibriumEnergy_readoutWeightPath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.readoutWeightEnergyPath .equilibrium state)
      (problem.detachedParameterGradient state).readoutWeight
      problem.readoutWeight := by
  have htask : HasDerivAt
      (fun value => value * state.active - problem.target)
      state.active problem.readoutWeight := by
    simpa using
      ((hasDerivAt_id problem.readoutWeight).mul_const state.active).sub_const
        problem.target
  have henergy := hasDerivAt_weightedResidualEnergy
    problem.residualPrecision problem.taskPrecision problem.readoutWeight
    (fun _value => problem.activeResidual state)
    (fun _value => problem.evidenceResidual state)
    (fun value => value * state.active - problem.target)
    0 0 state.active (hasDerivAt_const _ _) (hasDerivAt_const _ _) htask
  convert henergy using 1
  · rfl
  · simp [ScalarPCProblem.detachedParameterGradient,
      ScalarPCProblem.taskResidual]

theorem ScalarPCProblem.hasDerivAt_feedforwardEnergy_evidenceDrivePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.evidenceDriveEnergyPath .feedforward state)
      (problem.feedforwardDetachedParameterGradient state).evidenceDrive
      problem.evidenceDrive := by
  let parent := Real.tanh problem.activeDrive
  have hinner : HasDerivAt
      (fun value => value + problem.evidenceCoupling * parent)
      1 problem.evidenceDrive :=
    (hasDerivAt_id problem.evidenceDrive).add_const _
  have htanh := (hasDerivAt_tanh_localEnergy
    (problem.evidenceDrive + problem.evidenceCoupling * parent)).comp
      problem.evidenceDrive hinner
  have htanh' : HasDerivAt
      (fun value => Real.tanh
        (value + problem.evidenceCoupling * parent))
      (tanhSlope
        (problem.evidenceDrive + problem.evidenceCoupling * parent))
      problem.evidenceDrive := by
    simpa [Function.comp_def] using htanh.congr_deriv (by ring)
  have hevidence : HasDerivAt
      (fun value => state.evidence -
        Real.tanh (value + problem.evidenceCoupling * parent))
      (-tanhSlope
        (problem.evidenceDrive + problem.evidenceCoupling * parent))
      problem.evidenceDrive := by
    simpa [sub_eq_add_neg] using htanh'.neg.const_add state.evidence
  have henergy := hasDerivAt_weightedResidualEnergy
    problem.residualPrecision problem.taskPrecision problem.evidenceDrive
    (fun _value => problem.activeResidual state)
    (fun value => state.evidence -
      Real.tanh (value + problem.evidenceCoupling * parent))
    (fun _value => problem.taskResidual state)
    0 (-tanhSlope
      (problem.evidenceDrive + problem.evidenceCoupling * parent)) 0
    (hasDerivAt_const _ _) hevidence (hasDerivAt_const _ _)
  convert henergy using 1
  · rfl
  · simp [ScalarPCProblem.feedforwardDetachedParameterGradient,
      ScalarPCProblem.feedforwardEvidenceResidual,
      ScalarPCProblem.feedforwardEvidencePrediction, parent]
    ring

theorem ScalarPCProblem.hasDerivAt_feedforwardEnergy_activeCouplingPath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.activeCouplingEnergyPath .feedforward state)
      (problem.feedforwardDetachedParameterGradient state).activeCoupling
      problem.activeCoupling := by
  have hinner : HasDerivAt
      (fun value => problem.activeDrive + value * state.evidence)
      state.evidence problem.activeCoupling := by
    simpa [add_comm] using
      ((hasDerivAt_id problem.activeCoupling).mul_const
        state.evidence).const_add problem.activeDrive
  have htanh := (hasDerivAt_tanh_localEnergy
    (problem.activeDrive + problem.activeCoupling * state.evidence)).comp
      problem.activeCoupling hinner
  have htanh' : HasDerivAt
      (fun value => Real.tanh
        (problem.activeDrive + value * state.evidence))
      (tanhSlope
          (problem.activeDrive + problem.activeCoupling * state.evidence) *
        state.evidence) problem.activeCoupling := by
    simpa [Function.comp_def] using htanh
  have hactive : HasDerivAt
      (fun value => state.active -
        Real.tanh (problem.activeDrive + value * state.evidence))
      (-(tanhSlope
          (problem.activeDrive + problem.activeCoupling * state.evidence) *
        state.evidence)) problem.activeCoupling := by
    simpa [sub_eq_add_neg] using htanh'.neg.const_add state.active
  have henergy := hasDerivAt_weightedResidualEnergy
    problem.residualPrecision problem.taskPrecision problem.activeCoupling
    (fun value => state.active -
      Real.tanh (problem.activeDrive + value * state.evidence))
    (fun _value => problem.feedforwardEvidenceResidual state)
    (fun _value => problem.taskResidual state)
    (-(tanhSlope
        (problem.activeDrive + problem.activeCoupling * state.evidence) *
      state.evidence)) 0 0 hactive (hasDerivAt_const _ _)
      (hasDerivAt_const _ _)
  convert henergy using 1
  · rfl
  · simp [ScalarPCProblem.feedforwardDetachedParameterGradient,
      ScalarPCProblem.activeResidual, ScalarPCProblem.activePrediction]
    ring

theorem ScalarPCProblem.hasDerivAt_feedforwardEnergy_evidenceCouplingPath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.evidenceCouplingEnergyPath .feedforward state)
      (problem.feedforwardDetachedParameterGradient state).evidenceCoupling
      problem.evidenceCoupling := by
  let parent := Real.tanh problem.activeDrive
  have hinner : HasDerivAt
      (fun value => problem.evidenceDrive + value * parent)
      parent problem.evidenceCoupling := by
    simpa [add_comm] using
      ((hasDerivAt_id problem.evidenceCoupling).mul_const parent).const_add
        problem.evidenceDrive
  have htanh := (hasDerivAt_tanh_localEnergy
    (problem.evidenceDrive + problem.evidenceCoupling * parent)).comp
      problem.evidenceCoupling hinner
  have htanh' : HasDerivAt
      (fun value => Real.tanh (problem.evidenceDrive + value * parent))
      (tanhSlope
          (problem.evidenceDrive + problem.evidenceCoupling * parent) * parent)
      problem.evidenceCoupling := by
    simpa [Function.comp_def] using htanh
  have hevidence : HasDerivAt
      (fun value => state.evidence -
        Real.tanh (problem.evidenceDrive + value * parent))
      (-(tanhSlope
          (problem.evidenceDrive + problem.evidenceCoupling * parent) * parent))
      problem.evidenceCoupling := by
    simpa [sub_eq_add_neg] using htanh'.neg.const_add state.evidence
  have henergy := hasDerivAt_weightedResidualEnergy
    problem.residualPrecision problem.taskPrecision problem.evidenceCoupling
    (fun _value => problem.activeResidual state)
    (fun value => state.evidence -
      Real.tanh (problem.evidenceDrive + value * parent))
    (fun _value => problem.taskResidual state)
    0 (-(tanhSlope
      (problem.evidenceDrive + problem.evidenceCoupling * parent) * parent)) 0
    (hasDerivAt_const _ _) hevidence (hasDerivAt_const _ _)
  convert henergy using 1
  · rfl
  · simp [ScalarPCProblem.feedforwardDetachedParameterGradient,
      ScalarPCProblem.feedforwardEvidenceResidual,
      ScalarPCProblem.feedforwardEvidencePrediction, parent]
    ring

theorem ScalarPCProblem.hasDerivAt_feedforwardEnergy_readoutWeightPath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.readoutWeightEnergyPath .feedforward state)
      (problem.feedforwardDetachedParameterGradient state).readoutWeight
      problem.readoutWeight := by
  have htask : HasDerivAt
      (fun value => value * state.active - problem.target)
      state.active problem.readoutWeight := by
    simpa using
      ((hasDerivAt_id problem.readoutWeight).mul_const state.active).sub_const
        problem.target
  have henergy := hasDerivAt_weightedResidualEnergy
    problem.residualPrecision problem.taskPrecision problem.readoutWeight
    (fun _value => problem.activeResidual state)
    (fun _value => problem.feedforwardEvidenceResidual state)
    (fun value => value * state.active - problem.target)
    0 0 state.active (hasDerivAt_const _ _) (hasDerivAt_const _ _) htask
  convert henergy using 1
  · rfl
  · simp [ScalarPCProblem.feedforwardDetachedParameterGradient,
      ScalarPCProblem.taskResidual]

theorem ScalarPCProblem.hasDerivAt_feedforwardEnergy_activeDrivePath
    (problem : ScalarPCProblem) (state : TwoNodeState) :
    RealEnergyHasDerivAt
      (problem.activeDriveEnergyPath .feedforward state)
      (problem.feedforwardDetachedParameterGradient state).activeDrive
      problem.activeDrive := by
  have hactiveInner : HasDerivAt
      (fun value => value + problem.activeCoupling * state.evidence)
      1 problem.activeDrive :=
    (hasDerivAt_id problem.activeDrive).add_const _
  have hactiveTanh := (hasDerivAt_tanh_localEnergy
    (problem.activeDrive + problem.activeCoupling * state.evidence)).comp
      problem.activeDrive hactiveInner
  have hactiveTanh' : HasDerivAt
      (fun value => Real.tanh
        (value + problem.activeCoupling * state.evidence))
      (tanhSlope
        (problem.activeDrive + problem.activeCoupling * state.evidence))
      problem.activeDrive := by
    simpa [Function.comp_def] using hactiveTanh.congr_deriv (by ring)
  have hactive : HasDerivAt
      (fun value => state.active -
        Real.tanh (value + problem.activeCoupling * state.evidence))
      (-tanhSlope
        (problem.activeDrive + problem.activeCoupling * state.evidence))
      problem.activeDrive := by
    simpa [sub_eq_add_neg] using hactiveTanh'.neg.const_add state.active
  have hparent := hasDerivAt_tanh_localEnergy problem.activeDrive
  have hevidenceInner : HasDerivAt
      (fun value => problem.evidenceDrive +
        problem.evidenceCoupling * Real.tanh value)
      (problem.evidenceCoupling * tanhSlope problem.activeDrive)
      problem.activeDrive := by
    simpa [add_comm] using
      (hparent.const_mul problem.evidenceCoupling).const_add
        problem.evidenceDrive
  have hevidenceTanh := (hasDerivAt_tanh_localEnergy
    (problem.evidenceDrive +
      problem.evidenceCoupling * Real.tanh problem.activeDrive)).comp
      problem.activeDrive hevidenceInner
  have hevidenceTanh' : HasDerivAt
      (fun value => Real.tanh
        (problem.evidenceDrive +
          problem.evidenceCoupling * Real.tanh value))
      (tanhSlope
          (problem.evidenceDrive +
            problem.evidenceCoupling * Real.tanh problem.activeDrive) *
        (problem.evidenceCoupling * tanhSlope problem.activeDrive))
      problem.activeDrive := by
    simpa [Function.comp_def] using hevidenceTanh
  have hevidence : HasDerivAt
      (fun value => state.evidence - Real.tanh
        (problem.evidenceDrive + problem.evidenceCoupling * Real.tanh value))
      (-(tanhSlope
          (problem.evidenceDrive +
            problem.evidenceCoupling * Real.tanh problem.activeDrive) *
        (problem.evidenceCoupling * tanhSlope problem.activeDrive)))
      problem.activeDrive := by
    simpa [sub_eq_add_neg] using hevidenceTanh'.neg.const_add state.evidence
  have henergy := hasDerivAt_weightedResidualEnergy
    problem.residualPrecision problem.taskPrecision problem.activeDrive
    (fun value => state.active -
      Real.tanh (value + problem.activeCoupling * state.evidence))
    (fun value => state.evidence - Real.tanh
      (problem.evidenceDrive + problem.evidenceCoupling * Real.tanh value))
    (fun _value => problem.taskResidual state)
    (-tanhSlope
      (problem.activeDrive + problem.activeCoupling * state.evidence))
    (-(tanhSlope
        (problem.evidenceDrive +
          problem.evidenceCoupling * Real.tanh problem.activeDrive) *
      (problem.evidenceCoupling * tanhSlope problem.activeDrive))) 0
    hactive hevidence (hasDerivAt_const _ _)
  convert henergy using 1
  · rfl
  · simp [ScalarPCProblem.feedforwardDetachedParameterGradient,
      ScalarPCProblem.activeResidual, ScalarPCProblem.activePrediction,
      ScalarPCProblem.feedforwardEvidenceResidual,
      ScalarPCProblem.feedforwardEvidencePrediction]
    ring

/-- History-indexed readout used to state the non-unrolling boundary without
retaining the intermediate trajectory. -/
def detachedGradientOfHistory
    (problem : ScalarPCProblem) (fallback : TwoNodeState)
    (history : List TwoNodeState) : LocalParameterGradient :=
  problem.detachedParameterGradient (history.getLast?.getD fallback)

def detachedGradientOfHistoryFor
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (fallback : TwoNodeState) (history : List TwoNodeState) :
    LocalParameterGradient :=
  problem.detachedParameterGradientFor dynamics
    (history.getLast?.getD fallback)

theorem detachedGradientOfHistory_eq_of_equal_endpoint
    (problem : ScalarPCProblem) (fallback : TwoNodeState)
    (firstHistory secondHistory : List TwoNodeState)
    (hendpoint : firstHistory.getLast? = secondHistory.getLast?) :
    detachedGradientOfHistory problem fallback firstHistory =
      detachedGradientOfHistory problem fallback secondHistory := by
  simp [detachedGradientOfHistory, hendpoint]

theorem detachedGradientOfHistoryFor_eq_of_equal_endpoint
    (problem : ScalarPCProblem) (dynamics : ReasonerDynamics)
    (fallback : TwoNodeState) (firstHistory secondHistory : List TwoNodeState)
    (hendpoint : firstHistory.getLast? = secondHistory.getLast?) :
    detachedGradientOfHistoryFor problem dynamics fallback firstHistory =
      detachedGradientOfHistoryFor problem dynamics fallback secondHistory := by
  simp [detachedGradientOfHistoryFor, hendpoint]

/-- Negative fixture: equal initial states do not identify finite local credit
when the inference endpoints differ. -/
theorem different_endpoints_can_change_detached_credit :
    let problem : ScalarPCProblem :=
      { activeDrive := 0, evidenceDrive := 0
        activeCoupling := 0, evidenceCoupling := 0
        readoutWeight := 1, target := 1
        residualPrecision := 1, taskPrecision := 1 }
    let left : TwoNodeState := { active := 0, evidence := 0 }
    let right : TwoNodeState := { active := 1, evidence := 0 }
    problem.detachedParameterGradient left ≠
      problem.detachedParameterGradient right := by
  dsimp
  intro h
  have := congrArg LocalParameterGradient.activeDrive h
  norm_num [ScalarPCProblem.detachedParameterGradient,
    ScalarPCProblem.activeResidual, ScalarPCProblem.activePrediction,
    ScalarPCProblem.taskResidual, tanhSlope] at this

#print axioms ScalarPCProblem.hasDerivAt_energy_activePath
#print axioms ScalarPCProblem.hasDerivAt_energy_evidencePath
#print axioms ScalarPCProblem.hasDerivAt_feedforwardEnergy_activePath
#print axioms ScalarPCProblem.hasDerivAt_feedforwardEnergy_evidencePath
#print axioms ScalarPCProblem.hasDerivAt_equilibriumEnergy_activeDrivePath
#print axioms ScalarPCProblem.hasDerivAt_equilibriumEnergy_evidenceDrivePath
#print axioms ScalarPCProblem.hasDerivAt_equilibriumEnergy_activeCouplingPath
#print axioms ScalarPCProblem.hasDerivAt_equilibriumEnergy_evidenceCouplingPath
#print axioms ScalarPCProblem.hasDerivAt_equilibriumEnergy_readoutWeightPath
#print axioms ScalarPCProblem.hasDerivAt_feedforwardEnergy_activeDrivePath
#print axioms ScalarPCProblem.hasDerivAt_feedforwardEnergy_evidenceDrivePath
#print axioms ScalarPCProblem.hasDerivAt_feedforwardEnergy_activeCouplingPath
#print axioms ScalarPCProblem.hasDerivAt_feedforwardEnergy_evidenceCouplingPath
#print axioms ScalarPCProblem.hasDerivAt_feedforwardEnergy_readoutWeightPath
#print axioms detachedGradientOfHistory_eq_of_equal_endpoint
#print axioms detachedGradientOfHistoryFor_eq_of_equal_endpoint
#print axioms different_endpoints_can_change_detached_credit

end

end ActionMemoryLocalPC
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
