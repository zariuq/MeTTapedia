import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.Regime

/-!
# Concrete outcome semantics for the utilization atlas

This file supplies the architecture-neutral substrate for comparing predictive
coding, workspace, and belief-state policies.  A utilization problem contains
an actual reference transition, a finite task/observation trace, task losses,
resource limits, and a legal-action wrapper.  An architecture contains its
actual update and action policy.  Outcomes are computed by running those
transitions; architecture names do not determine performance.

Comparison is Pareto comparison of risk, forgetting, inference, communication,
and state costs.  No arbitrary scalar exchange rate between those quantities is
chosen.  Safety is a qualification rather than a numerical reward.  The scope
here is a finite deterministic trace with real-valued losses and natural-number
resource accounting; later files instantiate it with linear, quadratic,
linear-Gaussian, and finite-mixture models.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

universe uState uObservation uTask uAction

/-! ## Problems, policies, and their computed runs -/

/-- A finite deterministic utilization problem.  The reference dynamics say
how the modeled state should respond to each task/observation event. -/
structure UtilizationProblem
    (State : Type uState) (Observation : Type uObservation)
    (Task : Type uTask) (Action : Type uAction) where
  referenceUpdate : Task → State → Observation → State
  trainingEvents : List (Task × Observation)
  initialState : State
  estimationLoss : State → State → ℝ
  taskLoss : Task → State → ℝ
  sourceTask : Task
  topology : TopologyKind
  availableBandwidth : ℕ
  inferenceBudget : ℕ
  communicationUnitCost : ℕ
  stateUnitCost : ℕ
  legalAction : State → Action → Prop
  checkerAccepts : State → Action → Prop
  legalAction_sound :
    ∀ state action, legalAction state action → checkerAccepts state action

/-- The task sequence is carried by the event trace and exposed explicitly for
task-order diagnostics. -/
def UtilizationProblem.taskSequence
    {State : Type uState} {Observation : Type uObservation}
    {Task : Type uTask} {Action : Type uAction}
    (problem : UtilizationProblem State Observation Task Action) : List Task :=
  problem.trainingEvents.map Prod.fst

/-- A concrete architecture/configuration: an update, an action readout, and
the resources used for one event. -/
structure ArchitecturePolicy
    {State : Type uState} {Observation : Type uObservation}
    {Task : Type uTask} {Action : Type uAction}
    (problem : UtilizationProblem State Observation Task Action) where
  update : Task → State → Observation → State
  selectAction : State → Action
  requiredBandwidth : ℕ
  roundsPerEvent : ℕ
  workPerRound : ℕ
  messagesPerRound : ℕ
  stateDimension : ℕ

/-- Run either the reference dynamics or an architecture update over the
problem's concrete event sequence. -/
def UtilizationProblem.runWith
    {State : Type uState} {Observation : Type uObservation}
    {Task : Type uTask} {Action : Type uAction}
    (problem : UtilizationProblem State Observation Task Action)
    (update : Task → State → Observation → State) : State :=
  problem.trainingEvents.foldl
    (fun state event => update event.1 state event.2)
    problem.initialState

/-- Reference final state produced by the problem dynamics. -/
def UtilizationProblem.referenceFinalState
    {State : Type uState} {Observation : Type uObservation}
    {Task : Type uTask} {Action : Type uAction}
    (problem : UtilizationProblem State Observation Task Action) : State :=
  problem.runWith problem.referenceUpdate

/-- Final state actually produced by a policy. -/
def ArchitecturePolicy.finalState
    {State : Type uState} {Observation : Type uObservation}
    {Task : Type uTask} {Action : Type uAction}
    {problem : UtilizationProblem State Observation Task Action}
    (policy : ArchitecturePolicy problem) : State :=
  problem.runWith policy.update

/-! ## Computed outcomes and Pareto comparison -/

/-- Observable outcome of running one architecture on one problem.  Every
numeric coordinate is a cost: lower is better. -/
structure ArchitectureOutcome where
  targetRisk : ℝ
  sourceForgetting : ℝ
  inferenceRounds : ℕ
  serialWork : ℕ
  communicationCost : ℕ
  stateDimension : ℕ
  stateCost : ℕ
  legalityQualification : Prop

/-- Compute an architecture outcome from its actual transition trace. -/
noncomputable def evaluate
    {State : Type uState} {Observation : Type uObservation}
    {Task : Type uTask} {Action : Type uAction}
    (problem : UtilizationProblem State Observation Task Action)
    (policy : ArchitecturePolicy problem) : ArchitectureOutcome :=
  let finalState := policy.finalState
  let eventCount := problem.trainingEvents.length
  let rounds := eventCount * policy.roundsPerEvent
  { targetRisk := problem.estimationLoss problem.referenceFinalState finalState
    sourceForgetting :=
      problem.taskLoss problem.sourceTask finalState -
        problem.taskLoss problem.sourceTask problem.initialState
    inferenceRounds := rounds
    serialWork := rounds * policy.workPerRound
    communicationCost :=
      rounds * policy.messagesPerRound * problem.communicationUnitCost
    stateDimension := policy.stateDimension
    stateCost := policy.stateDimension * problem.stateUnitCost
    legalityQualification :=
      problem.legalAction finalState (policy.selectAction finalState) }

/-- Coordinates used by the scalar-free comparison. -/
inductive OutcomeMetric where
  | targetRisk
  | sourceForgetting
  | inferenceRounds
  | serialWork
  | communicationCost
  | stateDimension
  | stateCost
  deriving DecidableEq, Fintype, Repr

/-- Embed each outcome coordinate into the reals solely for a uniform order;
the natural-number coordinates remain exact natural-number counts. -/
noncomputable def ArchitectureOutcome.metricValue
    (outcome : ArchitectureOutcome) : OutcomeMetric → ℝ
  | .targetRisk => outcome.targetRisk
  | .sourceForgetting => outcome.sourceForgetting
  | .inferenceRounds => outcome.inferenceRounds
  | .serialWork => outcome.serialWork
  | .communicationCost => outcome.communicationCost
  | .stateDimension => outcome.stateDimension
  | .stateCost => outcome.stateCost

/-- Componentwise weak improvement among two safety-qualified outcomes. -/
def WeaklyBetter
    (first second : ArchitectureOutcome) : Prop :=
  first.legalityQualification ∧ second.legalityQualification ∧
    ∀ metric, first.metricValue metric ≤ second.metricValue metric

/-- Strict Pareto dominance is weak improvement without weak improvement in
the reverse direction. -/
def ParetoDominates
    (first second : ArchitectureOutcome) : Prop :=
  WeaklyBetter first second ∧ ¬ WeaklyBetter second first

theorem weaklyBetter_trans
    {first second third : ArchitectureOutcome}
    (hfirstSecond : WeaklyBetter first second)
    (hsecondThird : WeaklyBetter second third) :
    WeaklyBetter first third := by
  refine ⟨hfirstSecond.1, hsecondThird.2.1, ?_⟩
  intro metric
  exact le_trans (hfirstSecond.2.2 metric) (hsecondThird.2.2 metric)

/-- Strict Pareto dominance is irreflexive even though unsafe outcomes do not
participate in the weak relation. -/
theorem paretoDominates_irrefl (outcome : ArchitectureOutcome) :
    ¬ ParetoDominates outcome outcome := by
  intro hdominates
  exact hdominates.2 hdominates.1

/-- Strict Pareto dominance is asymmetric. -/
theorem paretoDominates_asymm
    {first second : ArchitectureOutcome}
    (hdominates : ParetoDominates first second) :
    ¬ ParetoDominates second first := by
  intro hreverse
  exact hdominates.2 hreverse.1

/-- Strict Pareto dominance is transitive. -/
theorem paretoDominates_trans
    {first second third : ArchitectureOutcome}
    (hfirstSecond : ParetoDominates first second)
    (hsecondThird : ParetoDominates second third) :
    ParetoDominates first third := by
  have hfirstThird := weaklyBetter_trans hfirstSecond.1 hsecondThird.1
  refine ⟨hfirstThird, ?_⟩
  intro hthirdFirst
  have hthirdSecond := weaklyBetter_trans hthirdFirst hfirstSecond.1
  exact hsecondThird.2 hthirdSecond

/-! ## Proof-bearing utilization licenses -/

/-- Resource premises common to every licensed architecture. -/
structure ResourceHypotheses
    {State : Type uState} {Observation : Type uObservation}
    {Task : Type uTask} {Action : Type uAction}
    {problem : UtilizationProblem State Observation Task Action}
    (policy : ArchitecturePolicy problem) : Prop where
  withinInferenceBudget : policy.roundsPerEvent ≤ problem.inferenceBudget
  withinBandwidth : policy.requiredBandwidth ≤ problem.availableBandwidth

/-- A utilization license contains checked resources, checked legal-action
qualification, and an independently stated outcome guarantee. -/
structure UtilizationLicense
    {State : Type uState} {Observation : Type uObservation}
    {Task : Type uTask} {Action : Type uAction}
    {problem : UtilizationProblem State Observation Task Action}
    (policy : ArchitecturePolicy problem)
    (guarantee : ArchitectureOutcome → Prop) : Prop where
  resources : ResourceHypotheses policy
  legalAction : (evaluate problem policy).legalityQualification
  checkedGuarantee : guarantee (evaluate problem policy)

/-- A licensed legal-action policy is accepted by the independent checker. -/
theorem UtilizationLicense.checkerAccepts
    {State : Type uState} {Observation : Type uObservation}
    {Task : Type uTask} {Action : Type uAction}
    {problem : UtilizationProblem State Observation Task Action}
    {policy : ArchitecturePolicy problem}
    {guarantee : ArchitectureOutcome → Prop}
    (license : UtilizationLicense policy guarantee) :
    problem.checkerAccepts policy.finalState
      (policy.selectAction policy.finalState) := by
  exact problem.legalAction_sound _ _ license.legalAction

/-! ## Risk/work incomparability fixture -/

/-- One-event scalar estimation problem used to show that risk and work do
not induce a scalar-free total architecture order. -/
def tradeoffProblem : UtilizationProblem ℝ Unit Unit Unit where
  referenceUpdate := fun _task _state _observation => 0
  trainingEvents := [((), ())]
  initialState := 0
  estimationLoss := fun reference estimate => (estimate - reference) ^ 2
  taskLoss := fun _task _state => 0
  sourceTask := ()
  topology := .chain
  availableBandwidth := 1
  inferenceBudget := 10
  communicationUnitCost := 1
  stateUnitCost := 1
  legalAction := fun _state _action => True
  checkerAccepts := fun _state _action => True
  legalAction_sound := by simp

/-- Accurate but work-intensive architecture in the tradeoff fixture. -/
def accuratePolicy : ArchitecturePolicy tradeoffProblem where
  update := fun _task _state _observation => 0
  selectAction := fun _state => ()
  requiredBandwidth := 1
  roundsPerEvent := 10
  workPerRound := 1
  messagesPerRound := 1
  stateDimension := 1

/-- Inaccurate zero-round architecture in the tradeoff fixture. -/
def zeroWorkPolicy : ArchitecturePolicy tradeoffProblem where
  update := fun _task _state _observation => 1
  selectAction := fun _state => ()
  requiredBandwidth := 0
  roundsPerEvent := 0
  workPerRound := 0
  messagesPerRound := 0
  stateDimension := 1

theorem tradeoff_outcomes_exact :
    (evaluate tradeoffProblem accuratePolicy).targetRisk = 0 ∧
      (evaluate tradeoffProblem accuratePolicy).serialWork = 10 ∧
      (evaluate tradeoffProblem zeroWorkPolicy).targetRisk = 1 ∧
      (evaluate tradeoffProblem zeroWorkPolicy).serialWork = 0 := by
  norm_num [evaluate, ArchitecturePolicy.finalState,
    UtilizationProblem.referenceFinalState, UtilizationProblem.runWith,
    tradeoffProblem, accuratePolicy, zeroWorkPolicy]

/-- T1 negative crown: the accurate policy and the zero-work policy exchange
risk and work, so neither Pareto-dominates the other. -/
theorem risk_work_tradeoff_pareto_incomparable :
    ¬ ParetoDominates
        (evaluate tradeoffProblem accuratePolicy)
        (evaluate tradeoffProblem zeroWorkPolicy) ∧
      ¬ ParetoDominates
        (evaluate tradeoffProblem zeroWorkPolicy)
        (evaluate tradeoffProblem accuratePolicy) := by
  constructor
  · intro hdominates
    have hwork := hdominates.1.2.2 .serialWork
    norm_num [ArchitectureOutcome.metricValue, evaluate,
      ArchitecturePolicy.finalState, UtilizationProblem.referenceFinalState,
      UtilizationProblem.runWith, tradeoffProblem, accuratePolicy,
      zeroWorkPolicy] at hwork
  · intro hdominates
    have hrisk := hdominates.1.2.2 .targetRisk
    norm_num [ArchitectureOutcome.metricValue, evaluate,
      ArchitecturePolicy.finalState, UtilizationProblem.referenceFinalState,
      UtilizationProblem.runWith, tradeoffProblem, accuratePolicy,
      zeroWorkPolicy] at hrisk

#print axioms paretoDominates_trans
#print axioms UtilizationLicense.checkerAccepts
#print axioms risk_work_tradeoff_pareto_incomparable

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
