import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.Predictive

/-!
# Primal-dual predictive-credit instances

The scalar family below follows an in-place primal-then-dual schedule for the
regularized augmented Lagrangian

`task(h) + lambda * (h - prediction) + rho/2 * (h - prediction)^2
  - tau/2 * lambda^2`.

Dual rate and dual leak are separate fields.  The `ScalarPCALMProblem`
specialization fixes leak and initial dual state to zero and uses the final
primal step of the published PC-ALM schedule.  No convergence or nonlinear
scale claim is made here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Instances

structure ScalarPrimalDualProblem where
  target : ℝ
  penalty : ℝ
  primalRate : ℝ
  dualRate : ℝ
  dualLeak : ℝ
  initialDual : ℝ

abbrev ScalarConstraintParameter := ℝ

noncomputable def scalarPrimalDualTaskObjective
    (problem : ScalarPrimalDualProblem)
    (prediction : ScalarConstraintParameter) : ℝ :=
  (prediction - problem.target) ^ 2 / 2

noncomputable def scalarRegularizedAugmentedLagrangian
    (problem : ScalarPrimalDualProblem)
    (prediction primal dual : ℝ) : ℝ :=
  (primal - problem.target) ^ 2 / 2 +
    dual * (primal - prediction) +
    problem.penalty * (primal - prediction) ^ 2 / 2 -
    problem.dualLeak * dual ^ 2 / 2

def scalarPrimalGradient
    (problem : ScalarPrimalDualProblem)
    (prediction primal dual : ℝ) : ℝ :=
  primal - problem.target + dual +
    problem.penalty * (primal - prediction)

def scalarCompositeParameterGradient
    (problem : ScalarPrimalDualProblem)
    (prediction primal dual : ℝ) : ℝ :=
  -(dual + problem.penalty * (primal - prediction))

theorem scalarRegularizedAugmentedLagrangian_primal_expansion
    (problem : ScalarPrimalDualProblem)
    (prediction primal dual step : ℝ) :
    scalarRegularizedAugmentedLagrangian problem prediction (primal + step) dual =
      scalarRegularizedAugmentedLagrangian problem prediction primal dual +
        step * scalarPrimalGradient problem prediction primal dual +
        step ^ 2 * (1 + problem.penalty) / 2 := by
  simp [scalarRegularizedAugmentedLagrangian, scalarPrimalGradient]
  ring

theorem scalarRegularizedAugmentedLagrangian_parameter_expansion
    (problem : ScalarPrimalDualProblem)
    (prediction primal dual step : ℝ) :
    scalarRegularizedAugmentedLagrangian problem (prediction + step) primal dual =
      scalarRegularizedAugmentedLagrangian problem prediction primal dual +
        step * scalarCompositeParameterGradient problem prediction primal dual +
        problem.penalty * step ^ 2 / 2 := by
  simp [scalarRegularizedAugmentedLagrangian,
    scalarCompositeParameterGradient]
  ring

inductive PrimalDualPhase where
  | ready
  | afterPrimal
  | afterDual
  | creditRead
  deriving DecidableEq

inductive PrimalDualEvent where
  | primalStep
  | dualStep
  | readCredit
  deriving DecidableEq

structure PrimalDualState where
  phase : PrimalDualPhase
  primal : ℝ
  dual : ℝ
  update : ℝ

def initialPrimalDualState
    (problem : ScalarPrimalDualProblem)
    (prediction : ScalarConstraintParameter) : PrimalDualState where
  phase := .ready
  primal := prediction
  dual := problem.initialDual
  update := 0

def primalDualEnabled
    (_problem : ScalarPrimalDualProblem) (_prediction : ScalarConstraintParameter)
    (state : PrimalDualState) (event : PrimalDualEvent) : Prop :=
  match state.phase, event with
  | .ready, .primalStep => True
  | .afterPrimal, .dualStep => True
  | .afterPrimal, .readCredit => True
  | .afterDual, .primalStep => True
  | _, _ => False

def primalDualTransition
    (problem : ScalarPrimalDualProblem)
    (prediction : ScalarConstraintParameter)
    (event : PrimalDualEvent) (state : PrimalDualState) : PrimalDualState :=
  match event with
  | .primalStep =>
      { state with
        phase := .afterPrimal
        primal := state.primal - problem.primalRate *
          scalarPrimalGradient problem prediction state.primal state.dual }
  | .dualStep =>
      { state with
        phase := .afterDual
        dual := state.dual + problem.dualRate *
          ((state.primal - prediction) - problem.dualLeak * state.dual) }
  | .readCredit =>
      { state with
        phase := .creditRead
        update := scalarCompositeParameterGradient
          problem prediction state.primal state.dual }

def primalDualEventCost
    (_problem : ScalarPrimalDualProblem) (_prediction : ScalarConstraintParameter)
    (_state : PrimalDualState) (event : PrimalDualEvent) : ResourceVector :=
  match event with
  | .primalStep =>
      { scalarWork := 9, criticalPathSpan := 6, persistentMemory := 3,
        peakTemporaryMemory := 3, localDerivativeCalls := 1 }
  | .dualStep =>
      { scalarWork := 6, criticalPathSpan := 4, persistentMemory := 3,
        peakTemporaryMemory := 2 }
  | .readCredit =>
      { scalarWork := 4, criticalPathSpan := 3, persistentMemory := 3,
        localDerivativeCalls := 1 }

noncomputable def scalarPrimalDualPC : CreditTransportSystem
    ScalarPrimalDualProblem ScalarConstraintParameter PrimalDualState
    PrimalDualEvent ℝ ℝ where
  objective := scalarPrimalDualTaskObjective
  initialState := initialPrimalDualState
  enabled := primalDualEnabled
  transition := primalDualTransition
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := primalDualEventCost
  oracleAudit := localPredictiveOracle
  localityAudit := edgeNeighborLocality PrimalDualEvent

def primalDualOneCycleFinalPrimalSchedule : List PrimalDualEvent :=
  [.primalStep, .dualStep, .primalStep, .readCredit]

theorem primalDualOneCycleFinalPrimalSchedule_enabled
    (problem : ScalarPrimalDualProblem)
    (prediction : ScalarConstraintParameter) :
    scalarPrimalDualPC.ScheduleEnabled problem prediction
      primalDualOneCycleFinalPrimalSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom,
    primalDualOneCycleFinalPrimalSchedule, scalarPrimalDualPC,
    initialPrimalDualState, primalDualEnabled, primalDualTransition]

/-! ## Published zero-leak PC-ALM specialization -/

structure ScalarPCALMProblem where
  target : ℝ
  penalty : ℝ
  primalRate : ℝ
  dualRate : ℝ

def ScalarPCALMProblem.toPrimalDual
    (problem : ScalarPCALMProblem) : ScalarPrimalDualProblem where
  target := problem.target
  penalty := problem.penalty
  primalRate := problem.primalRate
  dualRate := problem.dualRate
  dualLeak := 0
  initialDual := 0

noncomputable def scalarPCALM : CreditTransportSystem
    ScalarPCALMProblem ScalarConstraintParameter PrimalDualState
    PrimalDualEvent ℝ ℝ where
  objective := fun problem prediction =>
    scalarPrimalDualTaskObjective problem.toPrimalDual prediction
  initialState := fun problem prediction =>
    initialPrimalDualState problem.toPrimalDual prediction
  enabled := fun problem prediction =>
    primalDualEnabled problem.toPrimalDual prediction
  transition := fun problem prediction =>
    primalDualTransition problem.toPrimalDual prediction
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := fun problem prediction =>
    primalDualEventCost problem.toPrimalDual prediction
  oracleAudit := localPredictiveOracle
  localityAudit := edgeNeighborLocality PrimalDualEvent

def scalarPCALMOneCycleSchedule : List PrimalDualEvent :=
  primalDualOneCycleFinalPrimalSchedule

theorem scalarPCALM_schedule_enabled
    (problem : ScalarPCALMProblem)
    (prediction : ScalarConstraintParameter) :
    scalarPCALM.ScheduleEnabled problem prediction scalarPCALMOneCycleSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom,
    scalarPCALMOneCycleSchedule, primalDualOneCycleFinalPrimalSchedule,
    scalarPCALM, initialPrimalDualState, primalDualEnabled,
    primalDualTransition]

theorem scalarPCALM_recovers_full_zeroLeak_schedule
    (problem : ScalarPCALMProblem)
    (prediction : ScalarConstraintParameter) :
    scalarPCALM.finalUpdate problem prediction scalarPCALMOneCycleSchedule =
      scalarPrimalDualPC.finalUpdate problem.toPrimalDual prediction
        primalDualOneCycleFinalPrimalSchedule := by
  rfl

/-! ## Rate, leak, and schedule boundaries -/

noncomputable def zeroDualRateProblem : ScalarPrimalDualProblem :=
  { target := 1, penalty := 1, primalRate := 1 / 2,
    dualRate := 0, dualLeak := 7, initialDual := 0 }

def penaltyCredit
    (problem : ScalarPrimalDualProblem)
    (prediction primal : ℝ) : ℝ :=
  -(problem.penalty * (primal - prediction))

private theorem zeroDualRate_preserves_zero_dual_runFrom
    (prediction : ScalarConstraintParameter) (state : PrimalDualState)
    (events : List PrimalDualEvent) (dualZero : state.dual = 0) :
    (scalarPrimalDualPC.runFrom zeroDualRateProblem prediction state events).dual = 0 := by
  induction events generalizing state with
  | nil => exact dualZero
  | cons event events inductionHypothesis =>
      apply inductionHypothesis
      change (primalDualTransition zeroDualRateProblem prediction event state).dual = 0
      cases event <;>
        simp [primalDualTransition, zeroDualRateProblem, dualZero]

theorem zeroDualRate_zeroInitialization_keeps_dual_zero
    (prediction : ScalarConstraintParameter) (events : List PrimalDualEvent) :
    (scalarPrimalDualPC.run zeroDualRateProblem prediction events).dual = 0 := by
  exact zeroDualRate_preserves_zero_dual_runFrom prediction
    (initialPrimalDualState zeroDualRateProblem prediction) events rfl

theorem zeroDualRate_readCredit_recovers_penaltyCredit
    (prediction primal : ℝ) :
    (primalDualTransition zeroDualRateProblem prediction .readCredit
      { phase := .afterPrimal, primal := primal, dual := 0, update := 13 }).update =
        penaltyCredit zeroDualRateProblem prediction primal := by
  simp [primalDualTransition, scalarCompositeParameterGradient,
    penaltyCredit, zeroDualRateProblem]

def scalarPrimalDualEquilibrium
    (problem : ScalarPrimalDualProblem)
    (prediction primal dual : ℝ) : Prop :=
  scalarPrimalGradient problem prediction primal dual = 0 ∧
    primal - prediction = problem.dualLeak * dual

noncomputable def unregularizedEndpointProblem
    (dualRate : ℝ) : ScalarPrimalDualProblem :=
  { target := 1, penalty := 1, primalRate := 1 / 2,
    dualRate := dualRate, dualLeak := 0, initialDual := 0 }

noncomputable def leakyEndpointProblem
    (dualRate : ℝ) : ScalarPrimalDualProblem :=
  { target := 1, penalty := 1, primalRate := 1 / 2,
    dualRate := dualRate, dualLeak := 1, initialDual := 0 }

theorem unregularized_endpoint
    (dualRate : ℝ) :
    scalarPrimalDualEquilibrium (unregularizedEndpointProblem dualRate) 0 0 1 := by
  norm_num [scalarPrimalDualEquilibrium, scalarPrimalGradient,
    unregularizedEndpointProblem]

theorem leaky_endpoint
    (dualRate : ℝ) :
    scalarPrimalDualEquilibrium (leakyEndpointProblem dualRate) 0 (1 / 3) (1 / 3) := by
  norm_num [scalarPrimalDualEquilibrium, scalarPrimalGradient,
    leakyEndpointProblem]

theorem dualRate_does_not_define_endpoint
    (leftRate rightRate : ℝ) (primal dual : ℝ) :
    scalarPrimalDualEquilibrium (unregularizedEndpointProblem leftRate) 0 primal dual ↔
      scalarPrimalDualEquilibrium
        (unregularizedEndpointProblem rightRate) 0 primal dual := by
  rfl

theorem positiveLeak_changes_endpoint
    (dualRate : ℝ) :
    ¬ scalarPrimalDualEquilibrium (leakyEndpointProblem dualRate) 0 0 1 := by
  norm_num [scalarPrimalDualEquilibrium, scalarPrimalGradient,
    leakyEndpointProblem]

theorem finalPrimalStep_changes_finite_credit :
    let problem : ScalarPrimalDualProblem :=
      { target := 1, penalty := 1, primalRate := 1 / 2,
        dualRate := 1, dualLeak := 0, initialDual := 0 }
    scalarPrimalDualPC.finalUpdate problem 0
        [.primalStep, .dualStep, .readCredit] ≠
      scalarPrimalDualPC.finalUpdate problem 0
        primalDualOneCycleFinalPrimalSchedule := by
  norm_num [CreditTransportSystem.finalUpdate, CreditTransportSystem.run,
    CreditTransportSystem.runFrom, primalDualOneCycleFinalPrimalSchedule,
    scalarPrimalDualPC, initialPrimalDualState, primalDualTransition,
    scalarPrimalGradient, scalarCompositeParameterGradient]

theorem scalarPrimalDualPC_oracle_locality_consistent :
    OracleLocalityConsistent scalarPrimalDualPC.oracleAudit
      scalarPrimalDualPC.localityAudit := by
  simp [OracleLocalityConsistent, scalarPrimalDualPC, localPredictiveOracle,
    OracleAudit.Declares]

#print axioms scalarRegularizedAugmentedLagrangian_primal_expansion
#print axioms scalarRegularizedAugmentedLagrangian_parameter_expansion
#print axioms scalarPCALM_recovers_full_zeroLeak_schedule
#print axioms zeroDualRate_zeroInitialization_keeps_dual_zero
#print axioms zeroDualRate_readCredit_recovers_penaltyCredit
#print axioms dualRate_does_not_define_endpoint
#print axioms positiveLeak_changes_endpoint
#print axioms finalPrimalStep_changes_finite_credit

end Instances

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
