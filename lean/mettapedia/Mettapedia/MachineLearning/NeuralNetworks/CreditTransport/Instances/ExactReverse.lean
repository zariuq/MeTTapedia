import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Equivalence
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.BackpropExactness

/-!
# Exact reverse-credit instances

Two finite scalar machines expose ordinary reverse credit and tied recurrent
reverse credit through `CreditTransportSystem`.  The transition order is
explicit, exact reverse access is declared global, and the recurrent readout
sums both occurrences of the tied parameter.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Instances

/-! ## A two-layer scalar chain -/

structure ScalarChainProblem where
  input : ℝ
  target : ℝ

structure ScalarChainParameter where
  inputWeight : ℝ
  outputWeight : ℝ

@[ext] structure ScalarChainUpdate where
  inputWeight : ℝ
  outputWeight : ℝ

inductive ReversePhase where
  | ready
  | forwarded
  | outputReversed
  | hiddenReversed
  | aggregated
  deriving DecidableEq

inductive ChainReverseEvent where
  | forward
  | reverseOutput
  | reverseHidden
  | aggregateOccurrences
  deriving DecidableEq

structure ChainReverseState where
  phase : ReversePhase
  hidden : ℝ
  output : ℝ
  outputAdjoint : ℝ
  hiddenAdjoint : ℝ
  update : ScalarChainUpdate

noncomputable def scalarChainObjective
    (problem : ScalarChainProblem) (parameter : ScalarChainParameter) : ℝ :=
  let hidden := parameter.inputWeight * problem.input
  let output := parameter.outputWeight * hidden
  (output - problem.target) ^ 2 / 2

def scalarChainGradient
    (problem : ScalarChainProblem) (parameter : ScalarChainParameter) :
    ScalarChainUpdate :=
  let hidden := parameter.inputWeight * problem.input
  let residual := parameter.outputWeight * hidden - problem.target
  { inputWeight := parameter.outputWeight * residual * problem.input
    outputWeight := residual * hidden }

def initialChainReverseState : ChainReverseState where
  phase := .ready
  hidden := 0
  output := 0
  outputAdjoint := 0
  hiddenAdjoint := 0
  update := { inputWeight := 0, outputWeight := 0 }

def chainReverseEnabled
    (_problem : ScalarChainProblem) (_parameter : ScalarChainParameter)
    (state : ChainReverseState) (event : ChainReverseEvent) : Prop :=
  match state.phase, event with
  | .ready, .forward => True
  | .forwarded, .reverseOutput => True
  | .outputReversed, .reverseHidden => True
  | .hiddenReversed, .aggregateOccurrences => True
  | _, _ => False

def chainReverseTransition
    (problem : ScalarChainProblem) (parameter : ScalarChainParameter)
    (event : ChainReverseEvent) (state : ChainReverseState) : ChainReverseState :=
  match event with
  | .forward =>
      let hidden := parameter.inputWeight * problem.input
      { state with
        phase := .forwarded
        hidden := hidden
        output := parameter.outputWeight * hidden }
  | .reverseOutput =>
      { state with
        phase := .outputReversed
        outputAdjoint := state.output - problem.target }
  | .reverseHidden =>
      { state with
        phase := .hiddenReversed
        hiddenAdjoint := parameter.outputWeight * state.outputAdjoint }
  | .aggregateOccurrences =>
      { state with
        phase := .aggregated
        update :=
          { inputWeight := state.hiddenAdjoint * problem.input
            outputWeight := state.outputAdjoint * state.hidden } }

def chainReverseCost
    (_problem : ScalarChainProblem) (_parameter : ScalarChainParameter)
    (_state : ChainReverseState) (event : ChainReverseEvent) : ResourceVector :=
  match event with
  | .forward =>
      { scalarWork := 2, criticalPathSpan := 2, peakTemporaryMemory := 2 }
  | .reverseOutput =>
      { scalarWork := 1, criticalPathSpan := 1, exactReverseCalls := 1 }
  | .reverseHidden =>
      { scalarWork := 1, criticalPathSpan := 1, exactReverseCalls := 1 }
  | .aggregateOccurrences =>
      { scalarWork := 2, criticalPathSpan := 1, exactReverseCalls := 1 }

def exactReverseOracle : OracleAudit where
  accesses := [.exactReverseVjp]

def globalReverseLocality (Event : Type*) : LocalityAudit Event where
  scope := .globalReverse
  dependsOn := fun _ _ => True

noncomputable def scalarChainBP : CreditTransportSystem
    ScalarChainProblem ScalarChainParameter ChainReverseState
    ChainReverseEvent ScalarChainUpdate ScalarChainUpdate where
  objective := scalarChainObjective
  initialState := fun _ _ => initialChainReverseState
  enabled := chainReverseEnabled
  transition := chainReverseTransition
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := chainReverseCost
  oracleAudit := exactReverseOracle
  localityAudit := globalReverseLocality ChainReverseEvent

def scalarChainBPSchedule : List ChainReverseEvent :=
  [.forward, .reverseOutput, .reverseHidden, .aggregateOccurrences]

theorem scalarChainBP_oracle_locality_consistent :
    OracleLocalityConsistent scalarChainBP.oracleAudit scalarChainBP.localityAudit := by
  simp [OracleLocalityConsistent, OracleAudit.Declares, scalarChainBP,
    exactReverseOracle, globalReverseLocality, LocalityClass.NoBroaderThan,
    LocalityClass.rank]

theorem scalarChainBPSchedule_enabled
    (problem : ScalarChainProblem) (parameter : ScalarChainParameter) :
    scalarChainBP.ScheduleEnabled problem parameter scalarChainBPSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom, scalarChainBPSchedule,
    scalarChainBP, initialChainReverseState, chainReverseEnabled,
    chainReverseTransition]

theorem scalarChainBP_finalUpdate
    (problem : ScalarChainProblem) (parameter : ScalarChainParameter) :
    scalarChainBP.finalUpdate problem parameter scalarChainBPSchedule =
      scalarChainGradient problem parameter := by
  ext <;>
    simp [CreditTransportSystem.finalUpdate, CreditTransportSystem.run,
      CreditTransportSystem.runFrom, scalarChainBPSchedule, scalarChainBP,
      initialChainReverseState, chainReverseTransition, scalarChainGradient]

/-- Exact first-order coefficient for changing only the first weight. -/
theorem scalarChainObjective_inputWeight_expansion
    (problem : ScalarChainProblem) (parameter : ScalarChainParameter) (step : ℝ) :
    scalarChainObjective problem
        { parameter with inputWeight := parameter.inputWeight + step } =
      scalarChainObjective problem parameter +
        step * (scalarChainGradient problem parameter).inputWeight +
        step ^ 2 * (parameter.outputWeight * problem.input) ^ 2 / 2 := by
  simp [scalarChainObjective, scalarChainGradient]
  ring

/-- Exact first-order coefficient for changing only the second weight. -/
theorem scalarChainObjective_outputWeight_expansion
    (problem : ScalarChainProblem) (parameter : ScalarChainParameter) (step : ℝ) :
    scalarChainObjective problem
        { parameter with outputWeight := parameter.outputWeight + step } =
      scalarChainObjective problem parameter +
        step * (scalarChainGradient problem parameter).outputWeight +
        step ^ 2 * (parameter.inputWeight * problem.input) ^ 2 / 2 := by
  simp [scalarChainObjective, scalarChainGradient]
  ring

theorem scalarChainBP_incomplete_reverse_ne_gradient :
    scalarChainBP.finalUpdate
        { input := 1, target := 0 }
        { inputWeight := 2, outputWeight := 3 }
        [.forward, .reverseOutput] ≠
      scalarChainGradient
        { input := 1, target := 0 }
        { inputWeight := 2, outputWeight := 3 } := by
  intro equality
  have := congrArg ScalarChainUpdate.inputWeight equality
  norm_num [CreditTransportSystem.finalUpdate, CreditTransportSystem.run,
    CreditTransportSystem.runFrom, scalarChainBP, initialChainReverseState,
    chainReverseTransition, scalarChainGradient] at this

/-! ## A tied two-occurrence scalar recurrence -/

structure ScalarRecurrentProblem where
  input : ℝ
  target : ℝ

abbrev ScalarRecurrentParameter := ℝ

inductive RecurrentReverseEvent where
  | forwardFirst
  | forwardSecond
  | reverseSecond
  | reverseFirst
  | aggregateTiedOccurrences
  deriving DecidableEq

structure RecurrentReverseState where
  phase : Nat
  firstState : ℝ
  secondState : ℝ
  secondAdjoint : ℝ
  firstAdjoint : ℝ
  firstOccurrenceCredit : ℝ
  secondOccurrenceCredit : ℝ

noncomputable def scalarRecurrentObjective
    (problem : ScalarRecurrentProblem) (weight : ScalarRecurrentParameter) : ℝ :=
  (weight * (weight * problem.input) - problem.target) ^ 2 / 2

def scalarRecurrentBPTTCredit
    (problem : ScalarRecurrentProblem) (weight : ScalarRecurrentParameter) : ℝ :=
  let firstState := weight * problem.input
  let secondResidual := weight * firstState - problem.target
  let firstAdjoint := weight * secondResidual
  firstAdjoint * problem.input + secondResidual * firstState

def initialRecurrentReverseState : RecurrentReverseState where
  phase := 0
  firstState := 0
  secondState := 0
  secondAdjoint := 0
  firstAdjoint := 0
  firstOccurrenceCredit := 0
  secondOccurrenceCredit := 0

def recurrentReverseEnabled
    (_problem : ScalarRecurrentProblem) (_weight : ScalarRecurrentParameter)
    (state : RecurrentReverseState) (event : RecurrentReverseEvent) : Prop :=
  match state.phase, event with
  | 0, .forwardFirst => True
  | 1, .forwardSecond => True
  | 2, .reverseSecond => True
  | 3, .reverseFirst => True
  | 4, .aggregateTiedOccurrences => True
  | _, _ => False

def recurrentReverseTransition
    (problem : ScalarRecurrentProblem) (weight : ScalarRecurrentParameter)
    (event : RecurrentReverseEvent)
    (state : RecurrentReverseState) : RecurrentReverseState :=
  match event with
  | .forwardFirst =>
      { state with phase := 1, firstState := weight * problem.input }
  | .forwardSecond =>
      { state with phase := 2, secondState := weight * state.firstState }
  | .reverseSecond =>
      { state with phase := 3, secondAdjoint := state.secondState - problem.target }
  | .reverseFirst =>
      { state with phase := 4, firstAdjoint := weight * state.secondAdjoint }
  | .aggregateTiedOccurrences =>
      { state with
        phase := 5
        firstOccurrenceCredit := state.firstAdjoint * problem.input
        secondOccurrenceCredit := state.secondAdjoint * state.firstState }

def recurrentReverseCost
    (_problem : ScalarRecurrentProblem) (_weight : ScalarRecurrentParameter)
    (_state : RecurrentReverseState) (event : RecurrentReverseEvent) : ResourceVector :=
  match event with
  | .forwardFirst | .forwardSecond =>
      { scalarWork := 1, criticalPathSpan := 1, peakTemporaryMemory := 1 }
  | .reverseSecond | .reverseFirst =>
      { scalarWork := 1, criticalPathSpan := 1, exactReverseCalls := 1 }
  | .aggregateTiedOccurrences =>
      { scalarWork := 3, criticalPathSpan := 2, exactReverseCalls := 1 }

noncomputable def scalarTiedBPTT : CreditTransportSystem
    ScalarRecurrentProblem ScalarRecurrentParameter RecurrentReverseState
    RecurrentReverseEvent ℝ ℝ where
  objective := scalarRecurrentObjective
  initialState := fun _ _ => initialRecurrentReverseState
  enabled := recurrentReverseEnabled
  transition := recurrentReverseTransition
  signal := fun _ _ state =>
    state.firstOccurrenceCredit + state.secondOccurrenceCredit
  readUpdate := fun _ _ state =>
    state.firstOccurrenceCredit + state.secondOccurrenceCredit
  eventCost := recurrentReverseCost
  oracleAudit := exactReverseOracle
  localityAudit := globalReverseLocality RecurrentReverseEvent

def scalarTiedBPTTSchedule : List RecurrentReverseEvent :=
  [.forwardFirst, .forwardSecond, .reverseSecond, .reverseFirst,
    .aggregateTiedOccurrences]

theorem scalarTiedBPTT_oracle_locality_consistent :
    OracleLocalityConsistent scalarTiedBPTT.oracleAudit scalarTiedBPTT.localityAudit := by
  simp [OracleLocalityConsistent, OracleAudit.Declares, scalarTiedBPTT,
    exactReverseOracle, globalReverseLocality, LocalityClass.NoBroaderThan,
    LocalityClass.rank]

theorem scalarTiedBPTTSchedule_enabled
    (problem : ScalarRecurrentProblem) (weight : ScalarRecurrentParameter) :
    scalarTiedBPTT.ScheduleEnabled problem weight scalarTiedBPTTSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom, scalarTiedBPTTSchedule,
    scalarTiedBPTT, initialRecurrentReverseState, recurrentReverseEnabled,
    recurrentReverseTransition]

theorem scalarTiedBPTT_finalUpdate
    (problem : ScalarRecurrentProblem) (weight : ScalarRecurrentParameter) :
    scalarTiedBPTT.finalUpdate problem weight scalarTiedBPTTSchedule =
      scalarRecurrentBPTTCredit problem weight := by
  simp [CreditTransportSystem.finalUpdate, CreditTransportSystem.run,
    CreditTransportSystem.runFrom, scalarTiedBPTTSchedule, scalarTiedBPTT,
    initialRecurrentReverseState, recurrentReverseTransition,
    scalarRecurrentBPTTCredit]

theorem scalarRecurrentBPTTCredit_eq_two_occurrence_sum
    (problem : ScalarRecurrentProblem) (weight : ScalarRecurrentParameter) :
    scalarRecurrentBPTTCredit problem weight =
      (weight * (weight * (weight * problem.input) - problem.target)) *
          problem.input +
        (weight * (weight * problem.input) - problem.target) *
          (weight * problem.input) := by
  simp [scalarRecurrentBPTTCredit]

/-- Dropping the second tied occurrence loses a real term. -/
theorem tied_singleOccurrence_credit_is_wrong :
    let problem : ScalarRecurrentProblem := { input := 1, target := 0 }
    let weight : ScalarRecurrentParameter := 2
    let firstOnly :=
      (weight * (weight * (weight * problem.input) - problem.target)) * problem.input
    firstOnly ≠ scalarRecurrentBPTTCredit problem weight := by
  norm_num [scalarRecurrentBPTTCredit]

#print axioms scalarChainBP_finalUpdate
#print axioms scalarChainObjective_inputWeight_expansion
#print axioms scalarChainObjective_outputWeight_expansion
#print axioms scalarChainBP_incomplete_reverse_ne_gradient
#print axioms scalarTiedBPTT_finalUpdate
#print axioms scalarRecurrentBPTTCredit_eq_two_occurrence_sum
#print axioms tied_singleOccurrence_credit_is_wrong

end Instances

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
