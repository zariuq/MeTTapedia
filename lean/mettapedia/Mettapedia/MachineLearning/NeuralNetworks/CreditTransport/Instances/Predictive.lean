import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Equivalence
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ErrorStateReparameterization

/-!
# Predictive-credit instances

This module places a scalar residual model in the credit-transport calculus in
both state and error coordinates.  The coordinate systems are proved
finite-trajectory and update equivalent.  A frozen-parameter prospective
schedule is then separated from an interleaved-plasticity schedule at two
steps, while their first credit read agrees.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Instances

structure ScalarPCProblem where
  target : ℝ
  penalty : ℝ
  settlingRate : ℝ
  plasticityRate : ℝ

abbrev ScalarPCParameter := ℝ

noncomputable def scalarPCTaskObjective
    (problem : ScalarPCProblem) (prediction : ScalarPCParameter) : ℝ :=
  (prediction - problem.target) ^ 2 / 2

noncomputable def scalarStatePCEnergy
    (problem : ScalarPCProblem) (basePrediction latent : ℝ) : ℝ :=
  (latent - problem.target) ^ 2 / 2 +
    problem.penalty * (latent - basePrediction) ^ 2 / 2

noncomputable def scalarErrorPCEnergy
    (problem : ScalarPCProblem) (basePrediction error : ℝ) : ℝ :=
  (basePrediction + error - problem.target) ^ 2 / 2 +
    problem.penalty * error ^ 2 / 2

theorem scalar_state_error_energy_eq
    (problem : ScalarPCProblem) (basePrediction error : ℝ) :
    scalarStatePCEnergy problem basePrediction (basePrediction + error) =
      scalarErrorPCEnergy problem basePrediction error := by
  simp [scalarStatePCEnergy, scalarErrorPCEnergy]

inductive PCEvent where
  | settle
  | consolidate
  | interleaved
  deriving DecidableEq

structure StatePCState where
  basePrediction : ℝ
  latent : ℝ
  update : ℝ

structure ErrorPCState where
  basePrediction : ℝ
  error : ℝ
  update : ℝ

def initialStatePCState (prediction : ScalarPCParameter) : StatePCState where
  basePrediction := prediction
  latent := prediction
  update := 0

def initialErrorPCState (prediction : ScalarPCParameter) : ErrorPCState where
  basePrediction := prediction
  error := 0
  update := 0

def statePCForce (problem : ScalarPCProblem) (state : StatePCState) : ℝ :=
  problem.target - state.latent +
    problem.penalty * (state.basePrediction - state.latent)

def errorPCForce (problem : ScalarPCProblem) (state : ErrorPCState) : ℝ :=
  problem.target - (state.basePrediction + state.error) -
    problem.penalty * state.error

def predictiveEnabled
    (_problem : ScalarPCProblem) (_parameter : ScalarPCParameter)
    (_state : StatePCState) (event : PCEvent) : Prop :=
  event = .settle ∨ event = .consolidate

def errorPredictiveEnabled
    (_problem : ScalarPCProblem) (_parameter : ScalarPCParameter)
    (_state : ErrorPCState) (event : PCEvent) : Prop :=
  event = .settle ∨ event = .consolidate

def statePCTransition
    (problem : ScalarPCProblem) (_prediction : ScalarPCParameter)
    (event : PCEvent) (state : StatePCState) : StatePCState :=
  match event with
  | .settle =>
      { state with
        latent := state.latent + problem.settlingRate * statePCForce problem state }
  | .consolidate =>
      { state with
        update := problem.penalty * (state.basePrediction - state.latent) }
  | .interleaved => state

def errorPCTransition
    (problem : ScalarPCProblem) (_prediction : ScalarPCParameter)
    (event : PCEvent) (state : ErrorPCState) : ErrorPCState :=
  match event with
  | .settle =>
      { state with
        error := state.error + problem.settlingRate * errorPCForce problem state }
  | .consolidate =>
      { state with update := -problem.penalty * state.error }
  | .interleaved => state

def localPredictiveOracle : OracleAudit where
  accesses := [.localJvpOrVjp]

def edgeNeighborLocality (Event : Type*) : LocalityAudit Event where
  scope := .edgeNeighborLocal
  dependsOn := fun _ _ => True

def predictiveEventCost
    (_problem : ScalarPCProblem) (_parameter : ScalarPCParameter)
    (_state : StatePCState) (event : PCEvent) : ResourceVector :=
  match event with
  | .settle =>
      { scalarWork := 6, criticalPathSpan := 4, persistentMemory := 3,
        peakTemporaryMemory := 2, localDerivativeCalls := 1 }
  | .consolidate =>
      { scalarWork := 2, criticalPathSpan := 2, persistentMemory := 3,
        localDerivativeCalls := 1 }
  | .interleaved => 0

def errorPredictiveEventCost
    (_problem : ScalarPCProblem) (_parameter : ScalarPCParameter)
    (_state : ErrorPCState) (event : PCEvent) : ResourceVector :=
  match event with
  | .settle =>
      { scalarWork := 6, criticalPathSpan := 4, persistentMemory := 3,
        peakTemporaryMemory := 2, localDerivativeCalls := 1 }
  | .consolidate =>
      { scalarWork := 1, criticalPathSpan := 1, persistentMemory := 3,
        localDerivativeCalls := 1 }
  | .interleaved => 0

noncomputable def scalarStatePC : CreditTransportSystem
    ScalarPCProblem ScalarPCParameter StatePCState PCEvent ℝ ℝ where
  objective := scalarPCTaskObjective
  initialState := fun _ prediction => initialStatePCState prediction
  enabled := predictiveEnabled
  transition := statePCTransition
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := predictiveEventCost
  oracleAudit := localPredictiveOracle
  localityAudit := edgeNeighborLocality PCEvent

noncomputable def scalarErrorPC : CreditTransportSystem
    ScalarPCProblem ScalarPCParameter ErrorPCState PCEvent ℝ ℝ where
  objective := scalarPCTaskObjective
  initialState := fun _ prediction => initialErrorPCState prediction
  enabled := errorPredictiveEnabled
  transition := errorPCTransition
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := errorPredictiveEventCost
  oracleAudit := localPredictiveOracle
  localityAudit := edgeNeighborLocality PCEvent

def StateErrorRelated (state : StatePCState) (errorState : ErrorPCState) : Prop :=
  state.basePrediction = errorState.basePrediction ∧
    state.latent = errorState.basePrediction + errorState.error ∧
    state.update = errorState.update

theorem scalarStatePC_scalarErrorPC_traceSimulation :
    TraceSimulation scalarStatePC scalarErrorPC Eq StateErrorRelated := by
  refine
    { initial_related := ?_
      enabled_iff := ?_
      transition_related := ?_
      signal_eq := ?_ }
  · intro problem prediction
    simp [StateErrorRelated, scalarStatePC, scalarErrorPC,
      initialStatePCState, initialErrorPCState]
  · intro problem prediction state errorState leftEvent rightEvent
      statesRelated eventsEqual
    subst rightEvent
    simp [scalarStatePC, scalarErrorPC, predictiveEnabled,
      errorPredictiveEnabled]
  · intro problem prediction state errorState leftEvent rightEvent
      statesRelated eventsEqual
    subst rightEvent
    rcases statesRelated with ⟨baseEqual, latentEqual, updateEqual⟩
    cases leftEvent
    · refine ⟨baseEqual, ?_, updateEqual⟩
      simp [scalarStatePC, scalarErrorPC, statePCTransition,
        errorPCTransition, statePCForce, errorPCForce] at ⊢
      rw [latentEqual, baseEqual]
      ring
    · refine ⟨baseEqual, latentEqual, ?_⟩
      simp [scalarStatePC, scalarErrorPC, statePCTransition,
        errorPCTransition]
      rw [baseEqual, latentEqual]
      ring
    · exact ⟨baseEqual, latentEqual, updateEqual⟩
  · intro problem prediction state errorState statesRelated
    exact statesRelated.2.2

theorem scalarStatePC_scalarErrorPC_finiteTrajectoryEquivalent :
    FiniteTrajectoryEquivalent scalarStatePC scalarErrorPC Eq StateErrorRelated :=
  scalarStatePC_scalarErrorPC_traceSimulation.finiteTrajectoryEquivalent

theorem scalarStatePC_scalarErrorPC_updatePreserving :
    UpdatePreserving scalarStatePC scalarErrorPC StateErrorRelated := by
  intro problem prediction state errorState related
  exact related.2.2

theorem scalarStatePC_scalarErrorPC_parameterUpdateEquivalent :
    ParameterUpdateEquivalent scalarStatePC scalarErrorPC Eq :=
  scalarStatePC_scalarErrorPC_finiteTrajectoryEquivalent.parameterUpdateEquivalent
    scalarStatePC_scalarErrorPC_updatePreserving

/-! ## Frozen-parameter prospective schedule -/

def scalarProspectiveTwoStepSchedule : List PCEvent :=
  [.settle, .settle, .consolidate]

theorem scalarProspectiveTwoStepSchedule_enabled
    (problem : ScalarPCProblem) (prediction : ScalarPCParameter) :
    scalarStatePC.ScheduleEnabled problem prediction
      scalarProspectiveTwoStepSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom, scalarProspectiveTwoStepSchedule,
    scalarStatePC, predictiveEnabled]

private theorem scalarStatePC_runFrom_settling_preserves_base
    (problem : ScalarPCProblem) (prediction : ScalarPCParameter)
    (state : StatePCState) (steps : Nat) :
    (scalarStatePC.runFrom problem prediction state
      (List.replicate steps PCEvent.settle)).basePrediction =
        state.basePrediction := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      simp only [List.replicate_succ, CreditTransportSystem.runFrom]
      rw [ih]
      rfl

theorem scalarProspective_settling_preserves_base
    (problem : ScalarPCProblem) (prediction : ScalarPCParameter) (steps : Nat) :
    (scalarStatePC.run problem prediction
      (List.replicate steps PCEvent.settle)).basePrediction = prediction := by
  exact scalarStatePC_runFrom_settling_preserves_base problem prediction
    (initialStatePCState prediction) steps

/-! ## Interleaved predictive plasticity -/

inductive IncrementalPCEvent where
  | settleAndPlasticity
  deriving DecidableEq

structure IncrementalPCState where
  referencePrediction : ℝ
  latent : ℝ
  workingPrediction : ℝ
  latestUpdate : ℝ

def initialIncrementalPCState (prediction : ScalarPCParameter) : IncrementalPCState where
  referencePrediction := prediction
  latent := prediction
  workingPrediction := prediction
  latestUpdate := 0

def incrementalPCTransition
    (problem : ScalarPCProblem) (_prediction : ScalarPCParameter)
    (_event : IncrementalPCEvent) (state : IncrementalPCState) : IncrementalPCState :=
  let settled := state.latent + problem.settlingRate *
    (problem.target - state.latent +
      problem.penalty * (state.workingPrediction - state.latent))
  let gradient := problem.penalty * (state.workingPrediction - settled)
  { state with
    latent := settled
    workingPrediction := state.workingPrediction - problem.plasticityRate * gradient
    latestUpdate := gradient }

def incrementalPCEventCost
    (_problem : ScalarPCProblem) (_prediction : ScalarPCParameter)
    (_state : IncrementalPCState) (_event : IncrementalPCEvent) : ResourceVector :=
  { scalarWork := 10, criticalPathSpan := 7, persistentMemory := 4,
    peakTemporaryMemory := 3, localDerivativeCalls := 2 }

noncomputable def scalarIncrementalPC : CreditTransportSystem
    ScalarPCProblem ScalarPCParameter IncrementalPCState IncrementalPCEvent ℝ ℝ where
  objective := scalarPCTaskObjective
  initialState := fun _ prediction => initialIncrementalPCState prediction
  enabled := fun _ _ _ _ => True
  transition := incrementalPCTransition
  signal := fun _ _ state => state.latestUpdate
  readUpdate := fun _ _ state => state.latestUpdate
  eventCost := incrementalPCEventCost
  oracleAudit := localPredictiveOracle
  localityAudit := edgeNeighborLocality IncrementalPCEvent

theorem prospective_incremental_firstCredit_equal
    (problem : ScalarPCProblem) (prediction : ScalarPCParameter) :
    scalarStatePC.finalUpdate problem prediction [.settle, .consolidate] =
      scalarIncrementalPC.finalUpdate problem prediction [.settleAndPlasticity] := by
  simp [CreditTransportSystem.finalUpdate, CreditTransportSystem.run,
    CreditTransportSystem.runFrom, scalarStatePC, scalarIncrementalPC,
    initialStatePCState, initialIncrementalPCState, statePCTransition,
    incrementalPCTransition, statePCForce]

/-- Interleaving plasticity changes the second credit read even when the
first read agrees with prospective settling. -/
theorem prospective_incremental_secondCredit_separate :
    let problem : ScalarPCProblem :=
      { target := 1, penalty := 1, settlingRate := 1 / 2,
        plasticityRate := 1 / 2 }
    scalarStatePC.finalUpdate problem 0 scalarProspectiveTwoStepSchedule ≠
      scalarIncrementalPC.finalUpdate problem 0
        [.settleAndPlasticity, .settleAndPlasticity] := by
  norm_num [CreditTransportSystem.finalUpdate, CreditTransportSystem.run,
    CreditTransportSystem.runFrom, scalarProspectiveTwoStepSchedule,
    scalarStatePC, scalarIncrementalPC, initialStatePCState,
    initialIncrementalPCState, statePCTransition, incrementalPCTransition,
    statePCForce]

theorem scalarStatePC_oracle_locality_consistent :
    OracleLocalityConsistent scalarStatePC.oracleAudit scalarStatePC.localityAudit := by
  simp [OracleLocalityConsistent, scalarStatePC, localPredictiveOracle,
    OracleAudit.Declares]

theorem scalarIncrementalPC_oracle_locality_consistent :
    OracleLocalityConsistent scalarIncrementalPC.oracleAudit
      scalarIncrementalPC.localityAudit := by
  simp [OracleLocalityConsistent, scalarIncrementalPC, localPredictiveOracle,
    OracleAudit.Declares]

#print axioms scalar_state_error_energy_eq
#print axioms scalarStatePC_scalarErrorPC_finiteTrajectoryEquivalent
#print axioms scalarStatePC_scalarErrorPC_parameterUpdateEquivalent
#print axioms scalarProspective_settling_preserves_base
#print axioms prospective_incremental_firstCredit_equal
#print axioms prospective_incremental_secondCredit_separate

end Instances

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
