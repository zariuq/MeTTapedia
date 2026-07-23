import Mettapedia.MachineLearning.NeuralNetworks.Architecture.StateCarrier
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.VaryingScheduleTracking

/-!
# Certified tracking across carrier phase handoffs

An itinerant controller may change the command or operator family between
phases while a local solver only approximately reaches the corresponding
command-relative target inside each phase.  This module connects the existing
varying-solver tracking convolution to observation itineraries.

The result is finite and discrete.  It assumes a locally contractive solver
family, an admitted target-drift schedule, and an observation margin at every
handoff.  It does not infer a heteroclinic channel, timescale separation,
learned switching, or uniform stability from a realized trace.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace PhaseHandoffTracking

open CreditTransport
open CreditTransport.LocalAmortizedInitialization
open CreditTransport.ParameterTracking
open CreditTransport.VaryingScheduleTracking

variable {Parameter State Observation : Type*} [NormedAddCommGroup State]

/-- State reached after every declared within-phase settling block.  The
initial state is omitted; each list entry is one phase handoff. -/
def handoffStates (solver : Parameter → State → State) :
    State → List (TrackingStage Parameter) → List State
  | _state, [] => []
  | state, stage :: stages =>
      let nextState := (solver stage.next)^[stage.steps] state
      nextState :: handoffStates solver nextState stages

/-- Target and recursively propagated error budget at every handoff. -/
noncomputable def targetBudgetTrajectory
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius) :
    ℝ → List (TrackingStage Parameter) → List (State × ℝ)
  | _error, [] => []
  | error, stage :: stages =>
      let nextError := advanceBudget family error stage
      (target stage.next, nextError) ::
        targetBudgetTrajectory family nextError stages

/-- Every reached handoff state lies within its time-ordered target budget.
This is the all-prefix form of the final-state theorem in
`VaryingScheduleTracking`. -/
theorem handoffStates_forall₂_targetBudgetTrajectory
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (previous : Parameter) (state : State) (error : ℝ)
    (stages : List (TrackingStage Parameter))
    (herror : ‖state - target previous‖ ≤ error)
    (hadmissible : ScheduleAdmissible family previous error stages) :
    List.Forall₂
      (fun runtime targetBudget =>
        ‖runtime - targetBudget.1‖ ≤ targetBudget.2)
      (handoffStates solver state stages)
      (targetBudgetTrajectory family error stages) := by
  induction stages generalizing previous state error with
  | nil => exact .nil
  | cons stage stages ih =>
      rcases hadmissible with ⟨hdrift, hadmission, htail⟩
      let nextState := (solver stage.next)^[stage.steps] state
      let nextError := advanceBudget family error stage
      have hhead : ‖nextState - target stage.next‖ ≤ nextError := by
        have hsingle :
            ScheduleAdmissible family previous error [stage] :=
          ⟨hdrift, hadmission, trivial⟩
        simpa [nextState, nextError, runSchedule, finalParameter,
          scheduleBudget] using
          runSchedule_tracking_le family previous state error [stage]
            herror hsingle
      exact .cons hhead
        (ih stage.next nextState nextError hhead htail)

/-- The observation is insensitive to every state within the declared target
budget.  For discrete routing decisions this is the required margin premise;
continuity of a real-valued readout alone does not imply it. -/
def ObservationStableWithin (observe : State → Observation)
    (targetState : State) (error : ℝ) : Prop :=
  ∀ state, ‖state - targetState‖ ≤ error →
    observe state = observe targetState

/-- Observation-margin premises at every handoff, indexed by the same
time-ordered error recurrence as the solver tracking theorem. -/
noncomputable def ObservationHandoffAdmissible
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (observe : State → Observation)
    (family : LocalSolverFamily solver target radius) :
    ℝ → List (TrackingStage Parameter) → Prop
  | _error, [] => True
  | error, stage :: stages =>
      let nextError := advanceBudget family error stage
      ObservationStableWithin observe (target stage.next) nextError ∧
        ObservationHandoffAdmissible observe family nextError stages

/-- Observations produced after every within-phase settling block. -/
def realizedHandoffItinerary (observe : State → Observation)
    (solver : Parameter → State → State) (state : State)
    (stages : List (TrackingStage Parameter)) : List Observation :=
  (handoffStates solver state stages).map observe

/-- Ideal command-relative observations selected by the same phase list. -/
def targetHandoffItinerary (observe : State → Observation)
    (target : Parameter → State)
    (stages : List (TrackingStage Parameter)) : List Observation :=
  stages.map (fun stage => observe (target stage.next))

/-- Sufficient within-phase settling preserves the complete finite target
itinerary, not only its terminal observation. -/
theorem observationItinerary_eq_target
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (observe : State → Observation)
    (family : LocalSolverFamily solver target radius)
    (previous : Parameter) (state : State) (error : ℝ)
    (stages : List (TrackingStage Parameter))
    (herror : ‖state - target previous‖ ≤ error)
    (hadmissible : ScheduleAdmissible family previous error stages)
    (hobservation :
      ObservationHandoffAdmissible observe family error stages) :
    realizedHandoffItinerary observe solver state stages =
      targetHandoffItinerary observe target stages := by
  induction stages generalizing previous state error with
  | nil => rfl
  | cons stage stages ih =>
      rcases hadmissible with ⟨hdrift, hadmission, htail⟩
      rcases hobservation with ⟨hstable, hobservationTail⟩
      let nextState := (solver stage.next)^[stage.steps] state
      let nextError := advanceBudget family error stage
      have hhead : ‖nextState - target stage.next‖ ≤ nextError := by
        have hsingle :
            ScheduleAdmissible family previous error [stage] :=
          ⟨hdrift, hadmission, trivial⟩
        simpa [nextState, nextError, runSchedule, finalParameter,
          scheduleBudget] using
          runSchedule_tracking_le family previous state error [stage]
            herror hsingle
      have hheadObservation :
          observe nextState = observe (target stage.next) :=
        hstable nextState hhead
      simp only [realizedHandoffItinerary, targetHandoffItinerary,
        handoffStates, List.map_cons]
      rw [hheadObservation]
      exact congrArg (List.cons (observe (target stage.next)))
        (ih stage.next nextState nextError hhead htail hobservationTail)

/-! ## State-carrier specialization -/

universe uEnvironment uSlow uCommand uRead uRoute uProposal uPolicy

/-- A state carrier whose command-relative steps form the certified solver
family preserves the target observation itinerary under the same finite
handoff conditions.  Environment and slow weights are fixed throughout. -/
theorem StateCarrier.phaseHandoffItinerary_eq_targets
    {Environment : Type uEnvironment} {Slow : Type uSlow}
    {Command : Type uCommand} {Read : Type uRead} {Route : Type uRoute}
    {Proposal : Type uProposal} {Policy : Type uPolicy}
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow)
    (target : Command → State) (radius : ℝ)
    (family : LocalSolverFamily
      (fun command state => carrier.step environment slow command state)
      target radius)
    (previous : Command) (state : State) (error : ℝ)
    (stages : List (TrackingStage Command))
    (herror : ‖state - target previous‖ ≤ error)
    (hadmissible : ScheduleAdmissible family previous error stages)
    (hobservation : ObservationHandoffAdmissible
      (carrier.observeAtState environment slow) family error stages) :
    realizedHandoffItinerary (carrier.observeAtState environment slow)
        (fun command state => carrier.step environment slow command state)
        state stages =
      targetHandoffItinerary (carrier.observeAtState environment slow)
        target stages :=
  observationItinerary_eq_target
    (carrier.observeAtState environment slow) family previous state error
    stages herror hadmissible hobservation

/-! ## Executable positive and negative fixtures -/

open CreditTransport.ParameterTracking in
private noncomputable def phaseObservation (state : ℝ) : Bool :=
  decide ((2 / 5 : ℝ) ≤ state)

private theorem phaseObservation_stable_quarter :
    ObservationStableWithin phaseObservation (1 / 4 : ℝ) (1 / 8) := by
  intro state hstate
  have habs : |state - (1 / 4 : ℝ)| ≤ 1 / 8 := by
    simpa [Real.norm_eq_abs] using hstate
  have hupper := (abs_le.mp habs).2
  have hbelow : ¬ (2 / 5 : ℝ) ≤ state := by linarith
  simp [phaseObservation, hbelow]
  norm_num

private theorem phaseObservation_stable_half :
    ObservationStableWithin phaseObservation (1 / 2 : ℝ) (3 / 32) := by
  intro state hstate
  have habs : |state - (1 / 2 : ℝ)| ≤ 3 / 32 := by
    simpa [Real.norm_eq_abs] using hstate
  have hlower := (abs_le.mp habs).1
  have habove : (2 / 5 : ℝ) ≤ state := by linarith
  simp [phaseObservation, habove]
  norm_num

open CreditTransport.ParameterTracking

theorem shiftedHalf_phaseObservation_admissible :
    ObservationHandoffAdmissible phaseObservation shiftedHalfFamily 0
      shiftedHalfTwoStageSchedule := by
  rw [show shiftedHalfTwoStageSchedule =
    [ { next := 1 / 4, steps := 1, driftBound := 1 / 4 },
      { next := 1 / 2, steps := 2, driftBound := 1 / 4 } ] by rfl]
  refine ⟨?_, ?_⟩
  · convert phaseObservation_stable_quarter using 1
    norm_num [advanceBudget, stageAttenuation, shiftedHalfFamily]
  · refine ⟨?_, trivial⟩
    convert phaseObservation_stable_half using 1
    norm_num [advanceBudget, stageAttenuation, shiftedHalfFamily]

/-- The two admitted phase handoffs retain the nonconstant target itinerary. -/
theorem shiftedHalf_phaseObservation_itinerary :
    realizedHandoffItinerary phaseObservation shiftedHalfSolver 0
        shiftedHalfTwoStageSchedule =
      targetHandoffItinerary phaseObservation (fun target : ℝ => target)
        shiftedHalfTwoStageSchedule := by
  exact observationItinerary_eq_target phaseObservation shiftedHalfFamily
    0 0 0 shiftedHalfTwoStageSchedule (by norm_num)
    shiftedHalfTwoStageSchedule_admissible
    shiftedHalf_phaseObservation_admissible

theorem shiftedHalf_phaseObservation_itinerary_value :
    realizedHandoffItinerary phaseObservation shiftedHalfSolver 0
      shiftedHalfTwoStageSchedule = [false, true] := by
  rw [shiftedHalf_phaseObservation_itinerary]
  norm_num [targetHandoffItinerary, shiftedHalfTwoStageSchedule,
    phaseObservation]

private noncomputable def aboveHalfObservation (state : ℝ) : Bool :=
  decide ((1 / 2 : ℝ) ≤ state)

noncomputable def noSettlingHandoffSchedule : List (TrackingStage ℝ) :=
  [{ next := 1, steps := 0, driftBound := 1 }]

theorem noSettlingHandoffSchedule_admissible :
    ScheduleAdmissible shiftedHalfFamily 0 0 noSettlingHandoffSchedule := by
  norm_num [noSettlingHandoffSchedule, ScheduleAdmissible,
    advanceBudget, stageAttenuation, shiftedHalfFamily, Real.norm_eq_abs]

/-- A valid target-drift schedule with no within-phase settling changes the
discrete itinerary: the runtime state remains zero while the target is one. -/
theorem noSettling_changes_itinerary :
    realizedHandoffItinerary aboveHalfObservation shiftedHalfSolver 0
        noSettlingHandoffSchedule ≠
      targetHandoffItinerary aboveHalfObservation (fun target : ℝ => target)
        noSettlingHandoffSchedule := by
  norm_num [realizedHandoffItinerary, targetHandoffItinerary, handoffStates,
    noSettlingHandoffSchedule, aboveHalfObservation]

/-- The observation-margin checker rejects that inaccurate handoff. -/
theorem noSettling_observation_admission_impossible :
    ¬ ObservationHandoffAdmissible aboveHalfObservation shiftedHalfFamily 0
      noSettlingHandoffSchedule := by
  intro hadmissible
  rcases hadmissible with ⟨hstable, _⟩
  have hzero := hstable 0 (by
    norm_num [advanceBudget, stageAttenuation, shiftedHalfFamily,
      Real.norm_eq_abs])
  norm_num [aboveHalfObservation] at hzero

#print axioms handoffStates_forall₂_targetBudgetTrajectory
#print axioms observationItinerary_eq_target
#print axioms StateCarrier.phaseHandoffItinerary_eq_targets
#print axioms shiftedHalf_phaseObservation_itinerary
#print axioms shiftedHalf_phaseObservation_itinerary_value
#print axioms noSettling_changes_itinerary
#print axioms noSettling_observation_admission_impossible

end PhaseHandoffTracking

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
