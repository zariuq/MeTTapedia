import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ResourceSemantics

/-!
# Equivalence notions for credit transport

Objective, equilibrium, finite dynamics, parameter updates, and downstream
behavior are distinct observations.  The implication theorems in this module
state the extra factorization premises needed to pass from one level to another.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

open CreditTransportSystem

universe uP uΘ uS uE uS₁ uS₂ uE₁ uE₂ uSig uU uB

variable {Problem : Type uP} {Parameter : Type uΘ}
variable {LocalState₁ : Type uS₁} {LocalState₂ : Type uS₂}
variable {Event₁ : Type uE₁} {Event₂ : Type uE₂}
variable {Signal : Type uSig} {Update : Type uU}

abbrev CreditSystem
    (Problem : Type uP) (Parameter : Type uΘ)
    (LocalState : Type uS) (Event : Type uE)
    (Signal : Type uSig) (Update : Type uU) :=
  CreditTransportSystem Problem Parameter LocalState Event Signal Update

/-- The declared objectives agree pointwise.  This says nothing about solver
state, schedule, or finite dynamics. -/
def ObjectiveEquivalent
    (left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update)
    (right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update) : Prop :=
  ∀ problem parameter, left.objective problem parameter = right.objective problem parameter

/-- Both systems have equilibrium states with equal observable credit and
pre-optimizer updates.  Existence does not assert convergence to those states. -/
def EquilibriumCreditEquivalent
    (left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update)
    (right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update) : Prop :=
  ∀ problem parameter,
    ∃ leftState rightState,
      left.IsEquilibriumAt problem parameter leftState ∧
      right.IsEquilibriumAt problem parameter rightState ∧
      left.signal problem parameter leftState =
        right.signal problem parameter rightState ∧
      left.readUpdate problem parameter leftState =
        right.readUpdate problem parameter rightState

/-- A finite trajectory equivalence witnesses related terminal states and equal
signal traces for every pair of schedules related event by event. -/
structure FiniteTrajectoryEquivalent
    (left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update)
    (right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update)
    (eventRel : Event₁ → Event₂ → Prop)
    (stateRel : LocalState₁ → LocalState₂ → Prop) : Prop where
  run_related : ∀ {problem parameter leftEvents rightEvents},
    List.Forall₂ eventRel leftEvents rightEvents →
    stateRel
      (left.run problem parameter leftEvents)
      (right.run problem parameter rightEvents)
  signal_traces_eq : ∀ {problem parameter leftEvents rightEvents},
    List.Forall₂ eventRel leftEvents rightEvents →
    left.signalTrace problem parameter leftEvents =
      right.signalTrace problem parameter rightEvents

/-- Final pre-optimizer update equality for every paired finite schedule. -/
def ParameterUpdateEquivalent
    (left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update)
    (right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update)
    (eventRel : Event₁ → Event₂ → Prop) : Prop :=
  ∀ {problem parameter leftEvents rightEvents},
    List.Forall₂ eventRel leftEvents rightEvents →
    left.finalUpdate problem parameter leftEvents =
      right.finalUpdate problem parameter rightEvents

/-- A downstream kernel assigns a real weight to each behavior.  Probability
normalization, randomness coupling, budgets, and checker support are obligations
of a concrete SearchBridge instance. -/
abbrev BehaviorKernel (Behavior : Type uB) :=
  Problem → Parameter → Update → Behavior → ℝ

/-- Exact equality of all downstream behavior weights under paired schedules. -/
def BehavioralSearchEquivalent {Behavior : Type uB}
    (left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update)
    (right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update)
    (eventRel : Event₁ → Event₂ → Prop)
    (leftKernel rightKernel : BehaviorKernel
      (Problem := Problem) (Parameter := Parameter) (Update := Update) Behavior) : Prop :=
  ∀ {problem parameter leftEvents rightEvents},
    List.Forall₂ eventRel leftEvents rightEvents →
    ∀ behavior,
      leftKernel problem parameter
          (left.finalUpdate problem parameter leftEvents) behavior =
        rightKernel problem parameter
          (right.finalUpdate problem parameter rightEvents) behavior

/-- The final update readout respects a heterogeneous state relation. -/
def UpdatePreserving
    (left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update)
    (right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update)
    (stateRel : LocalState₁ → LocalState₂ → Prop) : Prop :=
  ∀ {problem parameter leftState rightState},
    stateRel leftState rightState →
    left.readUpdate problem parameter leftState =
      right.readUpdate problem parameter rightState

/-- A one-event simulation from the declared initial states.  It exposes the
event correspondence, enabledness boundary, state relation, and observable
signal preservation used to establish finite trajectory equivalence. -/
structure TraceSimulation
    (left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update)
    (right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update)
    (eventRel : Event₁ → Event₂ → Prop)
    (stateRel : LocalState₁ → LocalState₂ → Prop) : Prop where
  initial_related : ∀ problem parameter,
    stateRel (left.initialState problem parameter)
      (right.initialState problem parameter)
  enabled_iff : ∀ {problem parameter leftState rightState leftEvent rightEvent},
    stateRel leftState rightState → eventRel leftEvent rightEvent →
    (left.enabled problem parameter leftState leftEvent ↔
      right.enabled problem parameter rightState rightEvent)
  transition_related :
    ∀ {problem parameter leftState rightState leftEvent rightEvent},
      stateRel leftState rightState → eventRel leftEvent rightEvent →
      stateRel
        (left.transition problem parameter leftEvent leftState)
        (right.transition problem parameter rightEvent rightState)
  signal_eq : ∀ {problem parameter leftState rightState},
    stateRel leftState rightState →
    left.signal problem parameter leftState =
      right.signal problem parameter rightState

namespace TraceSimulation

variable
  {left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update}
  {right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update}
variable {eventRel : Event₁ → Event₂ → Prop}
variable {stateRel : LocalState₁ → LocalState₂ → Prop}

theorem runFrom_related
    (simulation : TraceSimulation left right eventRel stateRel)
    {problem : Problem} {parameter : Parameter} :
    ∀ {leftState : LocalState₁} {rightState : LocalState₂}
      {leftEvents : List Event₁} {rightEvents : List Event₂},
      stateRel leftState rightState →
      List.Forall₂ eventRel leftEvents rightEvents →
      stateRel
        (left.runFrom problem parameter leftState leftEvents)
        (right.runFrom problem parameter rightState rightEvents)
  | _, _, [], [], statesRelated, .nil => statesRelated
  | leftState, rightState, leftEvent :: leftEvents, rightEvent :: rightEvents,
      statesRelated, .cons eventRelated tailRelated =>
      runFrom_related simulation
        (problem := problem) (parameter := parameter)
        (leftState := left.transition problem parameter leftEvent leftState)
        (rightState := right.transition problem parameter rightEvent rightState)
        (leftEvents := leftEvents) (rightEvents := rightEvents)
        (simulation.transition_related statesRelated eventRelated)
        tailRelated

theorem run_related
    (simulation : TraceSimulation left right eventRel stateRel)
    {problem : Problem} {parameter : Parameter}
    {leftEvents : List Event₁} {rightEvents : List Event₂}
    (eventsRelated : List.Forall₂ eventRel leftEvents rightEvents) :
    stateRel
      (left.run problem parameter leftEvents)
      (right.run problem parameter rightEvents) :=
  runFrom_related simulation
    (simulation.initial_related problem parameter) eventsRelated

theorem traceFrom_related
    (simulation : TraceSimulation left right eventRel stateRel)
    {problem : Problem} {parameter : Parameter} :
    ∀ {leftState : LocalState₁} {rightState : LocalState₂}
      {leftEvents : List Event₁} {rightEvents : List Event₂},
      stateRel leftState rightState →
      List.Forall₂ eventRel leftEvents rightEvents →
      List.Forall₂ stateRel
        (left.traceFrom problem parameter leftState leftEvents)
        (right.traceFrom problem parameter rightState rightEvents)
  | _, _, [], [], statesRelated, .nil => .cons statesRelated .nil
  | leftState, rightState, leftEvent :: leftEvents, rightEvent :: rightEvents,
      statesRelated, .cons eventRelated tailRelated =>
      .cons statesRelated
        (traceFrom_related simulation
          (problem := problem) (parameter := parameter)
          (leftState := left.transition problem parameter leftEvent leftState)
          (rightState := right.transition problem parameter rightEvent rightState)
          (leftEvents := leftEvents) (rightEvents := rightEvents)
          (simulation.transition_related statesRelated eventRelated)
          tailRelated)

theorem trace_related
    (simulation : TraceSimulation left right eventRel stateRel)
    {problem : Problem} {parameter : Parameter}
    {leftEvents : List Event₁} {rightEvents : List Event₂}
    (eventsRelated : List.Forall₂ eventRel leftEvents rightEvents) :
    List.Forall₂ stateRel
      (left.trace problem parameter leftEvents)
      (right.trace problem parameter rightEvents) :=
  traceFrom_related simulation
    (simulation.initial_related problem parameter) eventsRelated

private theorem mapped_signals_eq
    (simulation : TraceSimulation left right eventRel stateRel)
    {problem : Problem} {parameter : Parameter} :
    ∀ {leftStates : List LocalState₁} {rightStates : List LocalState₂},
      List.Forall₂ stateRel leftStates rightStates →
      leftStates.map (left.signal problem parameter) =
        rightStates.map (right.signal problem parameter)
  | _, _, .nil => rfl
  | _, _, .cons stateRelated tailRelated => by
      simp only [List.map_cons]
      rw [simulation.signal_eq stateRelated,
        mapped_signals_eq simulation tailRelated]

theorem signal_traces_eq
    (simulation : TraceSimulation left right eventRel stateRel)
    {problem : Problem} {parameter : Parameter}
    {leftEvents : List Event₁} {rightEvents : List Event₂}
    (eventsRelated : List.Forall₂ eventRel leftEvents rightEvents) :
    left.signalTrace problem parameter leftEvents =
      right.signalTrace problem parameter rightEvents := by
  exact mapped_signals_eq simulation (trace_related simulation eventsRelated)

theorem finiteTrajectoryEquivalent
    (simulation : TraceSimulation left right eventRel stateRel) :
    FiniteTrajectoryEquivalent left right eventRel stateRel where
  run_related := fun eventsRelated => run_related simulation eventsRelated
  signal_traces_eq := fun eventsRelated => signal_traces_eq simulation eventsRelated

end TraceSimulation

/-- Finite trajectory equivalence yields update equivalence only when the
readout preserves the witnessed terminal-state relation. -/
theorem FiniteTrajectoryEquivalent.parameterUpdateEquivalent
    {left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update}
    {right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update}
    {eventRel : Event₁ → Event₂ → Prop}
    {stateRel : LocalState₁ → LocalState₂ → Prop}
    (finite : FiniteTrajectoryEquivalent left right eventRel stateRel)
    (readout : UpdatePreserving left right stateRel) :
    ParameterUpdateEquivalent left right eventRel := by
  intro problem parameter leftEvents rightEvents eventsRelated
  exact readout (finite.run_related eventsRelated)

/-- Equal updates induce equal downstream behavior only through extensionally
equal kernels. -/
theorem ParameterUpdateEquivalent.behavioralSearchEquivalent
    {Behavior : Type uB}
    {left : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update}
    {right : CreditSystem Problem Parameter LocalState₂ Event₂ Signal Update}
    {eventRel : Event₁ → Event₂ → Prop}
    (updates : ParameterUpdateEquivalent left right eventRel)
    (leftKernel rightKernel : BehaviorKernel
      (Problem := Problem) (Parameter := Parameter) (Update := Update) Behavior)
    (kernelsAgree : ∀ problem parameter update behavior,
      leftKernel problem parameter update behavior =
        rightKernel problem parameter update behavior) :
    BehavioralSearchEquivalent left right eventRel leftKernel rightKernel := by
  intro problem parameter leftEvents rightEvents eventsRelated behavior
  rw [updates eventsRelated]
  exact kernelsAgree problem parameter
    (right.finalUpdate problem parameter rightEvents) behavior

theorem ObjectiveEquivalent.refl
    (system : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update) :
    ObjectiveEquivalent system system := by
  intro _ _
  rfl

theorem ParameterUpdateEquivalent.refl
    (system : CreditSystem Problem Parameter LocalState₁ Event₁ Signal Update) :
    ParameterUpdateEquivalent system system Eq := by
  intro problem parameter leftEvents rightEvents eventsRelated
  have : leftEvents = rightEvents := by
    induction eventsRelated with
    | nil => rfl
    | cons eventEq _ ih => simp [eventEq, ih]
  subst rightEvents
  rfl

#print axioms TraceSimulation.runFrom_related
#print axioms TraceSimulation.finiteTrajectoryEquivalent
#print axioms FiniteTrajectoryEquivalent.parameterUpdateEquivalent
#print axioms ParameterUpdateEquivalent.behavioralSearchEquivalent

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
