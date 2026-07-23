import Mathlib.Data.List.Defs

/-!
# A common fast-state carrier interface

This module separates fast-state recurrence from parameter plasticity and from
checker-owned legality.  A carrier exposes its read, route, proposal, and write
stages instead of hiding them inside one opaque transition.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

universe uEnvironment uSlow uCommand uState uRead uRoute uProposal
  uObservation uPolicy

/-- A structured fast-state carrier.  `Environment` and `Slow` are immutable
arguments to one recurrence; only `State` is returned by `step`.  Legality and
checker acceptance deliberately do not occur in this interface. -/
structure StateCarrier
    (Environment : Type uEnvironment) (Slow : Type uSlow)
    (Command : Type uCommand) (State : Type uState) (Read : Type uRead)
    (Route : Type uRoute) (Proposal : Type uProposal)
    (Observation : Type uObservation) (Policy : Type uPolicy) where
  initialState : Environment → Slow → State
  read : Environment → Slow → State → Read
  route : Environment → Slow → Command → State → Read → Route
  propose : Environment → Slow → Command → State → Read → Route → Proposal
  write : Environment → Slow → Command → State → Route → Proposal → State
  observe : Environment → Slow → State → Observation
  policy : Environment → Slow → Observation → Policy

namespace StateCarrier

variable {Environment : Type uEnvironment} {Slow : Type uSlow}
  {Command : Type uCommand} {State : Type uState} {Read : Type uRead}
  {Route : Type uRoute} {Proposal : Type uProposal}
  {Observation : Type uObservation} {Policy : Type uPolicy}

/-- One structured carrier transition. -/
def step
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : State) : State :=
  let read := carrier.read environment slow state
  let route := carrier.route environment slow command state read
  let proposal := carrier.propose environment slow command state read route
  carrier.write environment slow command state route proposal

/-- Fold a command schedule from an explicitly supplied initial state. -/
def run
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State) :
    List Command → State
  | [] => state
  | command :: commands =>
      carrier.run environment slow
        (carrier.step environment slow command state) commands

/-- Run a schedule from the carrier's own initializer. -/
def runFromInitial
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (commands : List Command) : State :=
  carrier.run environment slow (carrier.initialState environment slow) commands

/-- The initial state followed by the state after every command. -/
def trajectory
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State) :
    List Command → List State
  | [] => [state]
  | command :: commands =>
      state :: carrier.trajectory environment slow
        (carrier.step environment slow command state) commands

/-- A trajectory starting from `initialize`. -/
def trajectoryFromInitial
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (commands : List Command) :
    List State :=
  carrier.trajectory environment slow (carrier.initialState environment slow)
    commands

/-- Observation obtained from one fast state. -/
def observeAtState
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State) : Observation :=
  carrier.observe environment slow state

/-- Policy obtained from one fast state through the declared observation. -/
def policyAtState
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State) : Policy :=
  carrier.policy environment slow (carrier.observeAtState environment slow state)

/-- Observe every state, including the initial state. -/
def observationTrajectory
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State)
    (commands : List Command) : List Observation :=
  (carrier.trajectory environment slow state commands).map
    (carrier.observeAtState environment slow)

/-- Read out a policy at every state, including the initial state. -/
def policyTrajectory
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State)
    (commands : List Command) : List Policy :=
  (carrier.trajectory environment slow state commands).map
    (carrier.policyAtState environment slow)

/-- Read out a policy trajectory from the carrier's declared initial state. -/
def policyTrajectoryFromInitial
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (commands : List Command) :
    List Policy :=
  carrier.policyTrajectory environment slow
    (carrier.initialState environment slow) commands

@[simp] theorem run_nil
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State) :
    carrier.run environment slow state [] = state := rfl

@[simp] theorem run_cons
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State)
    (command : Command) (commands : List Command) :
    carrier.run environment slow state (command :: commands) =
      carrier.run environment slow
        (carrier.step environment slow command state) commands := rfl

/-- Schedule concatenation agrees with sequential execution. -/
theorem run_append
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State)
    (first second : List Command) :
    carrier.run environment slow state (first ++ second) =
      carrier.run environment slow
        (carrier.run environment slow state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      exact inductionHypothesis
        (carrier.step environment slow command state)

@[simp] theorem trajectory_nil
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State) :
    carrier.trajectory environment slow state [] = [state] := rfl

@[simp] theorem trajectory_cons
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State)
    (command : Command) (commands : List Command) :
    carrier.trajectory environment slow state (command :: commands) =
      state :: carrier.trajectory environment slow
        (carrier.step environment slow command state) commands := rfl

/-- Every trajectory contains exactly one more state than commands. -/
theorem trajectory_length
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State)
    (commands : List Command) :
    (carrier.trajectory environment slow state commands).length =
      commands.length + 1 := by
  induction commands generalizing state with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      simp only [trajectory_cons, List.length_cons, inductionHypothesis]

/-- The first trajectory element is the supplied initial state. -/
theorem trajectory_head?
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State)
    (commands : List Command) :
    (carrier.trajectory environment slow state commands).head? = some state := by
  cases commands <;> rfl

/-! ## Policy-preserving simulations -/

universe uLeftState uLeftRead uLeftRoute uLeftProposal uLeftObservation
  uRightState uRightRead uRightRoute uRightProposal uRightObservation

/-- A relation-preserving simulation between two carriers that share their
immutable inputs, command language, and policy codomain.  Internal states,
reads, routes, proposals, and observations may all differ. -/
structure PolicySimulation
    {LeftState : Type uLeftState} {LeftRead : Type uLeftRead}
    {LeftRoute : Type uLeftRoute} {LeftProposal : Type uLeftProposal}
    {LeftObservation : Type uLeftObservation}
    {RightState : Type uRightState} {RightRead : Type uRightRead}
    {RightRoute : Type uRightRoute} {RightProposal : Type uRightProposal}
    {RightObservation : Type uRightObservation}
    (left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy) where
  Rel : LeftState → RightState → Prop
  initialize_related : ∀ environment slow,
    Rel (left.initialState environment slow) (right.initialState environment slow)
  step_related : ∀ environment slow command leftState rightState,
    Rel leftState rightState →
      Rel (left.step environment slow command leftState)
        (right.step environment slow command rightState)
  policy_related : ∀ environment slow leftState rightState,
    Rel leftState rightState →
      left.policyAtState environment slow leftState =
        right.policyAtState environment slow rightState

namespace PolicySimulation

variable
  {LeftState : Type uLeftState} {LeftRead : Type uLeftRead}
  {LeftRoute : Type uLeftRoute} {LeftProposal : Type uLeftProposal}
  {LeftObservation : Type uLeftObservation}
  {RightState : Type uRightState} {RightRead : Type uRightRead}
  {RightRoute : Type uRightRoute} {RightProposal : Type uRightProposal}
  {RightObservation : Type uRightObservation}
  {left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
    LeftProposal LeftObservation Policy}
  {right : StateCarrier Environment Slow Command RightState RightRead RightRoute
    RightProposal RightObservation Policy}

/-- A simulation relation is preserved by every finite command schedule. -/
theorem run_related
    (simulation : PolicySimulation left right)
    (environment : Environment) (slow : Slow)
    {leftState : LeftState} {rightState : RightState}
    (related : simulation.Rel leftState rightState)
    (commands : List Command) :
    simulation.Rel (left.run environment slow leftState commands)
      (right.run environment slow rightState commands) := by
  induction commands generalizing leftState rightState with
  | nil => exact related
  | cons command commands inductionHypothesis =>
      exact inductionHypothesis
        (simulation.step_related environment slow command leftState rightState
          related)

/-- Related initial states remain related after every finite schedule. -/
theorem runFromInitial_related
    (simulation : PolicySimulation left right)
    (environment : Environment) (slow : Slow) (commands : List Command) :
    simulation.Rel (left.runFromInitial environment slow commands)
      (right.runFromInitial environment slow commands) :=
  simulation.run_related environment slow
    (simulation.initialize_related environment slow) commands

/-- Related carrier states generate pointwise-related state trajectories. -/
theorem trajectory_related
    (simulation : PolicySimulation left right)
    (environment : Environment) (slow : Slow)
    {leftState : LeftState} {rightState : RightState}
    (related : simulation.Rel leftState rightState)
    (commands : List Command) :
    List.Forall₂ simulation.Rel
      (left.trajectory environment slow leftState commands)
      (right.trajectory environment slow rightState commands) := by
  induction commands generalizing leftState rightState with
  | nil => exact .cons related .nil
  | cons command commands inductionHypothesis =>
      exact .cons related <| inductionHypothesis <|
        simulation.step_related environment slow command leftState rightState
          related

/-- Policy-preserving simulation implies equality of every finite policy
trajectory, despite possibly different internal state representations. -/
theorem policyTrajectory_eq
    (simulation : PolicySimulation left right)
    (environment : Environment) (slow : Slow)
    {leftState : LeftState} {rightState : RightState}
    (related : simulation.Rel leftState rightState)
    (commands : List Command) :
    left.policyTrajectory environment slow leftState commands =
      right.policyTrajectory environment slow rightState commands := by
  induction commands generalizing leftState rightState with
  | nil =>
      exact congrArg (fun policy => [policy])
        (simulation.policy_related environment slow leftState rightState related)
  | cons command commands inductionHypothesis =>
      exact congrArg₂ List.cons
        (simulation.policy_related environment slow leftState rightState related)
        (inductionHypothesis <|
          simulation.step_related environment slow command leftState rightState
            related)

/-- Initializer-related carriers have equal policy trajectories for every
finite command schedule. -/
theorem policyTrajectoryFromInitial_eq
    (simulation : PolicySimulation left right)
    (environment : Environment) (slow : Slow) (commands : List Command) :
    left.policyTrajectoryFromInitial environment slow commands =
      right.policyTrajectoryFromInitial environment slow commands :=
  simulation.policyTrajectory_eq environment slow
    (simulation.initialize_related environment slow) commands

end PolicySimulation

end StateCarrier

#print axioms StateCarrier.run_append
#print axioms StateCarrier.trajectory_length
#print axioms StateCarrier.PolicySimulation.run_related
#print axioms StateCarrier.PolicySimulation.policyTrajectory_eq

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
