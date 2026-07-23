import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.Recurrent

/-!
# Carrier execution semantics

Scheduled execution, fixed-point settling, and itinerant execution describe
fast-state behavior.  They are independent of the rule used to train slow
parameters.  This module gives the first exact boundaries between fixed states
and nontrivial observation itineraries.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open StateCarrier

/-- Names for the three execution regimes; substantive claims use the
predicates below rather than this tag alone. -/
inductive CarrierExecutionKind where
  | scheduled
  | fixedPoint
  | itinerant
  deriving DecidableEq

universe uEnvironment uSlow uCommand uState uRead uRoute uProposal
  uObservation uPolicy

variable {Environment : Type uEnvironment} {Slow : Type uSlow}
  {Command : Type uCommand} {State : Type uState} {Read : Type uRead}
  {Route : Type uRoute} {Proposal : Type uProposal}
  {Observation : Type uObservation} {Policy : Type uPolicy}

/-- A state is fixed relative to one command and immutable context. -/
def CommandFixedPoint
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : State) : Prop :=
  carrier.step environment slow command state = state

/-- An execution realizes an itinerary when its complete observation trace,
including the initial observation, is exactly the declared trace. -/
def RealizesObservationItinerary
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (initial : State)
    (commands : List Command) (expected : List Observation) : Prop :=
  carrier.observationTrajectory environment slow initial commands = expected

/-- Repeated execution from a command-relative fixed point cannot move. -/
theorem run_replicate_eq_of_commandFixedPoint
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : State) (fixed : CommandFixedPoint carrier environment slow command state) :
    ∀ count,
      carrier.run environment slow state (List.replicate count command) = state
  | 0 => rfl
  | count + 1 => by
      rw [List.replicate_succ, StateCarrier.run_cons, fixed]
      exact run_replicate_eq_of_commandFixedPoint carrier environment slow
        command state fixed count

/-- Repeated execution from a fixed point yields a constant state trajectory. -/
theorem fixedPoint_repeated_trajectory
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : State) (fixed : CommandFixedPoint carrier environment slow command state) :
    ∀ count,
      carrier.trajectory environment slow state (List.replicate count command) =
        List.replicate (count + 1) state
  | 0 => rfl
  | count + 1 => by
      unfold CommandFixedPoint at fixed
      rw [List.replicate_succ]
      simp only [StateCarrier.trajectory_cons, fixed]
      rw [fixedPoint_repeated_trajectory carrier environment slow command state
        fixed count]
      simp only [List.replicate_succ]

/-- Repeated execution from a fixed point yields a constant observation
itinerary. -/
theorem fixedPoint_repeated_observationTrajectory
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : State) (fixed : CommandFixedPoint carrier environment slow command state)
    (count : Nat) :
    carrier.observationTrajectory environment slow state
        (List.replicate count command) =
      List.replicate (count + 1) (carrier.observeAtState environment slow state) := by
  simp [StateCarrier.observationTrajectory,
    fixedPoint_repeated_trajectory carrier environment slow command state fixed]

/-- A command-relative fixed point cannot realize even a one-step observation
change under that command.  This is the minimal directionality obstruction. -/
theorem commandFixedPoint_cannot_realize_observation_change
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : State) (nextObservation : Observation)
    (fixed : CommandFixedPoint carrier environment slow command state)
    (changes : nextObservation ≠
      carrier.observeAtState environment slow state) :
    ¬ RealizesObservationItinerary carrier environment slow state [command]
      [carrier.observeAtState environment slow state, nextObservation] := by
  intro realizes
  unfold RealizesObservationItinerary at realizes
  unfold CommandFixedPoint at fixed
  simp only [StateCarrier.observationTrajectory, StateCarrier.trajectory,
    fixed, List.map_cons, List.map_nil] at realizes
  have tailsEqual := (List.cons.inj realizes).2
  have observationsEqual := (List.cons.inj tailsEqual).1
  exact changes observationsEqual.symm

/-! ## Executable separation fixtures -/

/-- The moving recurrent carrier realizes a nonconstant three-state
itinerary under two repeated zero commands. -/
theorem movingScalarCarrier_realizes_nonconstant_itinerary :
    RealizesObservationItinerary movingScalarCarrier () () 0 [0, 0]
      [0, 1, 2] := rfl

/-- Its terminal state is not a fixed point under the same command. -/
theorem movingScalarCarrier_terminal_not_fixed :
    ¬ CommandFixedPoint movingScalarCarrier () () 0 2 := by
  simp [CommandFixedPoint, movingScalarCarrier, replacementCarrier,
    StateCarrier.step]

/-- Every frozen-carrier state is fixed under every command. -/
theorem frozenScalarCarrier_all_fixed (command state : Nat) :
    CommandFixedPoint frozenScalarCarrier () () command state :=
  frozenScalarCarrier_step_eq command state

/-- A fixed-point carrier cannot realize the moving carrier's nonconstant
itinerary from the same initial observation. -/
theorem frozenScalarCarrier_not_moving_itinerary :
    ¬ RealizesObservationItinerary frozenScalarCarrier () () 0 [0, 0]
      [0, 1, 2] := by
  simp [RealizesObservationItinerary, StateCarrier.observationTrajectory,
    StateCarrier.trajectory, StateCarrier.observeAtState, frozenScalarCarrier,
    replacementCarrier, StateCarrier.step]

/-- The examples establish that a nontrivial itinerary need not terminate at
a fixed point, while a repeated fixed-point execution cannot realize it. -/
theorem itinerary_and_fixedPoint_are_distinct_obligations :
    RealizesObservationItinerary movingScalarCarrier () () 0 [0, 0]
        [0, 1, 2] ∧
      ¬ CommandFixedPoint movingScalarCarrier () () 0 2 ∧
      ¬ RealizesObservationItinerary frozenScalarCarrier () () 0 [0, 0]
        [0, 1, 2] :=
  ⟨movingScalarCarrier_realizes_nonconstant_itinerary,
    movingScalarCarrier_terminal_not_fixed,
    frozenScalarCarrier_not_moving_itinerary⟩

#print axioms run_replicate_eq_of_commandFixedPoint
#print axioms fixedPoint_repeated_trajectory
#print axioms fixedPoint_repeated_observationTrajectory
#print axioms commandFixedPoint_cannot_realize_observation_change
#print axioms movingScalarCarrier_realizes_nonconstant_itinerary
#print axioms movingScalarCarrier_terminal_not_fixed
#print axioms frozenScalarCarrier_not_moving_itinerary
#print axioms itinerary_and_fixedPoint_are_distinct_obligations

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
