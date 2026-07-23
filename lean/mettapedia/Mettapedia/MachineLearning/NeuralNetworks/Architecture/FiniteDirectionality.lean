import Mettapedia.MachineLearning.NeuralNetworks.Architecture.AutonomousExecution

/-!
# Finite directionality of autonomous carrier execution

A command-relative fixed point and an autonomously switched carrier are
different execution mechanisms.  This module gives an arbitrary-horizon
boundary: repeated execution of one fixed command realizes exactly the
constant observation itinerary, whereas replaying a finite schedule realizes
exactly that schedule's ordinary observation trace.

The results remain finite and transition-level.  Continuous-time itinerant or
heteroclinic dynamics require additional entry, attraction, dwell, exit, and
halting certificates.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open StateCarrier

universe uEnvironment uSlow uCommand uState uRead uRoute uProposal
  uObservation uPolicy

variable {Environment : Type uEnvironment} {Slow : Type uSlow}
  {Command : Type uCommand} {State : Type uState} {Read : Type uRead}
  {Route : Type uRoute} {Proposal : Type uProposal}
  {Observation : Type uObservation} {Policy : Type uPolicy}

/-- An itinerary contains an observation different from a supplied reference
observation.  For a command-relative fixed point, the reference is the
observation of the fixed state. -/
def ContainsObservationDifferentFrom
    (reference : Observation) (itinerary : List Observation) : Prop :=
  ∃ observation ∈ itinerary, observation ≠ reference

/-- Arbitrary-horizon characterization of repeated fixed-point execution:
the only realizable itinerary is the constant observation trace. -/
theorem commandFixedPoint_realizes_itinerary_iff_eq_replicate
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : State) (fixed : CommandFixedPoint carrier environment slow command state)
    (count : Nat) (expected : List Observation) :
    RealizesObservationItinerary carrier environment slow state
          (List.replicate count command) expected ↔
      expected = List.replicate (count + 1)
        (carrier.observeAtState environment slow state) := by
  unfold RealizesObservationItinerary
  rw [fixedPoint_repeated_observationTrajectory carrier environment slow
    command state fixed count]
  exact eq_comm

/-- A repeated command-relative fixed point cannot realize any finite
itinerary containing an observation different from its initial observation. -/
theorem commandFixedPoint_cannot_realize_nonconstant_itinerary
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : State) (fixed : CommandFixedPoint carrier environment slow command state)
    (count : Nat) (expected : List Observation)
    (nonconstant : ContainsObservationDifferentFrom
      (carrier.observeAtState environment slow state) expected) :
    ¬ RealizesObservationItinerary carrier environment slow state
      (List.replicate count command) expected := by
  intro realizes
  have expectedEq :=
    (commandFixedPoint_realizes_itinerary_iff_eq_replicate carrier environment
      slow command state fixed count expected).1 realizes
  rcases nonconstant with ⟨observation, member, different⟩
  rw [expectedEq] at member
  exact different (List.eq_of_mem_replicate member)

/-- Explicit schedule clamping realizes an itinerary exactly when ordinary
scheduled execution realizes it. -/
theorem replayController_realizes_itinerary_iff [Inhabited Command]
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (state : State)
    (commands : List Command) (expected : List Observation) :
    autonomousObservationTrajectory carrier replayController environment slow
          (commands, state) commands.length = expected ↔
      RealizesObservationItinerary carrier environment slow state commands
        expected := by
  rw [replayController_observation_eq_scheduled]
  rfl

/-- If one carrier is fixed under a chosen command but a finite schedule
realizes a nonconstant itinerary, autonomous replay realizes that itinerary
while repeated fixed-command execution cannot. -/
theorem scheduled_nonconstant_itinerary_separates_autonomous_from_fixed
    [Inhabited Command]
    (carrier : StateCarrier Environment Slow Command State Read Route Proposal
      Observation Policy)
    (environment : Environment) (slow : Slow) (fixedCommand : Command)
    (state : State)
    (fixed : CommandFixedPoint carrier environment slow fixedCommand state)
    (commands : List Command) (expected : List Observation)
    (scheduled : RealizesObservationItinerary carrier environment slow state
      commands expected)
    (nonconstant : ContainsObservationDifferentFrom
      (carrier.observeAtState environment slow state) expected) :
    autonomousObservationTrajectory carrier replayController environment slow
          (commands, state) commands.length = expected ∧
      ¬ RealizesObservationItinerary carrier environment slow state
        (List.replicate commands.length fixedCommand) expected := by
  constructor
  · exact (replayController_realizes_itinerary_iff carrier environment slow
      state commands expected).2 scheduled
  · exact commandFixedPoint_cannot_realize_nonconstant_itinerary carrier
      environment slow fixedCommand state fixed commands.length expected
      nonconstant

/-! ## Same-carrier executable separation -/

/-- One Boolean command freezes the scalar state; the other advances it.
This single carrier therefore supports both command-relative fixed-point and
directed scheduled execution. -/
def gatedDirectionCarrier :
    StateCarrier Unit Unit Bool Nat Nat Unit Nat Nat Nat :=
  replacementCarrier
    (fun _environment _slow => 0)
    (fun _environment _slow command state => if command then state + 1 else state)
    (fun _environment _slow state => state)
    (fun _environment _slow observation => observation)

/-- The false command is stationary at every scalar state. -/
theorem gatedDirectionCarrier_false_fixed (state : Nat) :
    CommandFixedPoint gatedDirectionCarrier () () false state := rfl

/-- Two true commands expose the directed three-observation itinerary. -/
theorem gatedDirectionCarrier_true_schedule_realizes :
    RealizesObservationItinerary gatedDirectionCarrier () () 0 [true, true]
      [0, 1, 2] := rfl

/-- The positive itinerary contains an observation different from its initial
observation. -/
theorem gatedDirectionCarrier_itinerary_nonconstant :
    ContainsObservationDifferentFrom 0 [0, 1, 2] := by
  exact ⟨1, by simp, by decide⟩

/-- Autonomous replay realizes the directed itinerary, while settling under
the fixed false command for the same horizon cannot realize it. -/
theorem gatedDirectionCarrier_autonomous_fixed_separation :
    autonomousObservationTrajectory gatedDirectionCarrier replayController
          () () ([true, true], 0) 2 = [0, 1, 2] ∧
      ¬ RealizesObservationItinerary gatedDirectionCarrier () () 0
        [false, false] [0, 1, 2] := by
  simpa using
    scheduled_nonconstant_itinerary_separates_autonomous_from_fixed
      gatedDirectionCarrier () () false 0
      (gatedDirectionCarrier_false_fixed 0) [true, true] [0, 1, 2]
      gatedDirectionCarrier_true_schedule_realizes
      gatedDirectionCarrier_itinerary_nonconstant

/-- The gated carrier's observations distinguish its two commands. -/
theorem gatedDirectionCarrier_observationSeparatesCommands :
    ObservationSeparatesCommands gatedDirectionCarrier () () := by
  intro state first second equal
  cases first <;> cases second
  · rfl
  · simp [gatedDirectionCarrier, replacementCarrier, StateCarrier.step,
      StateCarrier.observeAtState] at equal
  · simp [gatedDirectionCarrier, replacementCarrier, StateCarrier.step,
      StateCarrier.observeAtState] at equal
  · rfl

/-- Consequently, every internally generated gated-carrier itinerary is
equivalent to an external scheduled itinerary exactly when the internal
controller generated that schedule. -/
theorem gatedDirectionCarrier_internal_external_iff
    {Control : Type*}
    (controller : AutonomousController Unit Unit Bool Nat Control)
    (configuration : AutonomousConfiguration Control Nat)
    (steps : Nat) (commands : List Bool) :
    autonomousObservationTrajectory gatedDirectionCarrier controller () ()
          configuration steps =
        gatedDirectionCarrier.observationTrajectory () () configuration.2
          commands ↔
      generatedCommands gatedDirectionCarrier controller () () configuration
        steps = commands :=
  autonomous_observation_eq_scheduled_iff_generatedCommands_eq
    gatedDirectionCarrier controller () ()
      gatedDirectionCarrier_observationSeparatesCommands configuration steps
      commands

/-! The command-opaque fixture from `AutonomousExecution` remains the negative
boundary: without `ObservationSeparatesCommands`, equal observations do not
identify the controlling schedule. -/

#print axioms commandFixedPoint_realizes_itinerary_iff_eq_replicate
#print axioms commandFixedPoint_cannot_realize_nonconstant_itinerary
#print axioms replayController_realizes_itinerary_iff
#print axioms scheduled_nonconstant_itinerary_separates_autonomous_from_fixed
#print axioms gatedDirectionCarrier_autonomous_fixed_separation
#print axioms gatedDirectionCarrier_observationSeparatesCommands
#print axioms gatedDirectionCarrier_internal_external_iff

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
