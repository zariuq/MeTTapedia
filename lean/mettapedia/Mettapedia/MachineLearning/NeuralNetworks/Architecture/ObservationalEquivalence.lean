import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.Recurrent

/-!
# Finite policy observations of state carriers

This module begins the carrier-equivalence ladder at its weakest finite levels.
It distinguishes agreement after one command from agreement over every finite
command schedule and supplies a concrete counterexample to the invalid converse.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

universe uEnvironment uSlow uCommand uPolicy
  uLeftState uLeftRead uLeftRoute uLeftProposal uLeftObservation
  uRightState uRightRead uRightRoute uRightProposal uRightObservation

open StateCarrier

section HeterogeneousCarriers

variable
  {Environment : Type uEnvironment} {Slow : Type uSlow}
  {Command : Type uCommand} {Policy : Type uPolicy}
  {LeftState : Type uLeftState} {LeftRead : Type uLeftRead}
  {LeftRoute : Type uLeftRoute} {LeftProposal : Type uLeftProposal}
  {LeftObservation : Type uLeftObservation}
  {RightState : Type uRightState} {RightRead : Type uRightRead}
  {RightRoute : Type uRightRoute} {RightProposal : Type uRightProposal}
  {RightObservation : Type uRightObservation}

/-- Two carriers agree observationally for one command when their complete
initial-plus-one-step policy traces agree for every immutable input and command.
Internal carrier types may differ. -/
def InitialOneStepPolicyEquivalent
    (left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy) : Prop :=
  ∀ environment slow command,
    left.policyTrajectoryFromInitial environment slow [command] =
      right.policyTrajectoryFromInitial environment slow [command]

/-- Two carriers agree at the finite policy-trajectory level when every finite
command schedule induces the same initial and subsequent policy readouts. -/
def FinitePolicyTrajectoryEquivalent
    (left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy)
    (right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy) : Prop :=
  ∀ environment slow commands,
    left.policyTrajectoryFromInitial environment slow commands =
      right.policyTrajectoryFromInitial environment slow commands

/-- Agreement on all finite policy trajectories includes agreement after one
command. -/
theorem finitePolicyTrajectoryEquivalent_implies_initialOneStep
    {left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy}
    {right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy}
    (equivalent : FinitePolicyTrajectoryEquivalent left right) :
    InitialOneStepPolicyEquivalent left right := by
  intro environment slow command
  exact equivalent environment slow [command]

/-- A policy-preserving state simulation supplies finite policy-trajectory
equivalence, even when the two state representations differ. -/
theorem StateCarrier.PolicySimulation.finitePolicyTrajectoryEquivalent
    {left : StateCarrier Environment Slow Command LeftState LeftRead LeftRoute
      LeftProposal LeftObservation Policy}
    {right : StateCarrier Environment Slow Command RightState RightRead RightRoute
      RightProposal RightObservation Policy}
    (simulation : StateCarrier.PolicySimulation left right) :
    FinitePolicyTrajectoryEquivalent left right := by
  intro environment slow commands
  exact simulation.policyTrajectoryFromInitial_eq environment slow commands

end HeterogeneousCarriers

/-! ## Strictness of the first implication -/

/-- A counter that advances once under every command. -/
def successorCarrier :
    StateCarrier Unit Unit Unit Nat Nat Unit Nat Nat Nat :=
  replacementCarrier
    (fun _environment _slow => 0)
    (fun _environment _slow _command state => state + 1)
    (fun _environment _slow state => state)
    (fun _environment _slow observation => observation)

/-- A recurrence that agrees with `successorCarrier` on its first step and then
jumps to three. -/
def delayedJumpCarrier :
    StateCarrier Unit Unit Unit Nat Nat Unit Nat Nat Nat :=
  replacementCarrier
    (fun _environment _slow => 0)
    (fun _environment _slow _command state =>
      match state with
      | 0 => 1
      | _ + 1 => 3)
    (fun _environment _slow state => state)
    (fun _environment _slow observation => observation)

/-- The two concrete carriers have exactly the same policy trace through their
first command. -/
theorem successor_delayedJump_initialOneStep :
    InitialOneStepPolicyEquivalent successorCarrier delayedJumpCarrier := by
  intro environment slow command
  rfl

/-- Their second-step policies differ, so one-step agreement cannot license a
finite-trajectory claim. -/
theorem successor_delayedJump_not_finite :
    ¬ FinitePolicyTrajectoryEquivalent successorCarrier delayedJumpCarrier := by
  intro equivalent
  simpa [FinitePolicyTrajectoryEquivalent, StateCarrier.policyTrajectoryFromInitial,
    StateCarrier.policyTrajectory, StateCarrier.trajectory,
    StateCarrier.policyAtState, StateCarrier.observeAtState, successorCarrier,
    delayedJumpCarrier, replacementCarrier, StateCarrier.step] using
    equivalent () () [(), ()]

/-- The first observational implication is strict. -/
theorem initialOneStep_does_not_imply_finite :
    InitialOneStepPolicyEquivalent successorCarrier delayedJumpCarrier ∧
      ¬ FinitePolicyTrajectoryEquivalent successorCarrier delayedJumpCarrier :=
  ⟨successor_delayedJump_initialOneStep, successor_delayedJump_not_finite⟩

/-- The tagged/scalar simulation is a positive heterogeneous instance of the
stronger finite observational level. -/
theorem moving_tagged_finitePolicyTrajectoryEquivalent :
    FinitePolicyTrajectoryEquivalent movingScalarCarrier taggedMovingCarrier :=
  movingTaggedSimulation.finitePolicyTrajectoryEquivalent

#print axioms finitePolicyTrajectoryEquivalent_implies_initialOneStep
#print axioms StateCarrier.PolicySimulation.finitePolicyTrajectoryEquivalent
#print axioms initialOneStep_does_not_imply_finite
#print axioms moving_tagged_finitePolicyTrajectoryEquivalent

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
