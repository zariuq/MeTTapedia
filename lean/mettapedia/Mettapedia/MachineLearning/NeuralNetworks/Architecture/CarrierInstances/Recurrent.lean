import Mettapedia.MachineLearning.NeuralNetworks.Architecture.StateCarrier

/-!
# Replacement-write recurrent carriers

This module embeds an ordinary recurrent state transition into the structured
carrier interface.  The examples separate a genuinely moving recurrence from
a frozen recurrence and exhibit policy-equivalent carriers with different
internal state representations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

universe uEnvironment uSlow uCommand uState uObservation uPolicy

open StateCarrier

/-- An ordinary recurrent transition as a carrier whose read is the whole
state, whose route is trivial, and whose proposal replaces the old state. -/
def replacementCarrier
    {Environment : Type uEnvironment} {Slow : Type uSlow}
    {Command : Type uCommand} {State : Type uState}
    {Observation : Type uObservation} {Policy : Type uPolicy}
    (initialState : Environment → Slow → State)
    (transition : Environment → Slow → Command → State → State)
    (observe : Environment → Slow → State → Observation)
    (policy : Environment → Slow → Observation → Policy) :
    StateCarrier Environment Slow Command State State Unit State Observation
      Policy where
  initialState := initialState
  read := fun _environment _slow state => state
  route := fun _environment _slow _command _state _read => ()
  propose := fun environment slow command _state read _route =>
    transition environment slow command read
  write := fun _environment _slow _command _state _route proposal => proposal
  observe := observe
  policy := policy

/-- The structured step of a replacement-write carrier is exactly its supplied
recurrent transition. -/
@[simp] theorem replacementCarrier_step_eq
    {Environment : Type uEnvironment} {Slow : Type uSlow}
    {Command : Type uCommand} {State : Type uState}
    {Observation : Type uObservation} {Policy : Type uPolicy}
    (initialState : Environment → Slow → State)
    (transition : Environment → Slow → Command → State → State)
    (observe : Environment → Slow → State → Observation)
    (policy : Environment → Slow → Observation → Policy)
    (environment : Environment) (slow : Slow) (command : Command)
    (state : State) :
    (replacementCarrier initialState transition observe policy).step
        environment slow command state =
      transition environment slow command state := rfl

/-! ## Concrete moving and frozen recurrences -/

/-- A nontrivial scalar recurrence used as the positive replacement-write
fixture.  Every command contributes its value plus one to the fast state. -/
def movingScalarCarrier :
    StateCarrier Unit Unit Nat Nat Nat Unit Nat Nat Nat :=
  replacementCarrier
    (fun _environment _slow => 0)
    (fun _environment _slow command state => state + command + 1)
    (fun _environment _slow state => state)
    (fun _environment _slow observation => observation)

/-- The moving fixture takes a genuinely non-identity step. -/
example : movingScalarCarrier.step () () 2 0 = 3 := rfl

/-- Three scheduled commands are accumulated by the recurrence. -/
theorem movingScalarCarrier_run_example :
    movingScalarCarrier.runFromInitial () () [0, 1, 2] = 6 := rfl

/-- A replacement-write carrier whose supplied transition freezes its state. -/
def frozenScalarCarrier :
    StateCarrier Unit Unit Nat Nat Nat Unit Nat Nat Nat :=
  replacementCarrier
    (fun _environment _slow => 0)
    (fun _environment _slow _command state => state)
    (fun _environment _slow state => state)
    (fun _environment _slow observation => observation)

/-- Every transition of the frozen fixture is the identity. -/
theorem frozenScalarCarrier_step_eq (command state : Nat) :
    frozenScalarCarrier.step () () command state = state := rfl

/-- The moving fixture is not a disguised frozen carrier. -/
theorem movingScalarCarrier_not_frozen :
    ¬ ∀ command state,
      movingScalarCarrier.step () () command state = state := by
  intro frozen
  exact Nat.one_ne_zero (frozen 0 0)

/-! ## A heterogeneous but policy-equivalent recurrence -/

/-- The same scalar recurrence represented inside a tagged state.  The tag is
preserved but hidden from observation and policy. -/
def taggedMovingCarrier :
    StateCarrier Unit Unit Nat (Bool × Nat) (Bool × Nat) Unit
      (Bool × Nat) Nat Nat :=
  replacementCarrier
    (fun _environment _slow => (true, 0))
    (fun _environment _slow command state =>
      (state.1, state.2 + command + 1))
    (fun _environment _slow state => state.2)
    (fun _environment _slow observation => observation)

/-- Forgetting the private tag relates the two nontrivial recurrences. -/
def movingTaggedSimulation :
    StateCarrier.PolicySimulation movingScalarCarrier taggedMovingCarrier where
  Rel := fun scalar tagged => scalar = tagged.2
  initialize_related := by
    intro environment slow
    rfl
  step_related := by
    intro environment slow command scalar tagged related
    exact congrArg (fun value => value + command + 1) related
  policy_related := by
    intro environment slow scalar tagged related
    exact related

/-- The scalar and tagged implementations expose identical policy trajectories
for every finite schedule, despite unequal internal state types. -/
theorem moving_tagged_policy_trajectories_eq (commands : List Nat) :
    movingScalarCarrier.policyTrajectoryFromInitial () () commands =
      taggedMovingCarrier.policyTrajectoryFromInitial () () commands :=
  movingTaggedSimulation.policyTrajectoryFromInitial_eq () () commands

#print axioms replacementCarrier_step_eq
#print axioms movingScalarCarrier_run_example
#print axioms movingScalarCarrier_not_frozen
#print axioms moving_tagged_policy_trajectories_eq

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
