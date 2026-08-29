import Mettapedia.Cybernetics.MultiscaleGoal
import Mettapedia.GSLT.Core.PolicyFamilySufficiency

/-!
# Multiscale goal and cost control

A coarse scale may steer a finer process only through information available
at its observation.  Goal membership and execution cost are separate policy
questions: a coarse observation may see a preferred region while hiding the
cost needed to reach or maintain it.

This module packages those questions as one dependent policy family and
proves the exact sufficiency criterion.  The coarse readout supports the
family precisely when both the preferred region and the requested cost value
factor through the observer.  This is an information boundary only; it does
not mint transitions, funding, or parallel-wave authority.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.MultiscaleGoalCostControl

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.GSLT.Core

universe uState uView uCost

/-- The two independent questions exposed to a multiscale controller. -/
inductive GoalCostPolicy where
  | preferred
  | cost
deriving DecidableEq, Repr

/-- A cost readout is visible at a scale when it factors through that scale's
observer. -/
def CostVisibleAt {State : Type uState} {View : Type uView}
    {Cost : Type uCost} (cost : State → Cost)
    (observer : Observer State View) : Prop :=
  ∃ coarseCost : View → Cost, ∀ state,
    coarseCost (observer.observe state) = cost state

/-- Goal membership and the requested exact cost as one heterogeneous policy
family. -/
def goalCostFamily {State : Type uState} {Cost : Type uCost}
    (space : ProblemSpace State) (cost : State → Cost) :
    PolicyFamily.{uState, 0, uCost} State where
  Policy := GoalCostPolicy
  Result
    | .preferred => ULift.{uCost} Prop
    | .cost => Cost
  decide
    | .preferred => fun state => ULift.up (state ∈ space.preferredRegion)
    | .cost => cost

/-- Exact multiscale sufficiency: the observer can answer the joint request
if and only if the goal and cost coordinates separately descend to it. -/
theorem supports_goalCostFamily_iff
    {State : Type uState} {View : Type uView} {Cost : Type uCost}
    (space : ProblemSpace State) (cost : State → Cost)
    (observer : Observer State View) :
    (goalCostFamily space cost).SupportsReadout observer.observe ↔
      space.GoalVisibleAt observer ∧ CostVisibleAt cost observer := by
  constructor
  · rintro ⟨realization⟩
    constructor
    · refine ⟨{view | (realization.run .preferred view).down}, ?_⟩
      intro state
      exact iff_of_eq
        (congrArg ULift.down (realization.agrees .preferred state)).symm
    · exact ⟨realization.run .cost, realization.agrees .cost⟩
  · rintro ⟨⟨coarseGoal, recognizes⟩, ⟨coarseCost, recoversCost⟩⟩
    refine ⟨{
      run := fun policy =>
        match policy with
        | .preferred => fun view => ULift.up (view ∈ coarseGoal)
        | .cost => coarseCost
      agrees := ?_ }⟩
    intro policy state
    cases policy with
    | preferred =>
        exact congrArg ULift.up (propext (recognizes state).symm)
    | cost =>
        exact recoversCost state

/-- A scale-level control interface retains the executable factorization,
not merely a Boolean claim that goal and cost happen to be visible. -/
structure Interface {State : Type uState} {View : Type uView}
    (Cost : Type uCost) where
  problem : ProblemSpace State
  cost : State → Cost
  observer : Observer State View
  realization : (goalCostFamily problem cost).ReadoutRealization
    observer.observe

namespace Interface

variable {State : Type uState} {View : Type uView} {Cost : Type uCost}

/-- Read whether a fine state lies in the preferred region through the
admitted coarse observation. -/
def preferred (interface : Interface (State := State) (View := View) Cost)
    (state : State) : Prop :=
  (interface.realization.run .preferred
    (interface.observer.observe state)).down

/-- Read the requested cost through the same admitted coarse observation. -/
def observedCost
    (interface : Interface (State := State) (View := View) Cost)
    (state : State) : Cost :=
  interface.realization.run .cost (interface.observer.observe state)

theorem preferred_agrees
    (interface : Interface (State := State) (View := View) Cost)
    (state : State) :
    interface.preferred state ↔ state ∈ interface.problem.preferredRegion :=
  iff_of_eq (congrArg ULift.down
    (interface.realization.agrees .preferred state))

theorem observedCost_agrees
    (interface : Interface (State := State) (View := View) Cost)
    (state : State) :
    interface.observedCost state = interface.cost state :=
  interface.realization.agrees .cost state

end Interface

/-! ## Positive and negative controls -/

namespace Canary

abbrev State := Bool × Nat

def problem : ProblemSpace State where
  preferredRegion := {state | state.1 = true}

def cost : State → Nat := Prod.snd

def exactObserver : Observer State State := Observer.identity State

/-- Retaining both coordinates supports the joint goal-and-cost request. -/
theorem exactObserver_supports_goal_and_cost :
    (goalCostFamily problem cost).SupportsReadout exactObserver.observe := by
  rw [supports_goalCostFamily_iff]
  constructor
  · exact ⟨problem.preferredRegion, fun _ => Iff.rfl⟩
  · exact ⟨cost, fun _ => rfl⟩

def goalOnlyObserver : Observer State Bool where
  observe := Prod.fst

/-- The coarse observer really can see the selected goal region. -/
theorem goalOnlyObserver_sees_goal :
    problem.GoalVisibleAt goalOnlyObserver := by
  exact ⟨{view | view = true}, fun _ => Iff.rfl⟩

/-- The same observer hides cost: equal coarse views may have distinct fine
costs. -/
theorem goalOnlyObserver_hides_cost :
    ¬ CostVisibleAt cost goalOnlyObserver := by
  rintro ⟨coarseCost, recovers⟩
  have zero := recovers (false, 0)
  have one := recovers (false, 1)
  simp [cost, goalOnlyObserver] at zero one
  omega

/-- Seeing a setpoint is not enough to implement cost-sensitive steering. -/
theorem goalOnlyObserver_refuses_joint_control :
    ¬ (goalCostFamily problem cost).SupportsReadout
      goalOnlyObserver.observe := by
  rw [supports_goalCostFamily_iff]
  exact fun joint => goalOnlyObserver_hides_cost joint.2

end Canary

/-! ## Axiom audit -/

#print axioms supports_goalCostFamily_iff
#print axioms Interface.preferred_agrees
#print axioms Interface.observedCost_agrees
#print axioms Canary.exactObserver_supports_goal_and_cost
#print axioms Canary.goalOnlyObserver_refuses_joint_control

end Mettapedia.Cybernetics.MultiscaleGoalCostControl
