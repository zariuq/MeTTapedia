import Mettapedia.Cybernetics.MultiscaleGoalCostControl
import Mettapedia.GSLT.Dynamics.TypedValueGeometry

/-!
# Geometric goal, cost, and value control

A controller may use a geometric value only at a scale where that value is
recoverable.  Goal membership, spent or predicted cost, and geometric value
are three independent questions.  This module combines them in one dependent
policy family and proves that the family factors through an observer exactly
when all three coordinates factor separately.

The resulting interface can compute a distance to an authored target through
the coarse observation.  It still grants no transition, funding, batch
serializability, or choice authority.  Those remain separate certificates.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.GeometricGoalCostControl

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.Cybernetics.MultiscaleGoalCostControl
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

universe uState uView uPayload

/-! ## A three-coordinate observation request -/

inductive GoalCostValuePolicy where
  | preferred
  | cost
  | value
deriving DecidableEq, Repr

/-- A value is visible when it factors through the observer. -/
def ValueVisibleAt {State : Type uState} {View : Type uView}
    {Value : Type uPayload} (value : State → Value)
    (observer : Observer State View) : Prop :=
  ∃ coarseValue : View → Value, ∀ state,
    coarseValue (observer.observe state) = value state

/-- Goal membership, cost, and a typed value as one heterogeneous request. -/
def goalCostValueFamily
    {State : Type uState} {Cost Value : Type uPayload}
    (space : ProblemSpace State) (cost : State → Cost)
    (value : State → Value) :
    PolicyFamily.{uState, 0, uPayload} State where
  Policy := GoalCostValuePolicy
  Result
    | .preferred => ULift.{uPayload} Prop
    | .cost => Cost
    | .value => Value
  decide
    | .preferred => fun state => ULift.up (state ∈ space.preferredRegion)
    | .cost => cost
    | .value => value

/-- Exact sufficiency for geometric control at one observation scale. -/
theorem supports_goalCostValueFamily_iff
    {State : Type uState} {View : Type uView}
    {Cost Value : Type uPayload}
    (space : ProblemSpace State) (cost : State → Cost)
    (value : State → Value) (observer : Observer State View) :
    (goalCostValueFamily space cost value).SupportsReadout observer.observe ↔
      space.GoalVisibleAt observer ∧ CostVisibleAt cost observer ∧
        ValueVisibleAt value observer := by
  constructor
  · rintro ⟨realization⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨{view | (realization.run .preferred view).down}, ?_⟩
      intro state
      exact iff_of_eq
        (congrArg ULift.down
          (realization.agrees .preferred state)).symm
    · exact ⟨realization.run .cost, realization.agrees .cost⟩
    · exact ⟨realization.run .value, realization.agrees .value⟩
  · rintro ⟨⟨coarseGoal, recognizes⟩, ⟨coarseCost, recoversCost⟩,
      ⟨coarseValue, recoversValue⟩⟩
    refine ⟨{
      run := fun policy =>
        match policy with
        | .preferred => fun view => ULift.up (view ∈ coarseGoal)
        | .cost => coarseCost
        | .value => coarseValue
      agrees := ?_ }⟩
    intro policy state
    cases policy with
    | preferred =>
        exact congrArg ULift.up (propext (recognizes state).symm)
    | cost => exact recoversCost state
    | value => exact recoversValue state

/-! ## Executable geometric interface -/

/-- All data needed to compute a geometric recommendation at one observation
scale.  This is information, not permission. -/
structure Interface {State : Type uState} {View : Type uView}
    (Cost Value : Type uPayload) where
  problem : ProblemSpace State
  cost : State → Cost
  value : State → Value
  observer : Observer State View
  geometry : ValueGeometry Value
  target : Value
  realization : (goalCostValueFamily problem cost value).ReadoutRealization
    observer.observe

namespace Interface

variable {State : Type uState} {View : Type uView}
variable {Cost Value : Type uPayload}

def preferred (interface : Interface (State := State) (View := View)
    Cost Value) (state : State) : Prop :=
  (interface.realization.run .preferred
    (interface.observer.observe state)).down

def observedCost (interface : Interface (State := State) (View := View)
    Cost Value) (state : State) : Cost :=
  interface.realization.run .cost (interface.observer.observe state)

def observedValue (interface : Interface (State := State) (View := View)
    Cost Value) (state : State) : Value :=
  interface.realization.run .value (interface.observer.observe state)

/-- Distance-to-target guidance computed entirely through the admitted
observation. -/
def observedDistance (interface : Interface (State := State) (View := View)
    Cost Value) (state : State) : ℝ :=
  interface.geometry.distance (interface.observedValue state) interface.target

theorem preferred_agrees
    (interface : Interface (State := State) (View := View) Cost Value)
    (state : State) :
    interface.preferred state ↔ state ∈ interface.problem.preferredRegion :=
  iff_of_eq (congrArg ULift.down
    (interface.realization.agrees .preferred state))

theorem observedCost_agrees
    (interface : Interface (State := State) (View := View) Cost Value)
    (state : State) :
    interface.observedCost state = interface.cost state :=
  interface.realization.agrees .cost state

theorem observedValue_agrees
    (interface : Interface (State := State) (View := View) Cost Value)
    (state : State) :
    interface.observedValue state = interface.value state :=
  interface.realization.agrees .value state

theorem observedDistance_agrees
    (interface : Interface (State := State) (View := View) Cost Value)
    (state : State) :
    interface.observedDistance state =
      interface.geometry.distance (interface.value state) interface.target := by
  rw [observedDistance, observedValue_agrees]

end Interface

/-! ## Forgetting geometry recovers ordinary goal/cost control -/

/-- A three-coordinate realization restricts to the existing goal/cost
interface without recomputing either coordinate. -/
def forgetValueReadout
    {State : Type uState} {View : Type uView}
    {Cost Value : Type uPayload}
    {space : ProblemSpace State} {cost : State → Cost}
    {value : State → Value} {observe : State → View}
    (realization : (goalCostValueFamily space cost value).ReadoutRealization
      observe) :
    (goalCostFamily space cost).ReadoutRealization observe where
  run
    | .preferred => realization.run .preferred
    | .cost => realization.run .cost
  agrees policy state := by
    cases policy with
    | preferred => exact realization.agrees .preferred state
    | cost => exact realization.agrees .cost state

/-! ## Positive and negative controls -/

namespace Canary

abbrev State := Bool × Nat × Bool
abbrev CoarseView := Bool × Nat

def problem : ProblemSpace State where
  preferredRegion := {state | state.1 = true}

def cost : State → Nat := fun state => state.2.1
def value : State → Bool := fun state => state.2.2

def exactObserver : Observer State State := Observer.identity State

def coarseObserver : Observer State CoarseView where
  observe := fun state => (state.1, state.2.1)

/-- The coarse observer retains both the goal bit and exact cost. -/
theorem coarse_sees_goal_and_cost :
    problem.GoalVisibleAt coarseObserver ∧ CostVisibleAt cost coarseObserver := by
  constructor
  · exact ⟨{view | view.1 = true}, fun _ => Iff.rfl⟩
  · exact ⟨Prod.snd, fun _ => rfl⟩

/-- It cannot recover the independent value bit. -/
theorem coarse_hides_value :
    ¬ ValueVisibleAt value coarseObserver := by
  rintro ⟨coarseValue, recovers⟩
  have falseValue := recovers (false, 0, false)
  have trueValue := recovers (false, 0, true)
  simp [value, coarseObserver] at falseValue trueValue
  rw [falseValue] at trueValue
  exact Bool.false_ne_true trueValue

/-- Goal and cost visibility do not counterfeit geometric visibility. -/
theorem coarse_refuses_geometric_control :
    ¬ (goalCostValueFamily problem cost value).SupportsReadout
      coarseObserver.observe := by
  rw [supports_goalCostValueFamily_iff]
  exact fun supported => coarse_hides_value supported.2.2

/-- The exact observer supports all three coordinates. -/
theorem exact_supports_geometric_control :
    (goalCostValueFamily problem cost value).SupportsReadout
      exactObserver.observe := by
  rw [supports_goalCostValueFamily_iff]
  exact ⟨⟨problem.preferredRegion, fun _ => Iff.rfl⟩,
    ⟨cost, fun _ => rfl⟩, ⟨value, fun _ => rfl⟩⟩

end Canary

/-! ## Axiom audit -/

#print axioms supports_goalCostValueFamily_iff
#print axioms Interface.observedDistance_agrees
#print axioms forgetValueReadout
#print axioms Canary.coarse_refuses_geometric_control
#print axioms Canary.exact_supports_geometric_control

end Mettapedia.Cybernetics.GeometricGoalCostControl
