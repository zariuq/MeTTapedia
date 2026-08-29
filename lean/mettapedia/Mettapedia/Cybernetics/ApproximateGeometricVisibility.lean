import Mettapedia.Cybernetics.GeometricGoalCostControl
import Mathlib.Tactic

/-!
# Approximate geometric visibility

Exact factorization through an observer remains the right boundary for
semantic equality and execution authority.  Geometric advice can be useful at
a weaker boundary: the observer reconstructs a value within an authored error
radius.

This module defines proof-relevant approximate value readouts and proves:

* exact visibility embeds at error zero;
* zero-error visibility recovers exact visibility when the geometry separates
  points;
* symmetric geometry bounds the diameter of every observation fibre by twice
  the readout error;
* distance-to-target guidance degrades by at most the same authored error;
* metric-preserving representation changes and observer refinements transport
  approximate readouts; and
* exact goal/cost readout may coexist with approximate value readout without
  granting execution, funding, or choice authority.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateGeometricVisibility

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.Cybernetics.MultiscaleGoalCostControl
open Mettapedia.Cybernetics.GeometricGoalCostControl
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

universe uState uView uFineView uValue uTarget uCost

/-! ## Approximate readouts -/

/-- A proof-relevant value reconstruction whose forward geometric error is
bounded at every represented state.  The orientation matters for directed
geometries: reconstructed value to authored value. -/
structure ApproximateValueReadout
    {State : Type uState} {View : Type uView} {Value : Type uValue}
    (geometry : ValueGeometry Value) (value : State → Value)
    (observer : Observer State View) (error : ℝ) where
  error_nonnegative : 0 ≤ error
  run : View → Value
  agrees : ∀ state,
    geometry.distance (run (observer.observe state)) (value state) ≤ error

/-- Approximate visibility is inhabited by an explicit reconstruction and its
uniform error certificate. -/
def ApproximatelyVisibleAt
    {State : Type uState} {View : Type uView} {Value : Type uValue}
    (geometry : ValueGeometry Value) (value : State → Value)
    (observer : Observer State View) (error : ℝ) : Prop :=
  Nonempty (ApproximateValueReadout geometry value observer error)

/-- The extra separation property needed to turn zero pseudodistance into
equality. -/
def SeparatesPoints
    {Value : Type uValue} (geometry : ValueGeometry Value) : Prop :=
  ∀ first second, geometry.distance first second = 0 → first = second

namespace ApproximateValueReadout

variable {State : Type uState} {View : Type uView} {Value : Type uValue}
variable {geometry : ValueGeometry Value} {value : State → Value}
variable {observer : Observer State View} {error : ℝ}

/-- Exact visibility is the zero-error special case. -/
noncomputable def ofExact (geometry : ValueGeometry Value) (value : State → Value)
    (observer : Observer State View)
    (visible : ValueVisibleAt value observer) :
    ApproximateValueReadout geometry value observer 0 where
  error_nonnegative := le_rfl
  run := Classical.choose visible
  agrees := by
    intro state
    rw [Classical.choose_spec visible state, geometry.self]

/-- In a point-separating geometry, zero-error reconstruction is exact. -/
def toExactOfZero
    (readout : ApproximateValueReadout geometry value observer 0)
    (separates : SeparatesPoints geometry) :
    ValueVisibleAt value observer := by
  refine ⟨readout.run, ?_⟩
  intro state
  apply separates
  exact le_antisymm (readout.agrees state)
    (geometry.nonnegative _ _)

/-- A metric-preserving change of value representation transports the same
error bound. -/
def mapPreserving
    {Target : Type uTarget} (readout : ApproximateValueReadout geometry value
      observer error)
    (targetGeometry : ValueGeometry Target) (translate : Value → Target)
    (preserves : geometry.Preserves targetGeometry translate) :
    ApproximateValueReadout targetGeometry (translate ∘ value) observer error where
  error_nonnegative := readout.error_nonnegative
  run := translate ∘ readout.run
  agrees := by
    intro state
    rw [Function.comp_apply, Function.comp_apply, preserves]
    exact readout.agrees state

/-- A finer observer can reuse a coarse readout whenever its view projects to
the coarse view by a commuting observation triangle. -/
def alongObserverRefinement
    {FineView : Type uFineView}
    (readout : ApproximateValueReadout geometry value observer error)
    (fineObserver : Observer State FineView) (project : FineView → View)
    (commutes : ∀ state,
      project (fineObserver.observe state) = observer.observe state) :
    ApproximateValueReadout geometry value fineObserver error where
  error_nonnegative := readout.error_nonnegative
  run := readout.run ∘ project
  agrees := by
    intro state
    rw [Function.comp_apply, commutes]
    exact readout.agrees state

/-- In symmetric geometry, two states collapsed by one observation cannot be
farther apart than twice the reconstruction radius. -/
theorem fibre_distance_le_two_error
    (readout : ApproximateValueReadout geometry value observer error)
    (symmetric : geometry.Symmetric)
    (first second : State)
    (sameView : observer.observe first = observer.observe second) :
    geometry.distance (value first) (value second) ≤ error + error := by
  let center := readout.run (observer.observe first)
  have firstBound : geometry.distance center (value first) ≤ error :=
    readout.agrees first
  have secondBound : geometry.distance center (value second) ≤ error := by
    dsimp only [center]
    rw [sameView]
    exact readout.agrees second
  calc
    geometry.distance (value first) (value second) ≤
        geometry.distance (value first) center +
          geometry.distance center (value second) :=
      geometry.triangle _ _ _
    _ = geometry.distance center (value first) +
          geometry.distance center (value second) := by
      rw [symmetric (value first) center]
    _ ≤ error + error := add_le_add firstBound secondBound

/-- Approximate distance-to-target guidance has an explicit two-sided error
bound.  This is advice quality, not action authority. -/
theorem targetDistance_bounds
    (readout : ApproximateValueReadout geometry value observer error)
    (symmetric : geometry.Symmetric) (target : Value) (state : State) :
    geometry.distance (readout.run (observer.observe state)) target ≤
        error + geometry.distance (value state) target ∧
      geometry.distance (value state) target ≤
        error + geometry.distance
          (readout.run (observer.observe state)) target := by
  constructor
  · exact le_trans
      (geometry.triangle
        (readout.run (observer.observe state)) (value state) target)
      (add_le_add (readout.agrees state) le_rfl)
  · have reverseError :
        geometry.distance (value state)
          (readout.run (observer.observe state)) ≤ error := by
      rw [symmetric (value state) (readout.run (observer.observe state))]
      exact readout.agrees state
    exact le_trans
      (geometry.triangle (value state)
        (readout.run (observer.observe state)) target)
      (add_le_add reverseError le_rfl)

end ApproximateValueReadout

/-! ## Exact goal/cost with approximate geometric value -/

/-- A controller-facing information interface: goal and cost factor exactly,
while value is reconstructed within an authored geometric radius.  No field
supplies execution, resource, serializability, intervention, or choice
authority. -/
structure ApproximateInterface
    {State : Type uState} {View : Type uView}
    (Cost : Type uCost) (Value : Type uValue) (error : ℝ) where
  problem : ProblemSpace State
  cost : State → Cost
  value : State → Value
  observer : Observer State View
  geometry : ValueGeometry Value
  target : Value
  goalCostReadout : (goalCostFamily problem cost).ReadoutRealization
    observer.observe
  valueReadout : ApproximateValueReadout geometry value observer error

namespace ApproximateInterface

variable {State : Type uState} {View : Type uView}
variable {Cost : Type uCost} {Value : Type uValue} {error : ℝ}

def observedValue
    (interface : ApproximateInterface (State := State) (View := View)
      Cost Value error) (state : State) : Value :=
  interface.valueReadout.run (interface.observer.observe state)

def observedDistance
    (interface : ApproximateInterface (State := State) (View := View)
      Cost Value error) (state : State) : ℝ :=
  interface.geometry.distance (interface.observedValue state) interface.target

/-- The interface inherits the exact geometric degradation bound while
remaining free of operational authority. -/
theorem observedDistance_bounds
    (interface : ApproximateInterface (State := State) (View := View)
      Cost Value error)
    (symmetric : interface.geometry.Symmetric) (state : State) :
    interface.observedDistance state ≤
        error + interface.geometry.distance
          (interface.value state) interface.target ∧
      interface.geometry.distance (interface.value state) interface.target ≤
        error + interface.observedDistance state := by
  simpa [observedDistance, observedValue] using
    interface.valueReadout.targetDistance_bounds symmetric interface.target state

end ApproximateInterface

/-! ## Positive and negative controls -/

namespace Canary

abbrev State := Bool × Bool

def coarseObserver : Observer State Bool where
  observe := Prod.fst

def exactObserver : Observer State State := Observer.identity State

def hiddenValue : State → ℝ :=
  fun state => if state.2 then 1 else 0

noncomputable def realGeometry : ValueGeometry ℝ :=
  ValueGeometry.ofPseudoMetric ℝ

/-- The midpoint reconstructs the hidden Boolean coordinate with radius one
half. -/
noncomputable def halfReadout :
    ApproximateValueReadout realGeometry hiddenValue coarseObserver (1 / 2) where
  error_nonnegative := by norm_num
  run := fun _ => 1 / 2
  agrees := by
    rintro ⟨visible, hidden⟩
    cases hidden <;>
      norm_num [realGeometry, hiddenValue, coarseObserver,
        ValueGeometry.ofPseudoMetric, Real.dist_eq]

theorem half_visible :
    ApproximatelyVisibleAt realGeometry hiddenValue coarseObserver (1 / 2) :=
  ⟨halfReadout⟩

/-- Radius one third is impossible: one coarse fibre contains values at
distance one, exceeding twice the proposed radius. -/
theorem third_not_visible :
    ¬ ApproximatelyVisibleAt realGeometry hiddenValue coarseObserver (1 / 3) := by
  rintro ⟨readout⟩
  have diameter := readout.fibre_distance_le_two_error
    (ValueGeometry.ofPseudoMetric_symmetric ℝ)
    (false, false) (false, true) rfl
  norm_num [realGeometry, hiddenValue, ValueGeometry.ofPseudoMetric,
    Real.dist_eq] at diameter

theorem realGeometry_separates : SeparatesPoints realGeometry := by
  intro first second zeroDistance
  exact dist_eq_zero.mp zeroDistance

theorem exact_value_visible : ValueVisibleAt hiddenValue exactObserver :=
  ⟨hiddenValue, fun _ => rfl⟩

noncomputable def exactZeroReadout :
    ApproximateValueReadout realGeometry hiddenValue exactObserver 0 :=
  ApproximateValueReadout.ofExact realGeometry hiddenValue exactObserver
    exact_value_visible

/-- Zero-error reconstruction returns the ordinary exact visibility witness. -/
theorem zero_recovers_exact : ValueVisibleAt hiddenValue exactObserver :=
  exactZeroReadout.toExactOfZero realGeometry_separates

def problem : ProblemSpace State where
  preferredRegion := {state | state.1 = true}

def cost : State → Nat := fun state => if state.1 then 1 else 0

def coarseCost : Bool → Nat := fun view => if view then 1 else 0

def coarseGoal : Set Bool := {view | view = true}

def coarseGoalCostReadout :
    (goalCostFamily problem cost).ReadoutRealization coarseObserver.observe where
  run := fun policy =>
    match policy with
    | .preferred => fun view => ULift.up (view ∈ coarseGoal)
    | .cost => coarseCost
  agrees := by
    intro policy state
    cases policy with
    | preferred =>
        exact congrArg ULift.up (propext Iff.rfl)
    | cost => rfl

/-- Goal and cost are exactly visible through the first bit while the second
bit remains a radius-one-half geometric estimate. -/
noncomputable def approximateInterface :
    ApproximateInterface (State := State) (View := Bool)
      Nat ℝ (1 / 2) where
  problem := problem
  cost := cost
  value := hiddenValue
  observer := coarseObserver
  geometry := realGeometry
  target := 1
  goalCostReadout := coarseGoalCostReadout
  valueReadout := halfReadout

theorem approximateInterface_guidance_is_bounded (state : State) :
    approximateInterface.observedDistance state ≤
        (1 / 2 : ℝ) + realGeometry.distance (hiddenValue state) 1 ∧
      realGeometry.distance (hiddenValue state) 1 ≤
        (1 / 2 : ℝ) + approximateInterface.observedDistance state :=
  approximateInterface.observedDistance_bounds
    (ValueGeometry.ofPseudoMetric_symmetric ℝ) state

end Canary

/-! ## Axiom audit -/

#print axioms ApproximateValueReadout.ofExact
#print axioms ApproximateValueReadout.toExactOfZero
#print axioms ApproximateValueReadout.mapPreserving
#print axioms ApproximateValueReadout.alongObserverRefinement
#print axioms ApproximateValueReadout.fibre_distance_le_two_error
#print axioms ApproximateValueReadout.targetDistance_bounds
#print axioms ApproximateInterface.observedDistance_bounds
#print axioms Canary.half_visible
#print axioms Canary.third_not_visible
#print axioms Canary.zero_recovers_exact
#print axioms Canary.approximateInterface_guidance_is_bounded

end Mettapedia.Cybernetics.ApproximateGeometricVisibility
