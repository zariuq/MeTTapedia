import Mettapedia.Cybernetics.GeometricGoalCostControl
import Mettapedia.Cybernetics.GoalDirectedResourceWave

/-!
# Geometric goal-directed resource waves

This module intersects five independently supplied authorities:

* exact candidate occurrences and their observation demand;
* operational serializability at the declared state observer;
* an exact additive resource decomposition;
* visibility of goal, cost, and a typed geometric value at that observer; and
* membership of the common reference target in the preferred region.

Only their intersection is a geometric goal-directed wave.  The geometric
value can recommend a direction but cannot manufacture any of the execution
or resource certificates.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.GeometricGoalDirectedResourceWave

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.Cybernetics.MultiscaleGoalCostControl
open Mettapedia.Cybernetics.GoalDirectedResourceWave
open Mettapedia.Cybernetics.GeometricGoalCostControl
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

universe uItem uGuard uCandidateView uState uStateView uAccount uPayload

/-- A resource-certified wave whose execution observer can also recover a
typed value and hence a geometric distance to a target. -/
structure GeometricGoalDirectedWave
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {Cost Value : Type uPayload}
    (contract : Contract Item Guard CandidateView)
    (semantics : ExecutionSemantics Item State StateView)
    (initial referenceTarget : State)
    (demand : Item → Account) (source : Account) (batch : List Item)
    (problem : ProblemSpace State) (cost : State → Cost)
    (value : State → Value) where
  certified : CertifiedBatch contract semantics initial referenceTarget
    Account demand source batch
  readout : (goalCostValueFamily problem cost value).ReadoutRealization
    semantics.observe
  targetPreferred : referenceTarget ∈ problem.preferredRegion
  geometry : ValueGeometry Value
  desiredValue : Value

namespace GeometricGoalDirectedWave

variable {Item : Type uItem} {Guard : Type uGuard}
variable {CandidateView : Type uCandidateView}
variable {State : Type uState} {StateView : Type uStateView}
variable {Account : Type uAccount} [AddMonoid Account]
variable {Cost Value : Type uPayload}
variable {contract : Contract Item Guard CandidateView}
variable {semantics : ExecutionSemantics Item State StateView}
variable {initial referenceTarget : State}
variable {demand : Item → Account} {source : Account} {batch : List Item}
variable {problem : ProblemSpace State} {cost : State → Cost}
variable {value : State → Value}

/-- Forget only the value coordinate, retaining the same certified wave. -/
def toGoalDirectedWave
    (wave : GeometricGoalDirectedWave contract semantics initial
      referenceTarget demand source batch problem cost value) :
    GoalDirectedWave contract semantics initial referenceTarget demand source
      batch problem cost where
  certified := wave.certified
  readout := forgetValueReadout wave.readout
  targetPreferred := wave.targetPreferred

/-- Complete-bag demand permits bulk execution only through the retained
generic certificate. -/
theorem completeBag_dispatches_bulk
    (wave : GeometricGoalDirectedWave contract semantics initial
      referenceTarget demand source batch problem cost value)
    (complete : contract.demand.completion = .completeBag) :
    (wave.certified.plan .general).activation = .bulk :=
  wave.certified.completeBag_dispatches_bulk complete

/-- The target's geometric recommendation agrees with the fine-state value. -/
theorem observed_target_distance
    (wave : GeometricGoalDirectedWave contract semantics initial
      referenceTarget demand source batch problem cost value) :
    wave.geometry.distance
        (wave.readout.run .value (semantics.observe referenceTarget))
        wave.desiredValue =
      wave.geometry.distance (value referenceTarget) wave.desiredValue := by
  have observedValue :
      wave.readout.run .value (semantics.observe referenceTarget) =
        value referenceTarget := by
    simpa [goalCostValueFamily] using
      (wave.readout.agrees .value referenceTarget)
  rw [observedValue]

/-- Without a joint goal/cost/value readout, no geometric wave exists at this
observer, regardless of candidate or resource evidence. -/
theorem no_wave_of_invisible
    (invisible : ¬ (goalCostValueFamily problem cost value).SupportsReadout
      semantics.observe) :
    ¬ Nonempty
      (GeometricGoalDirectedWave contract semantics initial referenceTarget
        demand source batch problem cost value) := by
  rintro ⟨wave⟩
  exact invisible ⟨wave.readout⟩

end GeometricGoalDirectedWave

/-! ## Positive and negative controls -/

namespace Canary

abbrev State := Bool × Nat × Bool
abbrev CoarseView := Bool × Nat

def problem : ProblemSpace State where
  preferredRegion := {state | state.1 = true}

def cost : State → Nat := fun state => state.2.1
def value : State → Bool := fun state => state.2.2

def run (_source : State) (items : List Unit) (target : State) : Prop :=
  items = [()] ∧ target = (true, 1, true)

def exactSemantics : ExecutionSemantics Unit State State where
  run := run
  observe := id

def coarseSemantics : ExecutionSemantics Unit State CoarseView where
  run := run
  observe := fun state => (state.1, state.2.1)

def contract : Contract Unit Unit (Multiset Unit) where
  observer := { observe := fun items => (items : Multiset Unit) }
  demand := { completion := .completeBag }

def demand (_item : Unit) : Nat := 1

def exactCertified :
    CertifiedBatch contract exactSemantics (false, 0, false) (true, 1, true)
      Nat demand 1 [()] where
  nonempty := by simp
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · exact ⟨rfl, rfl⟩
    · intro ordering permutation
      have orderingEqual : ordering = [()] := by simpa using permutation
      subst ordering
      exact ⟨(true, 1, true), ⟨rfl, rfl⟩, rfl⟩
  resources :=
    { frame := 0
      source_eq := by simp [batchDemand, demand] }

def coarseCertified :
    CertifiedBatch contract coarseSemantics (false, 0, false) (true, 1, true)
      Nat demand 1 [()] where
  nonempty := by simp
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · exact ⟨rfl, rfl⟩
    · intro ordering permutation
      have orderingEqual : ordering = [()] := by simpa using permutation
      subst ordering
      exact ⟨(true, 1, true), ⟨rfl, rfl⟩, rfl⟩
  resources :=
    { frame := 0
      source_eq := by simp [batchDemand, demand] }

def boolGeometry : ValueGeometry Bool where
  distance first second := if first = second then 0 else 1
  nonnegative := by
    intro first second
    split <;> norm_num
  self := by simp
  triangle := by
    intro first middle last
    cases first <;> cases middle <;> cases last <;> norm_num

def exactReadout :
    (goalCostValueFamily problem cost value).ReadoutRealization
      exactSemantics.observe where
  run
    | .preferred => fun state => ULift.up (state.1 = true)
    | .cost => cost
    | .value => value
  agrees policy state := by
    cases policy <;> rfl

def exactWave :
    GeometricGoalDirectedWave contract exactSemantics (false, 0, false)
      (true, 1, true) demand 1 [()] problem cost value where
  certified := exactCertified
  readout := exactReadout
  targetPreferred := rfl
  geometry := boolGeometry
  desiredValue := true

/-- Positive control: one fully visible and funded wave is bulk, reaches its
goal, and has zero geometric distance to its desired value. -/
theorem exact_wave_is_bulk_preferred_and_geometric :
    (exactWave.certified.plan .general).activation = .bulk ∧
      (true, 1, true) ∈ problem.preferredRegion ∧
      exactWave.geometry.distance
        (exactWave.readout.run .value
          (exactSemantics.observe (true, 1, true)))
        exactWave.desiredValue = 0 := by
  refine ⟨exactWave.completeBag_dispatches_bulk rfl,
    exactWave.targetPreferred, ?_⟩
  rfl

/-- The coarse observer has a real execution/resource certificate but cannot
acquire geometric authority because it forgets the independent value bit. -/
theorem coarse_certificates_do_not_recover_value :
    ¬ Nonempty
      (GeometricGoalDirectedWave contract coarseSemantics (false, 0, false)
        (true, 1, true) demand 1 [()] problem cost value) := by
  apply GeometricGoalDirectedWave.no_wave_of_invisible
  exact GeometricGoalCostControl.Canary.coarse_refuses_geometric_control

end Canary

/-! ## Axiom audit -/

#print axioms GeometricGoalDirectedWave.toGoalDirectedWave
#print axioms GeometricGoalDirectedWave.completeBag_dispatches_bulk
#print axioms GeometricGoalDirectedWave.observed_target_distance
#print axioms GeometricGoalDirectedWave.no_wave_of_invisible
#print axioms Canary.exact_wave_is_bulk_preferred_and_geometric
#print axioms Canary.coarse_certificates_do_not_recover_value

end Mettapedia.Cybernetics.GeometricGoalDirectedResourceWave
