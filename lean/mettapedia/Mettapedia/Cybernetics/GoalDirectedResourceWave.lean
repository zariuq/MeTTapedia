import Mettapedia.Cybernetics.MultiscaleGoalCostControl
import Mettapedia.GSLT.Core.ResourceAwareControl

/-!
# Goal-directed resource waves

A multiscale controller may recommend a resource-certified wave only when the
same observation used to justify schedule equivalence can also recover the
requested goal and cost coordinates.  This module packages that intersection.

The package does not create a transition, a resource decomposition, or an
observer.  It retains independently supplied evidence for all three and adds
only the fact that the common reference target lies in the preferred region.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.GoalDirectedResourceWave

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.Cybernetics.MultiscaleGoalCostControl
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl

universe uItem uGuard uCandidateView uState uStateView uAccount uCost

/-- One Levin-style wave at a declared observation scale.

* `certified` supplies exact occurrences, operational serializability, and
  resource separation;
* `readout` proves that both goal membership and cost factor through the very
  same state observer; and
* `targetPreferred` says the licensed reference target advances the authored
  setpoint.

The fields remain separate so that no one coordinate can masquerade as
another. -/
structure GoalDirectedWave
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account] {Cost : Type uCost}
    (contract : Contract Item Guard CandidateView)
    (semantics : ExecutionSemantics Item State StateView)
    (initial referenceTarget : State)
    (demand : Item → Account) (source : Account) (batch : List Item)
    (problem : ProblemSpace State) (cost : State → Cost) where
  certified : CertifiedBatch contract semantics initial referenceTarget
    Account demand source batch
  readout : (goalCostFamily problem cost).ReadoutRealization semantics.observe
  targetPreferred : referenceTarget ∈ problem.preferredRegion

namespace GoalDirectedWave

variable {Item : Type uItem} {Guard : Type uGuard}
variable {CandidateView : Type uCandidateView}
variable {State : Type uState} {StateView : Type uStateView}
variable {Account : Type uAccount} [AddMonoid Account]
variable {Cost : Type uCost}
variable {contract : Contract Item Guard CandidateView}
variable {semantics : ExecutionSemantics Item State StateView}
variable {initial referenceTarget : State}
variable {demand : Item → Account} {source : Account} {batch : List Item}
variable {problem : ProblemSpace State} {cost : State → Cost}

/-- A complete-bag goal-directed wave uses the generic certified bulk plan;
goal visibility adds no scheduling authority. -/
theorem completeBag_dispatches_bulk
    (wave : GoalDirectedWave contract semantics initial referenceTarget
      demand source batch problem cost)
    (complete : contract.demand.completion = .completeBag) :
    (wave.certified.plan .general).activation = .bulk :=
  wave.certified.completeBag_dispatches_bulk complete

/-- The coarse observer recognizes that the common target is preferred. -/
theorem observed_target_is_preferred
    (wave : GoalDirectedWave contract semantics initial referenceTarget
      demand source batch problem cost) :
    (wave.readout.run .preferred
      (semantics.observe referenceTarget)).down := by
  have agrees := congrArg ULift.down
    (wave.readout.agrees .preferred referenceTarget)
  rw [agrees]
  exact wave.targetPreferred

/-- The target cost recovered through the coarse observation is exact. -/
theorem observed_target_cost
    (wave : GoalDirectedWave contract semantics initial referenceTarget
      demand source batch problem cost) :
    wave.readout.run .cost (semantics.observe referenceTarget) =
      cost referenceTarget :=
  wave.readout.agrees .cost referenceTarget

/-- If goal and cost do not jointly factor through the execution observer,
no goal-directed wave at that observer can be constructed, even if separate
resource and serialization certificates happen to exist. -/
theorem no_wave_of_invisible
    (invisible : ¬ (goalCostFamily problem cost).SupportsReadout
      semantics.observe) :
    ¬ Nonempty (GoalDirectedWave contract semantics initial referenceTarget
      demand source batch problem cost) := by
  rintro ⟨wave⟩
  exact invisible ⟨wave.readout⟩

end GoalDirectedWave

/-! ## Executable positive and negative controls -/

namespace Canary

abbrev State := Bool × Nat

def problem : ProblemSpace State where
  preferredRegion := {state | state.1 = true}

def cost : State → Nat := Prod.snd

def run (_source : State) (items : List Unit) (target : State) : Prop :=
  items = [()] ∧ target = (true, 1)

def exactSemantics : ExecutionSemantics Unit State State where
  run := run
  observe := id

def coarseSemantics : ExecutionSemantics Unit State Bool where
  run := run
  observe := Prod.fst

def contract : Contract Unit Unit (Multiset Unit) where
  observer := { observe := fun items => (items : Multiset Unit) }
  demand := { completion := .completeBag }

def demand (_item : Unit) : Nat := 1

def certifiedExact :
    CertifiedBatch contract exactSemantics (false, 0) (true, 1)
      Nat demand 1 [()] where
  nonempty := by simp
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · exact ⟨rfl, rfl⟩
    · intro ordering permutation
      have orderingEqual : ordering = [()] := by
        simpa using permutation
      subst ordering
      exact ⟨(true, 1), ⟨rfl, rfl⟩, rfl⟩
  resources :=
    { frame := 0
      source_eq := by simp [batchDemand, demand] }

def exactReadout :
    (goalCostFamily problem cost).ReadoutRealization exactSemantics.observe where
  run
    | .preferred => fun state => ULift.up (state.1 = true)
    | .cost => Prod.snd
  agrees policy state := by
    cases policy <;> rfl

def exactWave :
    GoalDirectedWave contract exactSemantics (false, 0) (true, 1)
      demand 1 [()] problem cost where
  certified := certifiedExact
  readout := exactReadout
  targetPreferred := rfl

def exactObservedCost : Nat :=
  exactWave.readout.run .cost (exactSemantics.observe (true, 1))

/-- Positive control: a fully visible, funded singleton wave reaches the
preferred target and exposes its exact cost. -/
theorem exact_wave_is_bulk_preferred_and_costed :
    (exactWave.certified.plan .general).activation = .bulk ∧
      (exactWave.readout.run .preferred
        (exactSemantics.observe (true, 1))).down ∧
      exactObservedCost = 1 := by
  refine ⟨exactWave.completeBag_dispatches_bulk rfl,
    exactWave.observed_target_is_preferred, ?_⟩
  rfl

/-- The coarse Boolean observer sees the setpoint but hides the Nat cost. -/
theorem coarseObserver_refuses_joint_readout :
    ¬ (goalCostFamily problem cost).SupportsReadout
      coarseSemantics.observe := by
  intro supported
  have joint :=
    (supports_goalCostFamily_iff problem cost
      ({ observe := coarseSemantics.observe } : Observer State Bool)).mp
      supported
  rcases joint.2 with ⟨coarseCost, recovers⟩
  have zero := recovers (false, 0)
  have one := recovers (false, 1)
  simp [cost, coarseSemantics] at zero one
  omega

/-- Negative control: visibility of the goal alone cannot construct a
cost-sensitive wave at the coarse observer. -/
theorem no_coarse_goalDirectedWave :
    ¬ Nonempty
      (GoalDirectedWave contract coarseSemantics (false, 0) (true, 1)
        demand 1 [()] problem cost) :=
  GoalDirectedWave.no_wave_of_invisible coarseObserver_refuses_joint_readout

end Canary

#print axioms GoalDirectedWave.completeBag_dispatches_bulk
#print axioms GoalDirectedWave.observed_target_is_preferred
#print axioms GoalDirectedWave.observed_target_cost
#print axioms GoalDirectedWave.no_wave_of_invisible
#print axioms Canary.exact_wave_is_bulk_preferred_and_costed
#print axioms Canary.no_coarse_goalDirectedWave

end Mettapedia.Cybernetics.GoalDirectedResourceWave
