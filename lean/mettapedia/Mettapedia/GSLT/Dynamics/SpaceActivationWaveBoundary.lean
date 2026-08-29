import Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
import Mettapedia.GSLT.Core.ResourceAwareControl

/-!
# Capability composition does not grant parallel-wave authority

Compatible activation fragments may be joined over one resident and observed
store.  That join says which transitions exist; it does not say that enabled
transitions commute.  This module supplies a concrete positive and negative
boundary against the generic observer/resource wave certificate.

An increment fragment and a doubling communication fragment coexist in one
policy.  Both actions have exact transitions and enough resource units, but
their two orders reach different observed states.  Consequently no certified
parallel batch exists.  A repeated increment batch is serializable and does
receive the complete certificate, preserving duplicate occurrence positions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.SpaceActivationWaveBoundary

open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy

namespace Canary

inductive Node where
  | increment
  | sender
  | receiver
deriving DecidableEq, Repr

inductive Receipt where
  | incremented
  | communicated
deriving DecidableEq, Repr

abbrev Store := Nat

def resident (_store : Store) (node : Node) : Prop :=
  node ∈ [Node.increment, Node.sender, Node.receiver]

/-- Explicit evaluation increments the visible store. -/
def evaluation : Policy Store Node Unit Store Receipt where
  resident := resident
  enabled _store cause := cause = .requested () .increment
  step store cause next receipt :=
    cause = .requested () .increment ∧
      next = store + 1 ∧ receipt = .incremented
  step_enabled step := step.1
  enabled_supported := by
    intro store cause _enabled
    cases cause with
    | requested trigger occurrence =>
        cases occurrence <;> simp [Cause.Supported, resident]
    | communication leftNode rightNode =>
        cases leftNode <;> cases rightNode <;>
          simp [Cause.Supported, resident]
  observe := id

/-- Rho-style communication doubles the same visible store. -/
def communication : Policy Store Node Unit Store Receipt where
  resident := resident
  enabled _store cause := cause = .communication .sender .receiver
  step store cause next receipt :=
    cause = .communication .sender .receiver ∧
      next = store * 2 ∧ receipt = .communicated
  step_enabled step := step.1
  enabled_supported := by
    intro store cause _enabled
    cases cause with
    | requested trigger occurrence =>
        cases occurrence <;> simp [Cause.Supported, resident]
    | communication leftNode rightNode =>
        cases leftNode <;> cases rightNode <;>
          simp [Cause.Supported, resident]
  observe := id

def compatible : evaluation.Compatible communication :=
  ⟨fun _store _node => Iff.rfl, fun _store => rfl⟩

def combined : Policy Store Node Unit Store Receipt :=
  Policy.join evaluation communication compatible

inductive Action where
  | increment
  | double
deriving DecidableEq, Repr

def cause : Action → Cause Unit Node
  | .increment => .requested () .increment
  | .double => .communication .sender .receiver

def receipt : Action → Receipt
  | .increment => .incremented
  | .double => .communicated

def applyAction : Action → Store → Store
  | .increment, store => store + 1
  | .double, store => store * 2

/-- Every action used by the batch semantics is a transition of the joined
policy. -/
theorem combined_realizes_action (action : Action) (store : Store) :
    combined.step store (cause action) (applyAction action store)
      (receipt action) := by
  cases action <;>
    simp [combined, Policy.join, evaluation, communication, cause, receipt,
      applyAction]

def execute (source : Store) (actions : List Action) : Store :=
  actions.foldl (fun store action => applyAction action store) source

def executionSemantics : ExecutionSemantics Action Store Store where
  run source actions target := target = execute source actions
  observe := id

def completeBagContract : Contract Action Unit (Multiset Action) where
  observer := { observe := fun actions => (actions : Multiset Action) }
  demand := { completion := .completeBag }

def unitDemand (_action : Action) : Nat := 1

def conflictingBatch : List Action := [.increment, .double]

theorem conflicting_reference_run :
    executionSemantics.run 1 conflictingBatch 4 :=
  rfl

/-- Both activation capabilities exist in the join at the relevant sources. -/
theorem conflicting_actions_are_individually_enabled :
    combined.CanFire 1 (cause .increment) ∧
      combined.CanFire 1 (cause .double) :=
  ⟨⟨2, .incremented, combined_realizes_action .increment 1⟩,
    ⟨2, .communicated, combined_realizes_action .double 1⟩⟩

/-- Resource separation is not the obstruction: two execution units exactly
fund the two occurrence positions. -/
def conflictingResources :
    BatchSeparation Nat unitDemand 2 conflictingBatch where
  frame := 0
  source_eq := rfl

/-- Increment-then-double reaches four, while double-then-increment reaches
three.  The joined policy therefore does not imply observer serializability. -/
theorem conflicting_not_serializable :
    ¬ executionSemantics.SerializesTo 1 conflictingBatch 4 := by
  intro serializable
  obtain ⟨target, targetRun, sameObservation⟩ :=
    serializable.2 [.double, .increment]
      (List.Perm.swap Action.increment Action.double [])
  have targetIsThree : target = 3 := by
    simpa [executionSemantics, execute, applyAction] using targetRun
  have targetIsFour : target = 4 := by
    simpa [executionSemantics] using sameObservation
  have impossible : (3 : Nat) = 4 := targetIsThree.symm.trans targetIsFour
  norm_num at impossible

/-- Even complete-bag demand, joined capabilities, and exact resources cannot
construct a wave certificate when the selected state observer distinguishes
the two schedules. -/
theorem policy_join_does_not_grant_wave :
    ¬ Nonempty
      (CertifiedBatch completeBagContract executionSemantics 1 4
        Nat unitDemand 2 conflictingBatch) := by
  rintro ⟨certified⟩
  exact conflicting_not_serializable certified.executionSerializable

def repeatedIncrementBatch : List Action := [.increment, .increment]

/-- Repeated occurrences remain two positions while all their permutations
reach the same observed state. -/
def repeatedIncrementCertified :
    CertifiedBatch completeBagContract executionSemantics 1 3
      Nat unitDemand 2 repeatedIncrementBatch where
  nonempty := by simp [repeatedIncrementBatch]
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · rfl
    · intro ordering permutation
      have orderingIsRepeated : ordering = repeatedIncrementBatch := by
        have everyIncrement : ∀ action ∈ ordering,
            action = Action.increment := by
          intro action member
          have targetMember : action ∈ repeatedIncrementBatch :=
            permutation.mem_iff.mp member
          simpa [repeatedIncrementBatch] using targetMember
        have lengthIsTwo : ordering.length = 2 := by
          simpa [repeatedIncrementBatch] using permutation.length_eq
        cases ordering with
        | nil => simp at lengthIsTwo
        | cons first rest =>
            have firstIsIncrement : first = Action.increment :=
              everyIncrement first (by simp)
            subst first
            cases rest with
            | nil => simp at lengthIsTwo
            | cons second tail =>
                have secondIsIncrement : second = Action.increment :=
                  everyIncrement second (by simp)
                subst second
                have tailIsNil : tail = [] := by
                  simpa using lengthIsTwo
                subst tail
                rfl
      subst ordering
      exact ⟨3, rfl, rfl⟩
  resources :=
    { frame := 0
      source_eq := rfl }

/-- Positive control: policy capability plus the missing semantic/resource
certificates does authorize one bulk wave. -/
theorem repeated_increment_is_bulk :
    (repeatedIncrementCertified.plan .general).activation = .bulk :=
  repeatedIncrementCertified.completeBag_dispatches_bulk rfl

end Canary

#print axioms Canary.combined_realizes_action
#print axioms Canary.conflicting_actions_are_individually_enabled
#print axioms Canary.conflicting_not_serializable
#print axioms Canary.policy_join_does_not_grant_wave
#print axioms Canary.repeated_increment_is_bulk

end Mettapedia.GSLT.Dynamics.SpaceActivationWaveBoundary
