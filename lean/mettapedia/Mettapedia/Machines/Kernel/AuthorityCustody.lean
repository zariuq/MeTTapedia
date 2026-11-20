import Mettapedia.Machines.Kernel.DelegationPolicy
import Mettapedia.Machines.Kernel.CorrelatedReplies

/-!
# Authority envelopes with retained custody

This module composes two existing kernel theories without enlarging either
trusted transition system:

* `Delegation` supplies actual capabilities, derivation ancestry, confinement
  to the genesis envelope, and cascading revocation.
* `CorrelatedReplies` supplies bounded, fresh, exactly-once work obligations.

The coupling is deliberately small. A configured caller may admit work, and a
peer may claim it, only while the caller currently holds grant authority to
that peer. Once claimed, the recorded peer may still complete the obligation:
revocation removes publication permission, not the duty to settle accepted
work. A ready value is exposed only while current authority exists; otherwise
polling discards it while releasing custody.

This is an abstract composition theorem. It does not claim refinement of the
SexOS C kernel, page tables, PKU, DMA, scheduling, or hardware observations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.AuthorityCustody

open Mettapedia.Machines.Kernel.Delegation

/-- A static authority envelope, the policy for delegation, and the bounded
call window whose admitted peers are justified by that envelope. -/
structure Profile (S O : Type) where
  genesis : Delegation.State S O
  rule : Delegation.Policy.Rule S O
  caller : S
  calls : CorrelatedReplies.Config S
  allowed_sound : ∀ peer, calls.allowed peer = true →
    CanHold genesis caller (.subj peer) true

/-- Actual authority and outstanding custody are separate state components. -/
structure State (S O : Type) where
  authority : Delegation.State S O
  custody : CorrelatedReplies.Window S

variable {S O : Type} [DecidableEq S] [DecidableEq O]

/-- Every actual capability remains inside the genesis closure. -/
def Confined (profile : Profile S O) (authority : Delegation.State S O) : Prop :=
  ∀ cap ∈ authority.caps,
    CanHold profile.genesis cap.holder cap.target cap.grant

/-- The product invariant: authority is confined and every outstanding call
is bounded, fresh, unique, and addressed to a statically permitted peer. -/
structure Valid (profile : Profile S O) (state : State S O) : Prop where
  authority : Confined profile state.authority
  custody : CorrelatedReplies.Valid profile.calls state.custody

/-- Current authority is a dynamic condition, separate from static policy. -/
def currentAllowed (profile : Profile S O) (state : State S O) (peer : S) : Bool :=
  mayGrant state.authority profile.caller peer

/-- Product actions. Custody actions are named separately so the authority
guard is part of the abstract semantics rather than a caller convention. -/
inductive Action (S O : Type) where
  | authority (operation : Delegation.Op S O)
  | admit (peer : S) (registered room : Bool)
  | claim (actor : S) (id : Nat)
  | complete (actor : S) (id value : Nat)
  | poll (id : Nat)
  | cancel (id : Nat)

/-- Cancellation is only valid before a peer has claimed the work. In-flight
and ready obligations cannot be erased by caller cancellation. -/
def cancelUnclaimed (window : CorrelatedReplies.Window S) (id : Nat) :
    CorrelatedReplies.Window S :=
  match CorrelatedReplies.lookup window id with
  | some call =>
      if call.phase = .queued then (CorrelatedReplies.cancel window id).1
      else window
  | none => window

/-- The value that may cross the publication boundary. A ready value with no
current authority is deliberately unobservable, although polling still
settles and releases its custody. -/
def publishable (profile : Profile S O) (state : State S O) (id : Nat) : Option Nat :=
  match CorrelatedReplies.lookup state.custody id with
  | some call =>
      match call.phase with
      | .ready value =>
          if currentAllowed profile state call.peer then some value else none
      | _ => none
  | none => none

/-- Advance custody. Admission and claiming require current authority. A
completion is instead authorized by the peer recorded when custody was
created, so revocation cannot strand an accepted operation. Polling always
settles a ready obligation; `publishable` separately controls observation. -/
def custodyStep (profile : Profile S O) (state : State S O) :
    Action S O → CorrelatedReplies.Window S
  | .authority _ => state.custody
  | .admit peer registered room =>
      (CorrelatedReplies.admit profile.calls state.custody peer
        (registered && currentAllowed profile state peer) room).1
  | .claim actor id =>
      if currentAllowed profile state actor then
        (CorrelatedReplies.claim state.custody actor id).1
      else state.custody
  | .complete actor id value =>
      (CorrelatedReplies.complete state.custody actor id value).1
  | .poll id => (CorrelatedReplies.poll state.custody id).1
  | .cancel id => cancelUnclaimed state.custody id

def step (profile : Profile S O) (state : State S O) : Action S O → State S O
  | .authority operation =>
      { state with authority := Delegation.Policy.step profile.rule state.authority operation }
  | action => { state with custody := custodyStep profile state action }

def run (profile : Profile S O) (state : State S O) : List (Action S O) → State S O
  | [] => state
  | action :: rest => run profile (step profile state action) rest

def initial (profile : Profile S O) : State S O :=
  ⟨profile.genesis, ⟨0, []⟩⟩

omit [DecidableEq S] [DecidableEq O] in
theorem genesis_confined (profile : Profile S O) : Confined profile profile.genesis := by
  intro cap member
  exact CanHold.base ⟨cap, member, rfl, rfl, fun held => held⟩

omit [DecidableEq S] [DecidableEq O] in
theorem initial_valid (profile : Profile S O) : Valid profile (initial profile) :=
  ⟨genesis_confined profile, CorrelatedReplies.empty_valid profile.calls⟩

/-- A restrictive policy step inherits confinement from the general
delegation core. -/
theorem confined_policy_step {profile : Profile S O}
    {authority : Delegation.State S O} (confined : Confined profile authority)
    (operation : Delegation.Op S O) :
    Confined profile (Delegation.Policy.step profile.rule authority operation) := by
  unfold Delegation.Policy.step
  split
  · exact Delegation.step_confined confined operation
  · exact confined

theorem custodyStep_valid {profile : Profile S O} {state : State S O}
    (valid : CorrelatedReplies.Valid profile.calls state.custody) (action : Action S O) :
    CorrelatedReplies.Valid profile.calls (custodyStep profile state action) := by
  cases action with
  | authority operation => exact valid
  | admit peer registered room =>
      exact valid.admit peer (registered && currentAllowed profile state peer) room
  | claim actor id =>
      simp only [custodyStep]
      split
      · exact valid.claim actor id
      · exact valid
  | complete actor id value =>
      exact valid.complete actor id value
  | poll id => exact valid.poll id
  | cancel id =>
      simp only [custodyStep, cancelUnclaimed]
      split
      · split
        · exact valid.cancel id
        · exact valid
      · exact valid

theorem Valid.step {profile : Profile S O} {state : State S O}
    (valid : Valid profile state) (action : Action S O) :
    Valid profile (step profile state action) := by
  cases action with
  | authority operation =>
      exact ⟨confined_policy_step valid.authority operation, valid.custody⟩
  | admit peer registered room =>
      exact ⟨valid.authority, custodyStep_valid valid.custody (.admit peer registered room)⟩
  | claim actor id =>
      exact ⟨valid.authority, custodyStep_valid valid.custody (.claim actor id)⟩
  | complete actor id value =>
      exact ⟨valid.authority, custodyStep_valid valid.custody (.complete actor id value)⟩
  | poll id => exact ⟨valid.authority, custodyStep_valid valid.custody (.poll id)⟩
  | cancel id => exact ⟨valid.authority, custodyStep_valid valid.custody (.cancel id)⟩

/-- The product invariant is inductive over arbitrary interleavings of
delegation, revocation, work progress, observation and settlement. -/
theorem Valid.run {profile : Profile S O} {state : State S O}
    (valid : Valid profile state) (actions : List (Action S O)) :
    Valid profile (run profile state actions) := by
  induction actions generalizing state with
  | nil => exact valid
  | cons action rest induction =>
      exact induction (valid.step action)

/- Every outstanding call names a peer permitted by the static authority
envelope, even when its current capability has later been revoked. -/
omit [DecidableEq S] [DecidableEq O] in
theorem Valid.outstanding_permitted {profile : Profile S O} {state : State S O}
    (valid : Valid profile state) {call : CorrelatedReplies.Call S}
    (member : call ∈ state.custody.calls) :
    CanHold profile.genesis profile.caller (.subj call.peer) true :=
  profile.allowed_sound call.peer (valid.custody.authority call member)

@[simp] theorem authority_step_preserves_custody (profile : Profile S O)
    (state : State S O) (operation : Delegation.Op S O) :
    (step profile state (.authority operation)).custody = state.custody := rfl

theorem blocked_claim_preserves_custody (profile : Profile S O)
    (state : State S O) (actor : S) (id : Nat)
    (blocked : currentAllowed profile state actor = false) :
    (step profile state (.claim actor id)).custody = state.custody := by
  simp [step, custodyStep, blocked]

@[simp] theorem completion_uses_recorded_custody (profile : Profile S O)
    (state : State S O) (actor : S) (id value : Nat) :
    (step profile state (.complete actor id value)).custody =
      (CorrelatedReplies.complete state.custody actor id value).1 := rfl

theorem cancel_heard_preserves_custody (profile : Profile S O)
    (state : State S O) (id : Nat) (peer : S)
    (heard : CorrelatedReplies.lookup state.custody id =
      some ⟨id, peer, .heard⟩) :
    (step profile state (.cancel id)).custody = state.custody := by
  simp [step, custodyStep, cancelUnclaimed, heard]

/-! ## Finite controls -/

def exampleGenesis : Delegation.State (Fin 3) (Fin 1) :=
  { caps := [
      ⟨0, 2, .subj 1, true, []⟩,
      ⟨1, 0, .subj 1, true, [0]⟩]
    next := 2 }

def exampleProfile : Profile (Fin 3) (Fin 1) where
  genesis := exampleGenesis
  rule := fun _ _ _ _ => true
  caller := 0
  calls := ⟨2, 8, fun peer => peer == 1⟩
  allowed_sound := by
    intro peer allowed
    have same : peer = 1 := by simpa using allowed
    subst peer
    apply CanHold.base
    exact ⟨⟨1, 0, .subj 1, true, [0]⟩, by simp [exampleGenesis], rfl, rfl,
      fun held => held⟩

def exampleHeard : State (Fin 3) (Fin 1) :=
  run exampleProfile (initial exampleProfile)
    [.admit 1 true true, .claim 1 1]

def exampleRevoked : State (Fin 3) (Fin 1) :=
  step exampleProfile exampleHeard (.authority (.revoke 2 0))

def exampleCompleted : State (Fin 3) (Fin 1) :=
  step exampleProfile exampleHeard (.complete 1 1 99)

def exampleCompletedAfterRevocation : State (Fin 3) (Fin 1) :=
  step exampleProfile exampleRevoked (.complete 1 1 99)

theorem example_heard :
    CorrelatedReplies.lookup exampleHeard.custody 1 = some ⟨1, 1, .heard⟩ := by decide

theorem example_completion_with_authority :
    CorrelatedReplies.lookup exampleCompleted.custody 1 = some ⟨1, 1, .ready 99⟩ := by decide

theorem example_publication_with_authority :
    publishable exampleProfile exampleCompleted 1 = some 99 := by decide

theorem example_revocation_removes_current_authority :
    currentAllowed exampleProfile exampleRevoked 1 = false := by decide

theorem example_revocation_retains_custody :
    exampleRevoked.custody = exampleHeard.custody := by decide

theorem example_completion_after_revocation_settles :
    CorrelatedReplies.lookup exampleCompletedAfterRevocation.custody 1 =
      some ⟨1, 1, .ready 99⟩ := by decide

theorem example_revoked_result_not_publishable :
    publishable exampleProfile exampleCompletedAfterRevocation 1 = none := by decide

theorem example_poll_after_revocation_releases_custody :
    CorrelatedReplies.lookup
      (step exampleProfile exampleCompletedAfterRevocation (.poll 1)).custody 1 = none := by decide

theorem example_cannot_cancel_claimed_work :
    (step exampleProfile exampleHeard (.cancel 1)).custody = exampleHeard.custody := by decide

theorem example_run_valid : Valid exampleProfile exampleRevoked := by
  apply Valid.step
  apply Valid.run (initial_valid exampleProfile)

#print axioms Valid.run
#print axioms Valid.outstanding_permitted
#print axioms completion_uses_recorded_custody
#print axioms cancel_heard_preserves_custody
#print axioms example_run_valid

end Mettapedia.Machines.Kernel.AuthorityCustody
