import Mettapedia.CognitiveArchitecture.Agent.WorldState

/-!
# Goal Commitment as a Witnessed Trace Discipline

Source provenance: adapted from GödelClaw commit
`86b20409f63c973c7a7204507b8b3b73181d6b1d`; only module packaging and
taxonomy-facing names were changed during integration.

This file gives a small executable companion to richer modal theories of
intention.  A commitment remains active until a typed witness records one of
three discharge conditions: achievement, impossibility, or loss of the
background justification under which the goal was adopted.

The evidence reference is opaque to this layer.  A replaceable epistemic
policy may obtain it from WM-PLN, a test receipt, a human instruction, or some
future method.  The commitment layer proves only that dropping an active goal
cannot occur without such a witness; it does not pretend to prove that the
epistemic policy is infallible.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.GoalCommitment

open Mettapedia.CognitiveArchitecture.Agent.WorldState

/-- Conditions under which a persistent goal may be discharged. -/
inductive DropReason where
  | achieved
  | impossible
  | justificationEnded
deriving Repr, DecidableEq

/-- A discharge decision carries a reference to its supporting evidence. -/
structure DropWitness (EvidenceRef : Type*) where
  reason : DropReason
  evidence : EvidenceRef
deriving Repr, DecidableEq

/-- Per-goal commitment state.  Discharge retains its reason and evidence
instead of silently deleting the goal. -/
inductive Status (EvidenceRef : Type*) where
  | inactive
  | active
  | discharged (witness : DropWitness EvidenceRef)
deriving Repr, DecidableEq

/-- Events understood by the commitment layer.  There is deliberately no
unwitnessed `drop` constructor. -/
inductive Event (EvidenceRef : Type*) where
  | adopt
  | discharge (witness : DropWitness EvidenceRef)
  | unrelated
deriving Repr, DecidableEq

/-- One goal-local commitment transition. -/
def step {EvidenceRef : Type*} :
    Status EvidenceRef → Event EvidenceRef → Status EvidenceRef
  | _, .adopt => .active
  | .active, .discharge witness => .discharged witness
  | .inactive, .discharge _ => .inactive
  | .discharged witness, .discharge _ => .discharged witness
  | status, .unrelated => status

/-- An active commitment changes only when an explicit discharge witness is
present. -/
theorem active_changes_only_with_witness
    {EvidenceRef : Type*} (event : Event EvidenceRef)
    (changes : step (.active : Status EvidenceRef) event ≠ .active) :
    ∃ witness, event = .discharge witness ∧
      step (.active : Status EvidenceRef) event = .discharged witness := by
  cases event with
  | adopt => simp [step] at changes
  | discharge witness => exact ⟨witness, rfl, rfl⟩
  | unrelated => simp [step] at changes

/-- Once discharged, further discharge reports cannot rewrite the recorded
reason.  Re-adoption is an explicit event rather than an accidental side
effect. -/
theorem discharge_is_stable
    {EvidenceRef : Type*} (first second : DropWitness EvidenceRef) :
    step (.discharged first) (.discharge second) = .discharged first := by
  rfl

/-- Execute a chronological commitment trace. -/
def run {EvidenceRef : Type*} :
    List (Event EvidenceRef) → Status EvidenceRef → Status EvidenceRef
  | [], status => status
  | event :: events, status => run events (step status event)

/-- A trace without adoption or discharge cannot alter commitment state. -/
theorem unrelated_trace_stutters
    {EvidenceRef : Type*} (events : List (Event EvidenceRef))
    (onlyUnrelated : ∀ event ∈ events, event = .unrelated)
    (status : Status EvidenceRef) :
    run events status = status := by
  induction events generalizing status with
  | nil => rfl
  | cons event events ih =>
      have eventUnrelated : event = .unrelated :=
        onlyUnrelated event (by simp)
      subst event
      simp only [run, step]
      apply ih
      intro later member
      exact onlyUnrelated later (by simp [member])

/-! ## Commitment-aware context -/

/-- The smallest query needed to recover one goal's current commitment
status. -/
inductive CommitmentQuery where
  | status
deriving Repr, DecidableEq

def answer {EvidenceRef : Type*}
    (status : Status EvidenceRef) (_ : CommitmentQuery) : Status EvidenceRef :=
  status

theorem answer_separates {EvidenceRef : Type*} :
    QuerySeparating (answer (EvidenceRef := EvidenceRef)) := by
  intro left right same
  exact same .status

/-- Any context view advertised as complete for commitment status must at
least distinguish every distinct status, including its discharge witness. -/
theorem commitment_complete_view_injective
    {EvidenceRef View : Type*} {view : Status EvidenceRef → View}
    (complete : QueryComplete (answer (EvidenceRef := EvidenceRef)) view) :
    Function.Injective view :=
  queryComplete_injective answer_separates complete

end Mettapedia.CognitiveArchitecture.Agent.GoalCommitment

#print axioms Mettapedia.CognitiveArchitecture.Agent.GoalCommitment.active_changes_only_with_witness
#print axioms Mettapedia.CognitiveArchitecture.Agent.GoalCommitment.unrelated_trace_stutters
#print axioms Mettapedia.CognitiveArchitecture.Agent.GoalCommitment.commitment_complete_view_injective
