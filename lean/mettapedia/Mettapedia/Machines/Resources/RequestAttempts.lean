import Mettapedia.Machines.Resources.StateIndexed
import Mettapedia.Machines.Kernel.CorrelatedReplies

/-!
# Logical conversations over correlated transport attempts

The logical job survives cancellation and retry. A transport id is attached
only when it is newer than every previous attempt in this conversation. An
empty result word is `some 0`, distinct from no completion. The kernel window
continues to enforce peer authority; the conversation cannot manufacture that
authority or consume an unrelated pending call.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources.RequestAttempts

open Mettapedia.Machines.Kernel

structure Conversation where
  job : JobId
  awaiting : Option Nat
  last : Nat
  result : Option Nat
  deriving DecidableEq, Repr

def attach (s : Conversation) (id : Nat) : Option Conversation :=
  if s.awaiting = none ∧ s.result = none ∧ s.last < id then
    some { s with awaiting := some id, last := id }
  else none

def receive (s : Conversation) (id value : Nat) : Conversation :=
  if s.awaiting = some id then { s with awaiting := none, result := some value } else s

def retry (s : Conversation) (id : Nat) : Conversation :=
  if s.awaiting = some id then { s with awaiting := none } else s

def poll {Peer : Type} (window : CorrelatedReplies.Window Peer) (s : Conversation) (id : Nat) :
    CorrelatedReplies.Window Peer × Conversation :=
  if s.awaiting = some id then
    let completed := CorrelatedReplies.poll window id
    match completed.2 with
    | .value value => (completed.1, receive s id value)
    | _ => (completed.1, s)
  else (window, s)

theorem stale_reply_inert (s : Conversation) (id value : Nat)
    (different : s.awaiting ≠ some id) : receive s id value = s := by
  simp [receive, different]

theorem completion_consumed_once (s : Conversation) (id value other : Nat)
    (pending : s.awaiting = some id) :
    receive (receive s id value) id other = receive s id value := by
  simp [receive, pending]

theorem retry_preserves_job (s : Conversation) (id : Nat) : (retry s id).job = s.job := by
  unfold retry; split <;> rfl

theorem attach_preserves_job {s next : Conversation} (id : Nat)
    (accepted : attach s id = some next) : next.job = s.job ∧ next.last = id := by
  unfold attach at accepted
  split at accepted
  · cases Option.some.inj accepted; exact ⟨rfl, rfl⟩
  · cases accepted

theorem retry_does_not_restore_old_nonce (s : Conversation) (id : Nat) :
    (retry s id).last = s.last := by unfold retry; split <;> rfl

theorem old_attempt_cannot_be_reattached (s : Conversation) (id : Nat)
    (old : id ≤ s.last) : attach (retry s id) id = none := by
  simp [attach, retry_does_not_restore_old_nonce, Nat.not_lt_of_ge old]

theorem old_reply_after_retry_inert {s next : Conversation} (old newer value : Nat)
    (oldIssued : old ≤ s.last) (accepted : attach (retry s old) newer = some next) :
    receive next old value = next := by
  unfold attach at accepted
  split at accepted
  · rename_i admissible
    have newerThanOld : old < newer := lt_of_le_of_lt oldIssued
      (by simpa [retry_does_not_restore_old_nonce] using admissible.2.2)
    cases Option.some.inj accepted
    apply stale_reply_inert
    simp [Nat.ne_of_gt newerThanOld]
  · cases accepted

theorem mismatched_poll_leaves_window (Peer : Type) (window : CorrelatedReplies.Window Peer)
    (s : Conversation) (id : Nat) (different : s.awaiting ≠ some id) :
    poll window s id = (window, s) := by simp [poll, different]

theorem observed_value_comes_from_ready_slot {Peer : Type} (window : CorrelatedReplies.Window Peer)
    (s : Conversation) (id value : Nat) (pending : s.awaiting = some id)
    (observed : (CorrelatedReplies.poll window id).2 = .value value) :
    ∃ call : CorrelatedReplies.Call Peer, CorrelatedReplies.lookup window id = some call ∧ call.phase = .ready value ∧
      (poll window s id).2.result = some value := by
  obtain ⟨call, found, ready, _⟩ := CorrelatedReplies.poll_correct window id value observed
  refine ⟨call, found, ready, ?_⟩
  simp [poll, pending, observed, receive]

theorem cancellation_preserves_other_slot {Peer : Type} (window : CorrelatedReplies.Window Peer)
    (id other : Nat) (different : other ≠ id) :
    CorrelatedReplies.lookup (CorrelatedReplies.cancel window id).1 other = CorrelatedReplies.lookup window other := by
  unfold CorrelatedReplies.cancel
  split
  · exact CorrelatedReplies.lookup_remove_other window id other different
  · rfl

def sampleConversation : Conversation := ⟨⟨3, 17⟩, some 23, 23, none⟩
theorem completed_empty_is_a_result : (receive sampleConversation 23 0).result = some 0 := by decide
theorem foreign_completion_is_inert : receive sampleConversation 24 99 = sampleConversation := by decide
theorem retry_keeps_conversation_identity :
    (attach (retry sampleConversation 23) 24).map Conversation.job = some ⟨3, 17⟩ := by decide
theorem duplicate_id_refused : attach (retry sampleConversation 23) 23 = none := by decide

#print axioms old_reply_after_retry_inert
#print axioms observed_value_comes_from_ready_slot
#print axioms cancellation_preserves_other_slot

end Mettapedia.Machines.Resources.RequestAttempts
