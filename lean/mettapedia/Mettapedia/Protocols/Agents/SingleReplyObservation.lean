import Mathlib.Data.List.Basic

/-!
# One outstanding call and its reply observation

A serial client keeps the first response for its current request. Notifications,
responses to other requests, and duplicates supply no new completion.
This is an abstract protocol model, not a refinement proof of transport code.
-/

namespace Mettapedia.Protocols.Agents.SingleReplyObservation

inductive Message (α : Type) where
  | notification
  | response (id : Nat) (body : α)

structure State (α : Type) where
  expected : Option Nat
  reply : Option α
  deriving Repr

def begin (id : Nat) : State α := ⟨some id, none⟩

def observe (s : State α) : Message α → State α
  | .notification => s
  | .response id body =>
      if s.expected = some id then
        match s.reply with
        | none => { s with reply := some body }
        | some _ => s
      else s

def observeMany (s : State α) : List (Message α) → State α
  | [] => s
  | message :: rest => observeMany (observe s message) rest

@[simp] theorem notification_preserves_state (s : State α) :
    observe s .notification = s := rfl

theorem wrong_request_preserves_state (s : State α) (id : Nat) (body : α)
    (wrong : s.expected ≠ some id) :
    observe s (.response id body) = s := by
  simp [observe, wrong]

theorem first_response_completes (id : Nat) (body : α) :
    (observe (begin id) (.response id body)).reply = some body := by
  simp [observe, begin]

theorem stored_reply_preserves_state (s : State α) (body : α)
    (stored : s.reply = some body) (message : Message α) :
    observe s message = s := by
  cases message with
  | notification => rfl
  | response id value =>
      by_cases h : s.expected = some id <;> simp [observe, h, stored]

theorem stored_reply_survives_all_messages (s : State α) (body : α)
    (stored : s.reply = some body) (messages : List (Message α)) :
    observeMany s messages = s := by
  induction messages with
  | nil => rfl
  | cons message rest ih =>
      simpa [observeMany, stored_reply_preserves_state s body stored message] using ih

theorem expected_request_is_preserved (s : State α) (message : Message α) :
    (observe s message).expected = s.expected := by
  cases message with
  | notification => rfl
  | response id body =>
      by_cases h : s.expected = some id
      · cases hr : s.reply <;> simp [observe, h, hr]
      · simp [observe, h]

def firstReply (id : Nat) : List (Message α) → Option α
  | [] => none
  | .notification :: rest => firstReply id rest
  | .response other body :: rest =>
      if other = id then some body else firstReply id rest

theorem trace_retains_first_matching_reply (id : Nat) (messages : List (Message α)) :
    (observeMany (begin id) messages).reply = firstReply id messages := by
  induction messages with
  | nil => rfl
  | cons message rest ih =>
      cases message with
      | notification => simpa [observeMany, observe, firstReply] using ih
      | response other body =>
          by_cases h : other = id
          · subst other
            have stable := stored_reply_survives_all_messages
              (observe (begin id) (.response id body)) body (first_response_completes id body) rest
            simp only [observeMany]
            rw [stable]
            simp [firstReply, first_response_completes]
          · simpa [observeMany, observe, begin, firstReply, h, Ne.symm h] using ih

def retainedReplies (s : State α) : Nat :=
  match s.reply with | none => 0 | some _ => 1

theorem retained_replies_are_bounded (s : State α) : retainedReplies s ≤ 1 := by
  cases h : s.reply <;> simp [retainedReplies, h]

def finish : State α := ⟨none, none⟩

theorem late_response_cannot_reopen_finished_call (id : Nat) (body : α) :
    observe finish (.response id body) = finish := by
  simp [observe, finish]

theorem wrong_id_is_not_completion :
    (observe (begin 7) (.response 8 "unrelated")).reply = none := by
  decide

theorem duplicate_does_not_replace_first :
    (observeMany (begin 7) [.response 7 "first", .response 7 "second"]).reply = some "first" := by
  decide

end Mettapedia.Protocols.Agents.SingleReplyObservation
