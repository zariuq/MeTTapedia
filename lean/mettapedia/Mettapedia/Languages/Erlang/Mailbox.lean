import Mathlib.Data.List.Basic

/-! The mailbox component of the local Core Erlang machine. The scanned
prefix and incoming rear are stored in reverse order. Delivery is constant
work; peeking rotates the rear only when the unread front is empty. Payloads
are parametric: pattern matching and clause guards belong to the sequential
machine, which calls next only after rejecting the current message.

This module does not define the complete process scheduler or Core Erlang
evaluation. In particular, an empty unread suffix is a local wait condition,
not a proof that the whole configuration is blocked. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

structure Mailbox (α : Type*) where
  savedRev : List α := []
  front : List α := []
  rearRev : List α := []
  deriving Repr, DecidableEq, BEq

namespace Mailbox

variable {α β : Type*}

def unread (mailbox : Mailbox α) : List α := mailbox.front ++ mailbox.rearRev.reverse

def contents (mailbox : Mailbox α) : List α := mailbox.savedRev.reverse ++ mailbox.unread

def deliver (message : α) (mailbox : Mailbox α) : Mailbox α :=
  {mailbox with rearRev := message :: mailbox.rearRev}

def normalize (mailbox : Mailbox α) : Mailbox α :=
  match mailbox.front with
  | [] => {mailbox with front := mailbox.rearRev.reverse, rearRev := []}
  | _ :: _ => mailbox

def peek (mailbox : Mailbox α) : Option α := mailbox.unread.head?

def next? (mailbox : Mailbox α) : Option (Mailbox α) :=
  match mailbox.front with
  | [] => none
  | message :: rest => some {mailbox with savedRev := message :: mailbox.savedRev, front := rest}

def remove? (mailbox : Mailbox α) : Option (Mailbox α) :=
  match mailbox.front with
  | [] => none
  | _ :: rest => some ⟨[], mailbox.savedRev.reverse ++ rest, mailbox.rearRev⟩

theorem unread_normalize (mailbox : Mailbox α) : mailbox.normalize.unread = mailbox.unread := by
  cases mailbox with
  | mk saved front rear => cases front <;> simp [normalize, unread]

theorem contents_normalize (mailbox : Mailbox α) : mailbox.normalize.contents = mailbox.contents := by
  cases mailbox with
  | mk saved front rear => cases front <;> simp [normalize, contents, unread]

theorem contents_deliver (message : α) (mailbox : Mailbox α) :
    (mailbox.deliver message).contents = mailbox.contents ++ [message] := by
  simp [deliver, contents, unread, List.append_assoc]

theorem unread_deliver (message : α) (mailbox : Mailbox α) :
    (mailbox.deliver message).unread = mailbox.unread ++ [message] := by
  simp [deliver, unread, List.append_assoc]

theorem next_contents (message : α) (saved rest rear : List α) :
    (Mailbox.mk (message :: saved) rest rear).contents =
      (Mailbox.mk saved (message :: rest) rear).contents := by
  simp [contents, unread, List.append_assoc]

theorem remove_contents (message : α) (saved rest rear : List α) :
    remove? (Mailbox.mk saved (message :: rest) rear) =
      some ⟨[], saved.reverse ++ rest, rear⟩ := rfl

theorem deliver_order (first second : α) (mailbox : Mailbox α) :
    ((mailbox.deliver first).deliver second).contents = mailbox.contents ++ [first, second] := by
  simp [contents_deliver, List.append_assoc]

/-- Abstract receive selection, including guards in the supplied selector.
The residual queue retains every unmatched occurrence in its original order. -/
def selectFirst (select : α → Option β) : List α → Option (β × List α)
  | [] => none
  | message :: rest => match select message with
    | some result => some (result, rest)
    | none => (selectFirst select rest).map fun pair => (pair.1, message :: pair.2)

theorem selectFirst_some {select : α → Option β} {messages : List α} {result : β} {rest : List α}
    (selected : selectFirst select messages = some (result, rest)) :
    ∃ before message after, messages = before ++ message :: after ∧
      select message = some result ∧ (∀ prior ∈ before, select prior = none) ∧
      rest = before ++ after := by
  induction messages generalizing rest with
  | nil => simp [selectFirst] at selected
  | cons head tail ih =>
      cases found : select head with
      | some value =>
          simp [selectFirst, found] at selected
          obtain ⟨rfl, rfl⟩ := selected
          exact ⟨[], head, tail, rfl, found, by simp, rfl⟩
      | none =>
          simp only [selectFirst, found] at selected
          cases answer : selectFirst select tail with
          | none => simp [answer] at selected
          | some pair =>
              rcases pair with ⟨value, residual⟩
              simp only [answer, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
              obtain ⟨rfl, rfl⟩ := selected
              obtain ⟨before, message, after, source, succeeds, earlier, remaining⟩ := ih answer
              refine ⟨head :: before, message, after, ?_, succeeds, ?_, ?_⟩
              · simp [source]
              · intro prior member
                rcases List.mem_cons.mp member with rfl | member
                · exact found
                · exact earlier prior member
              · simp [remaining]

theorem selectFirst_none_iff (select : α → Option β) (messages : List α) :
    selectFirst select messages = none ↔ ∀ message ∈ messages, select message = none := by
  induction messages with
  | nil => simp [selectFirst]
  | cons head tail ih =>
      cases found : select head <;> simp [selectFirst, found, ih]

end Mailbox
end Mettapedia.Languages.Erlang
