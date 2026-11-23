import Mathlib.Tactic

/-!
# The command responder's cycle: its wake-up and its outbox

Each cycle of the command responder reads the channel service's pending work,
answers it, submits one intent of the mode outbox and then waits. The wait
ends early when the service reports work published after a revision token.
The responder takes that token when it arms, before it reads anything; the
service's revisions only grow, one per publication, and a read sees every
task published up to the revision it read at.

Invariants proved here:
* no lost wake-up: a task the cycle's read did not see makes the next wait end
  at once, because its revision is above the token;
* the outbox makes progress: with an available service, every intent of a
  queue is gone (submitted, or set aside when it is not an intent) after as
  many cycles as the queue is long.

Counterexamples:
* taking the token after the read: a task published between the read and the
  token is neither seen nor reported, and waits out the bound;
* stopping at a file that is not an intent, as the replaced pump did: the
  intents behind it are never submitted.

This is an abstract contract, not a refinement proof of
`channels/telegram_control_io.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ResponderCycle

/-! ## The wake-up -/

/-- A wait with token `t` ends at once when the service's revision passed it. -/
def wakes (revision token : ℕ) : Bool := token < revision

/-- One cycle: the token is taken at `armedAt`, the read sees the revision at
`readAt`, the wait asks at `waitAt`; `rev` is the service's revision at each
moment, never decreasing. -/
structure Cycle where
  rev : ℕ → ℕ
  monotone : Monotone rev
  armedAt : ℕ
  readAt : ℕ
  waitAt : ℕ
  readAfterArm : armedAt ≤ readAt
  waitAfterRead : readAt ≤ waitAt

/-- A task with revision `v` published by the time of the wait but after the
read's revision ends the wait at once. -/
theorem no_lost_wakeup (c : Cycle) (v : ℕ) (unseen : c.rev c.readAt < v)
    (published : v ≤ c.rev c.waitAt) :
    wakes (c.rev c.waitAt) (c.rev c.armedAt) = true := by
  have h₁ : c.rev c.armedAt ≤ c.rev c.readAt := c.monotone c.readAfterArm
  simp [wakes]
  omega

/-- Taking the token after the read: revision 0 when read, a task published
(revision 1), the token taken then, nothing more published. The task was not
seen, and the wait does not end. -/
theorem token_after_read_loses_a_wakeup :
    ∃ readRev token waitRev v : ℕ, readRev < v ∧ v ≤ waitRev ∧ token = waitRev ∧
      wakes waitRev token = false := by
  exact ⟨0, 1, 1, 1, by decide, le_refl 1, rfl, by decide⟩

/-! ## The outbox -/

/-- An outbox file: an intent, or a file that is not one. -/
inductive Item
  | intent
  | unreadable
  deriving DecidableEq

/-- One cycle's pump with an available service: the first file goes, submitted
or set aside. -/
def pump : List Item → List Item
  | [] => []
  | _ :: rest => rest

/-- The replaced pump: a file that is not an intent stops it. -/
def pumpStopping : List Item → List Item
  | [] => []
  | Item.unreadable :: rest => Item.unreadable :: rest
  | Item.intent :: rest => rest

theorem outbox_drains (q : List Item) : pump^[q.length] q = [] := by
  induction q with
  | nil => rfl
  | cons head rest ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simpa [pump] using ih

theorem stopping_pump_never_drains (n : ℕ) :
    pumpStopping^[n] [Item.unreadable, Item.intent] = [Item.unreadable, Item.intent] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simpa [pumpStopping] using ih

end Mettapedia.Protocols.Agents.ResponderCycle
