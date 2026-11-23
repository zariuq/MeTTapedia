import Mathlib.Tactic

/-!
# Progress receipts and the service watchdog

A process writes a progress receipt only at real progress: a phase it reached,
a provider call it submitted, more of the provider's answer. A receipt carries
the end of the wait the process owns (0 for none); each one renews the service
watchdog, whose renewal is the service's interval extended by the wait still
owned, in whole microseconds rounded up.

* A phase owns no wait.
* A submitted call owns its wait to its deadline, and counts its answer's
  bytes from none.
* More of the answer writes a receipt that keeps the call's deadline; a poll
  that brought no new bytes writes none.

Invariants proved here:
* a poll with no new bytes writes no receipt and changes nothing, so idle
  polling can neither look like progress nor move the deadline;
* data keeps the call's deadline;
* the watchdog's renewal at a later time is never longer than at an earlier
  one for the same wait, so no renewal outlives the owned wait;
* without an owned wait the renewal is the service's interval;
* receipts are numbered without repeat, in order;
* after a new submission its first data writes a receipt.

The counterexample writes a receipt at every poll: a call whose provider sends
nothing renews the watchdog forever.

This is an abstract contract, not a refinement proof of
`src/progress_receipt_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ProgressReceipts

/-- A process's receipts so far, the end of the wait it owns (0 for none) and
the answer bytes reported so far. -/
structure State where
  receipts : ℕ
  deadline : ℕ
  bytes : ℕ
  deriving DecidableEq

def phase (s : State) : State := { s with receipts := s.receipts + 1, deadline := 0 }

def providerWait (s : State) (now wait : ℕ) : State :=
  { receipts := s.receipts + 1, deadline := now + wait, bytes := 0 }

def providerData (s : State) (count : ℕ) : State :=
  if count ≤ s.bytes then s else { s with receipts := s.receipts + 1, bytes := count }

/-- The watchdog's renewal in microseconds, times in nanoseconds. -/
def renewal (base deadline now : ℕ) : ℕ :=
  if now < deadline then base + (deadline - now + 999) / 1000 else base

theorem idle_poll_writes_nothing (s : State) (count : ℕ) (h : count ≤ s.bytes) :
    providerData s count = s := by
  simp [providerData, h]

theorem data_keeps_deadline (s : State) (count : ℕ) : (providerData s count).deadline = s.deadline := by
  unfold providerData; split_ifs <;> rfl

theorem renewal_never_grows (base deadline now later : ℕ) (h : now ≤ later) :
    renewal base deadline later ≤ renewal base deadline now := by
  unfold renewal
  split_ifs with h1 h2 h2
  · have : deadline - later + 999 ≤ deadline - now + 999 := by omega
    exact Nat.add_le_add_left (Nat.div_le_div_right this) base
  · omega
  · exact Nat.le_add_right base _
  · exact le_refl base

theorem renewal_without_wait (base now : ℕ) : renewal base 0 now = base := by
  simp [renewal]

theorem renewal_after_deadline (base deadline now : ℕ) (h : deadline ≤ now) :
    renewal base deadline now = base := by
  simp [renewal, not_lt.mpr h]

theorem phase_numbers_next (s : State) : (phase s).receipts = s.receipts + 1 := rfl
theorem wait_numbers_next (s : State) (now wait : ℕ) : (providerWait s now wait).receipts = s.receipts + 1 := rfl

theorem receipts_never_decrease (s : State) (count : ℕ) : s.receipts ≤ (providerData s count).receipts := by
  unfold providerData; split_ifs <;> simp

theorem first_data_after_submission_is_receipt (s : State) (now wait count : ℕ) (h : 0 < count) :
    (providerData (providerWait s now wait) count).receipts = s.receipts + 2 := by
  simp [providerData, providerWait, Nat.not_le.mpr h]

/-- Counterexample: a receipt at every poll renews the watchdog with no new data. -/
def eagerData (s : State) (_count : ℕ) : State := { s with receipts := s.receipts + 1 }

theorem eager_polling_renews_forever (s : State) (n : ℕ) :
    (Nat.iterate (fun t => eagerData t 0) n s).receipts = s.receipts + n := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [eagerData]
    omega

/-- The contract's polls write none: the receipt count stays. -/
theorem contract_polling_writes_none (s : State) (n : ℕ) :
    (Nat.iterate (fun t => providerData t 0) n s).receipts = s.receipts := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [providerData]

end Mettapedia.Protocols.Agents.ProgressReceipts
