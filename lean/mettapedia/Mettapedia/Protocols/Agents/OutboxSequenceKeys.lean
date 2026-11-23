import Mathlib.Tactic

/-!
# Mode-outbox keys: strictly increasing, whatever the clock does

Every send queued in a mode outbox is named by a key ending in a sequence
number. Each writer (the native responder, and Python writers that remain)
takes the outbox's lock, reads the stored sequence, uses the larger of the
stored value plus one and the wall clock's nanoseconds, and stores it before
releasing the lock. The channel service treats a key as an identity: a
repeated key with other bytes would be a conflict, and an older key could
read as a resend.

Invariants proved here, for any clock readings, including a clock that stands
still or steps back:
* the keys handed out are strictly increasing, and above the stored value
  they started from;
* each key is at least the clock reading it was made at.

Counterexample: the clock alone, without the stored value, repeats a key when
two requests read the same nanosecond, or when the clock steps back.

This is an abstract contract, not a refinement proof of
`channels/telegram_control_io.metta` or `durable_telegram.Channel.key`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.OutboxSequenceKeys

/-- The next sequence from the stored one and the clock. -/
def next (stored now : ℕ) : ℕ := max (stored + 1) now

/-- Requests in lock order, each with its clock reading: the keys handed out. -/
def issue : ℕ → List ℕ → List ℕ
  | _, [] => []
  | stored, now :: later => next stored now :: issue (next stored now) later

theorem next_above (stored now : ℕ) : stored < next stored now := by
  unfold next; omega

theorem next_clock (stored now : ℕ) : now ≤ next stored now := by
  unfold next; omega

/-- Every key is above the stored value the run started from. -/
theorem issued_above (stored : ℕ) (clock : List ℕ) : ∀ k ∈ issue stored clock, stored < k := by
  induction clock generalizing stored with
  | nil => simp [issue]
  | cons now later ih =>
    intro k hk
    simp only [issue, List.mem_cons] at hk
    rcases hk with hk | hk
    · rw [hk]; exact next_above stored now
    · exact lt_trans (next_above stored now) (ih (next stored now) k hk)

/-- **Strictly increasing**: each key is above every key before it. -/
theorem issued_increasing (stored : ℕ) (clock : List ℕ) : (issue stored clock).Pairwise (· < ·) := by
  induction clock generalizing stored with
  | nil => simp [issue]
  | cons now later ih =>
    simp only [issue, List.pairwise_cons]
    exact ⟨issued_above (next stored now) later, ih (next stored now)⟩

/-- Each key is at least its clock reading. -/
theorem issued_clock (stored : ℕ) (clock : List ℕ) :
    List.Forall₂ (fun now k => now ≤ k) clock (issue stored clock) := by
  induction clock generalizing stored with
  | nil => simp [issue]
  | cons now later ih => exact List.Forall₂.cons (next_clock stored now) (ih (next stored now))

/-- The clock alone repeats a key: the same nanosecond twice. -/
theorem clock_alone_repeats : ∃ now : ℕ, ¬ ([now, now] : List ℕ).Pairwise (· < ·) :=
  ⟨5, by simp⟩

end Mettapedia.Protocols.Agents.OutboxSequenceKeys
