import Mathlib.Tactic

/-!
# The turn-failure notice: one intent per episode, through crashes and restarts

When model turns fail, the command responder tells the operator once per
failure episode. Each cycle it builds a fresh candidate intent (a new key and
the notice text) and asks the ledger to reserve it under the episode; the
ledger keeps the first reservation and answers it to every later attempt. The
responder publishes the stored intent into the mode outbox, then marks it
queued. A cycle may stop after any of these effects (a crash), and a restart
forgets what the process remembered: which episodes it saw queued.

Invariants proved here, for every sequence of cycles, crashes and restarts:
* every intent ever published is the one the ledger reserved first: one key
  and one text per episode, however often a publication is repeated;
* once the ledger marked the notice queued, no cycle publishes again, with or
  without the process's memory;
* the process remembers an episode as queued only when the ledger says so.

Counterexample: publishing the cycle's own fresh candidate after a crash left
a reservation unqueued gives a second intent with another key: the operator
would be told twice.

This is an abstract contract, not a refinement proof of
`channels/telegram_failure_notice.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.FailureNoticeOnce

variable {I : Type}

/-- The ledger's record of one episode's notice: the reserved intent and
whether it was queued, or nothing yet. -/
abbrev Ledger (I : Type) := Option (I × Bool)

/-- Reserving keeps an existing reservation and otherwise stores this one. -/
def reserve (l : Ledger I) (i : I) : Ledger I :=
  match l with
  | none => some (i, false)
  | some r => some r

/-- What a cycle got done before it stopped. -/
inductive Stop
  | afterReserve
  | afterPublish
  | completed

/-- The world: the ledger, every intent ever written to the outbox (delivery
may consume a file, never this history), and the process's memory. -/
structure World (I : Type) where
  ledger : Ledger I
  published : List I
  remembered : Bool

/-- What a cycle does with the intent it publishes, stopping as `s` says. -/
def after (w : World I) (i : I) : Stop → World I
  | .afterReserve => { w with ledger := some (i, false) }
  | .afterPublish => { w with ledger := some (i, false), published := w.published ++ [i] }
  | .completed => { ledger := some (i, true), published := w.published ++ [i], remembered := true }

/-- One cycle with a fresh candidate, stopping as `s` says: a remembered or
queued notice is left alone; otherwise the reserved intent (the stored one,
else the candidate, as `reserve` gives it) is published. -/
def cycle (w : World I) (fresh : I) (s : Stop) : World I :=
  if w.remembered then w else
  match w.ledger with
  | none => after w fresh s
  | some (_, true) => { w with remembered := true }
  | some (i, false) => after w i s

/-- A restart forgets what the process remembered. -/
def restart (w : World I) : World I := { w with remembered := false }

/-- A step of the system. -/
inductive Step (I : Type)
  | cycle (fresh : I) (s : Stop)
  | restart

def step (w : World I) : Step I → World I
  | .cycle fresh s => cycle w fresh s
  | .restart => restart w

def run (w : World I) (steps : List (Step I)) : World I := steps.foldl step w

/-- The invariant: every published intent is the reserved one, and the
process remembers only a queued notice. -/
def Inv (w : World I) : Prop :=
  (∀ x ∈ w.published, ∃ q, w.ledger = some (x, q)) ∧
  (w.remembered = true → ∃ i, w.ledger = some (i, true))

def initial : World I := { ledger := none, published := [], remembered := false }

theorem inv_initial : Inv (initial : World I) := by
  simp [Inv, initial]

theorem inv_after (w : World I) (i : I) (s : Stop) (hall : ∀ x ∈ w.published, x = i)
    (hm : w.remembered = false) : Inv (after w i s) := by
  cases s with
  | afterReserve =>
    refine ⟨fun x hx => ⟨false, ?_⟩, by simp [after, hm]⟩
    simp only [after] at hx ⊢
    rw [hall x hx]
  | afterPublish =>
    refine ⟨fun x hx => ⟨false, ?_⟩, by simp [after, hm]⟩
    simp only [after, List.mem_append, List.mem_singleton] at hx ⊢
    rcases hx with hx | hx
    · rw [hall x hx]
    · rw [hx]
  | completed =>
    refine ⟨fun x hx => ⟨true, ?_⟩, fun _ => ⟨i, rfl⟩⟩
    simp only [after, List.mem_append, List.mem_singleton] at hx ⊢
    rcases hx with hx | hx
    · rw [hall x hx]
    · rw [hx]

theorem inv_cycle (w : World I) (fresh : I) (s : Stop) (h : Inv w) : Inv (cycle w fresh s) := by
  obtain ⟨hp, hr⟩ := h
  by_cases hm : w.remembered = true
  · simp only [cycle, hm, ↓reduceIte]; exact ⟨hp, hr⟩
  · have hm' : w.remembered = false := by simpa using hm
    cases hl : w.ledger with
    | none =>
      have hnil : ∀ x ∈ w.published, x = fresh := by
        intro x hx; obtain ⟨q, hq⟩ := hp x hx; rw [hl] at hq; cases hq
      simp only [cycle, hm', hl, Bool.false_eq_true, ↓reduceIte]
      exact inv_after w fresh s hnil hm'
    | some r =>
      obtain ⟨i, q⟩ := r
      have hall : ∀ x ∈ w.published, x = i := by
        intro x hx; obtain ⟨q', hq'⟩ := hp x hx; rw [hl] at hq'; simp at hq'; exact hq'.1.symm
      cases q with
      | true =>
        simp only [cycle, hm', hl, Bool.false_eq_true, ↓reduceIte]
        exact ⟨fun x hx => ⟨true, by simp [hall x hx]⟩, fun _ => ⟨i, by simp⟩⟩
      | false =>
        simp only [cycle, hm', hl, Bool.false_eq_true, ↓reduceIte]
        exact inv_after w i s hall hm'

theorem inv_restart (w : World I) (h : Inv w) : Inv (restart w) := by
  obtain ⟨hp, _⟩ := h
  exact ⟨hp, by simp [restart]⟩

theorem inv_step (w : World I) (st : Step I) (h : Inv w) : Inv (step w st) := by
  cases st with
  | cycle fresh s => exact inv_cycle w fresh s h
  | restart => exact inv_restart w h

theorem inv_run (w : World I) (steps : List (Step I)) (h : Inv w) : Inv (run w steps) := by
  induction steps generalizing w with
  | nil => simpa [run]
  | cons st rest ih => exact ih (step w st) (inv_step w st h)

/-- **One intent.** From the start, whatever runs: every published intent is
the reserved one, so all publications carry one key and one text. -/
theorem one_intent (steps : List (Step I)) (x y : I)
    (hx : x ∈ (run initial steps).published) (hy : y ∈ (run initial steps).published) : x = y := by
  obtain ⟨hp, _⟩ := inv_run initial steps inv_initial
  obtain ⟨qx, hqx⟩ := hp x hx
  obtain ⟨qy, hqy⟩ := hp y hy
  rw [hqx] at hqy
  simp at hqy
  exact hqy.1

/-- **Never again once queued**, remembered or not. -/
theorem queued_publishes_nothing (w : World I) (i : I) (fresh : I) (s : Stop)
    (hq : w.ledger = some (i, true)) : (cycle w fresh s).published = w.published := by
  by_cases hm : w.remembered = true
  · simp [cycle, hm]
  · simp [cycle, hm, hq]

/-- **Memory is sound**: remembered only when queued. -/
theorem remembered_only_queued (steps : List (Step I)) (h : (run initial steps).remembered = true) :
    ∃ i, (run initial steps).ledger = some (i, true) :=
  (inv_run initial steps inv_initial).2 h

/-- Publishing the cycle's own candidate instead of the stored one, after a
crash left the reservation unqueued, publishes two intents. -/
def cycleFresh (w : World I) (fresh : I) : World I :=
  match reserve w.ledger fresh with
  | some (_, false) => { w with published := w.published ++ [fresh] }
  | _ => w

theorem fresh_candidate_publishes_twice :
    (cycleFresh (cycleFresh (cycle (initial : World ℕ) 1 .afterReserve) 2) 3).published = [2, 3] := by
  simp [cycleFresh, cycle, after, initial, reserve]

end Mettapedia.Protocols.Agents.FailureNoticeOnce
