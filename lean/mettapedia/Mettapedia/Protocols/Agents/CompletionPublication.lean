import Mathlib.Tactic

/-!
# Publishing a committed completion once

A provider call's completion is published only after the ledger has committed
it: its effects are recorded (the completion observation, the calibration of
the captured model, a usage tally), then its answer is delivered. The call's
owner keeps one publication mark, which moves from unpublished to published
once. A completion delivered again — a reconcile retry after an uncertain
commit, or a replayed delivery — publishes nothing. Recording an effect may
fail; the answer does not depend on it.

Invariants proved here, for every event trace:
* effects are recorded at most once;
* no effect is recorded before the commit;
* the delivered answer is the same whether or not the effects were recorded.

The counterexample is the rule the publication mark guards against:
publishing on every committed delivery records the effects twice when an
uncertain commit is reconciled and delivered again, so a usage tally counts
one call twice.

This is an abstract contract, not a refinement proof of the MeTTa owner, of
the provider ledger or of the files the effects write.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.CompletionPublication

inductive Event where
  | commit | deliver

structure State where
  committed : Bool
  published : Bool
  effects : Nat
  deriving DecidableEq

def initial : State := ⟨false, false, 0⟩

/-- One transition: a delivery publishes only a committed, unpublished call. -/
def step (s : State) : Event → State
  | .commit => { s with committed := true }
  | .deliver =>
    if s.committed && !s.published then { s with published := true, effects := s.effects + 1 }
    else s

def run (s : State) (es : List Event) : State := es.foldl step s

/-- The reachable invariant: effects count publications, which follow a commit. -/
def Invariant (s : State) : Prop :=
  s.effects = (if s.published then 1 else 0) ∧ (s.published = true → s.committed = true)

theorem initial_invariant : Invariant initial := by
  simp [Invariant, initial]

theorem step_invariant {s : State} (h : Invariant s) (e : Event) : Invariant (step s e) := by
  obtain ⟨count, after⟩ := h
  cases e with
  | commit => exact ⟨count, fun _ => rfl⟩
  | deliver =>
    by_cases hc : s.committed <;> by_cases hp : s.published <;>
      simp_all [step, Invariant]

theorem run_invariant {s : State} (h : Invariant s) (es : List Event) : Invariant (run s es) := by
  induction es generalizing s with
  | nil => simpa [run] using h
  | cons e es ih => exact ih (step_invariant h e)

/-- Effects are recorded at most once along any trace. -/
theorem effects_at_most_once (es : List Event) : (run initial es).effects ≤ 1 := by
  obtain ⟨count, _⟩ := run_invariant initial_invariant es
  rw [count]
  split <;> simp

/-- No effect is recorded before the ledger commit. -/
theorem no_effects_before_commit (es : List Event) (h : (run initial es).committed = false) :
    (run initial es).effects = 0 := by
  obtain ⟨count, after⟩ := run_invariant initial_invariant es
  cases hp : (run initial es).published
  · simpa [hp] using count
  · exact absurd (after hp) (by simp [h])

/-- The delivered answer is a function of the result alone: whether each
effect was recorded does not enter it. -/
def answer {Result Answer : Type} (deliver : Result → Answer) (r : Result) (_recorded : Bool) : Answer :=
  deliver r

theorem answer_independent_of_effects {Result Answer : Type} (deliver : Result → Answer) (r : Result) :
    answer deliver r true = answer deliver r false := rfl

/-- The rejected rule: every committed delivery publishes. -/
def stepEveryDelivery (s : State) : Event → State
  | .commit => { s with committed := true }
  | .deliver => if s.committed then { s with published := true, effects := s.effects + 1 } else s

def runEveryDelivery (s : State) (es : List Event) : State := es.foldl stepEveryDelivery s

/-- Reconciled and delivered again, one call's effects are recorded twice. -/
theorem every_delivery_records_twice :
    (runEveryDelivery initial [.commit, .deliver, .deliver]).effects = 2 := by
  simp [runEveryDelivery, stepEveryDelivery, initial]

theorem owned_rule_records_once :
    (run initial [.commit, .deliver, .deliver]).effects = 1 := by
  simp [run, step, initial]

end Mettapedia.Protocols.Agents.CompletionPublication
