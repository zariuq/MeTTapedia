import Mathlib.Tactic

/-!
# A model turn's owned outcome, and the pacing of a failed turn

The loop asks whether its model turn succeeded before it commits history or
acknowledges input. The answer is a phase the native owner keeps: a turn's
call begins pending, and the owner of the provider call ends it completed
(a program was released) or failed (failure facts came back). A call the
rejection gate refuses gets no owner decision at all.

A failed turn waits before the next one. The wait is a pure function of the
failure's facts and of the streak of transient failures before it.

Invariants proved here:
* a turn succeeds only through a completion inside that turn: no outcome an
  earlier turn left can answer for it, and a refused call never succeeds;
* a retained rejection block waits 0, since corrective input ends it;
* a deterministic rejection waits at least the cap;
* a transient failure's backoff never passes the cap;
* any other failure ends the streak and waits the base, so with a positive
  base no failure, including a refused oversized answer, retries at once.

Counterexamples:
* an outcome kept for the process, not begun again by each turn, answers
  success for a refused turn after a completed one;
* pacing that lets a non-transient failure retry at once makes any number of
  failures take no time at all: an unbounded model and ledger loop.

This is an abstract contract, not a refinement proof of
`src/turn_health_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.TurnHealth

inductive Phase
  | none
  | pending
  | completed
  | failed
  deriving DecidableEq

/-- What a turn's call can bring. `refuse` is the gate refusing the call: the
owner decides nothing. -/
inductive Event
  | begin
  | complete
  | fail
  | refuse
  deriving DecidableEq

def step : Phase → Event → Phase
  | _, .begin => .pending
  | _, .complete => .completed
  | _, .fail => .failed
  | p, .refuse => p

def run (p : Phase) (events : List Event) : Phase := events.foldl step p

def succeeded (p : Phase) : Bool := decide (p = .completed)

/-- The events of one call; the next turn's `begin` ends it. -/
def WithinTurn (events : List Event) : Prop := Event.begin ∉ events

theorem run_without_complete (p : Phase) (events : List Event)
    (hp : p ≠ .completed) (hc : Event.complete ∉ events) : run p events ≠ .completed := by
  induction events generalizing p with
  | nil => simpa [run] using hp
  | cons e rest ih =>
    simp only [List.mem_cons, not_or] at hc
    simp only [run, List.foldl_cons]
    exact ih (step p e) (by cases e <;> simp_all [step]) hc.2

/-- A turn succeeds only through a completion inside it, whatever phase the
process held before. -/
theorem success_needs_own_completion (p : Phase) (events : List Event)
    (h : succeeded (run p (.begin :: events)) = true) : Event.complete ∈ events := by
  by_contra hc
  apply run_without_complete .pending events (by decide) hc
  simpa [run, step] using of_decide_eq_true h

theorem refused_turn_fails (p : Phase) (events : List Event)
    (h : ∀ e ∈ events, e = .refuse) : succeeded (run p (.begin :: events)) = false := by
  have hc : Event.complete ∉ events := fun hm => by cases h _ hm
  have := run_without_complete .pending events (by decide) hc
  exact decide_eq_false (by simpa [run, step] using this)

/-- Counterexample: an outcome the process keeps, which no turn begins again. -/
def stepKept : Phase → Event → Phase
  | p, .begin => p
  | p, e => step p e

example : succeeded ([Event.begin, .complete, .begin, .refuse].foldl stepKept .none) = true := by
  decide

/-! ## Pacing -/

/-- What the host classifies about a failure. -/
structure Facts where
  transient : Bool
  /-- The provider's retry-after, if it gave one. -/
  retry : Option ℚ
  /-- A client error the provider would give again for the same request. -/
  rejected : Bool
  /-- A retained rejection blocks retries until corrective input. -/
  blocked : Bool

def backoff (base cap : ℚ) (streak : ℕ) : ℚ := min cap (base * 2 ^ min (streak - 1) 20)

/-- The wait and the next streak. -/
def pace (base cap : ℚ) (streak : ℕ) (f : Facts) : ℚ × ℕ :=
  let next := if f.transient then streak + 1 else 0
  let paced := if f.transient ∧ 0 < base then backoff base cap next else base
  let stated := f.retry.getD paced
  let floored := if f.rejected then max stated cap else stated
  (if f.blocked then 0 else floored, next)

theorem blocked_waits_zero (base cap : ℚ) (streak : ℕ) (f : Facts) (h : f.blocked = true) :
    (pace base cap streak f).1 = 0 := by
  simp [pace, h]

theorem rejection_waits_cap (base cap : ℚ) (streak : ℕ) (f : Facts)
    (hb : f.blocked = false) (hr : f.rejected = true) : cap ≤ (pace base cap streak f).1 := by
  simp [pace, hb, hr]

theorem backoff_within_cap (base cap : ℚ) (streak : ℕ) (f : Facts)
    (ht : f.transient = true) (hpos : 0 < base) (hn : f.retry = none)
    (hr : f.rejected = false) (hb : f.blocked = false) : (pace base cap streak f).1 ≤ cap := by
  simp [pace, ht, hpos, hn, hr, hb, backoff]

theorem other_failure_waits_base (base cap : ℚ) (streak : ℕ) (f : Facts)
    (ht : f.transient = false) (hn : f.retry = none) (hr : f.rejected = false)
    (hb : f.blocked = false) : pace base cap streak f = (base, 0) := by
  simp [pace, ht, hn, hr, hb]

/-- With a positive base, failures that are neither transient nor stated take
time: n of them wait n times the base. -/
theorem failures_take_time (base cap : ℚ) (f : Facts) (n : ℕ)
    (ht : f.transient = false) (hn : f.retry = none) (hr : f.rejected = false)
    (hb : f.blocked = false) :
    (List.replicate n f).foldl (fun total g => total + (pace base cap 0 g).1) 0 = n * base := by
  have hw : (pace base cap 0 f).1 = base := by rw [other_failure_waits_base base cap 0 f ht hn hr hb]
  suffices ∀ start : ℚ, (List.replicate n f).foldl (fun total g => total + (pace base cap 0 g).1) start
      = start + n * base by simpa using this 0
  intro start
  induction n generalizing start with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, ih, hw]; push_cast; ring

theorem failures_take_positive_time (base cap : ℚ) (f : Facts) (n : ℕ) (hpos : 0 < base)
    (hn0 : 0 < n) (ht : f.transient = false) (hn : f.retry = none) (hr : f.rejected = false)
    (hb : f.blocked = false) :
    0 < (List.replicate n f).foldl (fun total g => total + (pace base cap 0 g).1) 0 := by
  rw [failures_take_time base cap f n ht hn hr hb]
  exact mul_pos (by exact_mod_cast hn0) hpos

/-- Counterexample: pacing that retries a non-transient failure at once. -/
def paceAtOnce (base cap : ℚ) (streak : ℕ) (f : Facts) : ℚ × ℕ :=
  if f.transient then pace base cap streak f else (0, 0)

example : ([1, 2, 3].map fun _ => (paceAtOnce 15 300 0
    ⟨false, none, false, false⟩).1).sum = 0 := by
  simp [paceAtOnce]

end Mettapedia.Protocols.Agents.TurnHealth
