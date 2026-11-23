import Mathlib.Tactic

/-!
# A provider call's display records

The local work display is best effort and has no authority: it only shows. A
console control holds whether the display is on and its epoch; a reset starts
a new epoch, and a record of another epoch is dropped. A provider call keeps a
small display state from its claim to its end: the epoch it began in, the
bytes of its streamed body observed, and whether observation stopped. Its
streamed text is shown only while the console shows its epoch and observation
has not stopped; a read that does not continue the last one stops observation
with one gap record; the call ends once, and then its state is gone.

Invariants proved here:
* nothing is written for a call while the console shows another epoch or is
  off;
* a call's end is written at most once: a second end writes nothing;
* observation that stopped stays stopped, and its gap is written once;
* the observed offset only grows by contiguous reads;
* every state a call kept is gone once it ended.

The counterexample is an end written without the epoch check: after a console
reset, an old call's end lands in the new epoch, which never showed the call.

This is an abstract contract, not a refinement proof of
`src/display_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.DisplayRecords

/-- What a call keeps from its claim to its end. -/
structure Call where
  epoch : ℕ
  offset : ℕ
  stopped : Bool

inductive Record
  | opened (attempt : ℕ)
  | text (attempt : ℕ)
  | gap (attempt : ℕ)
  | finished (attempt : ℕ)
  deriving DecidableEq

structure Display where
  enabled : Bool
  epoch : ℕ
  calls : ℕ → Option Call
  written : List Record

/-- A record of `epoch` is written only while the console shows that epoch. -/
def emit (d : Display) (epoch : ℕ) (r : Record) : Display :=
  if d.enabled = true ∧ d.epoch = epoch then { d with written := d.written ++ [r] } else d

def begin (d : Display) (a : ℕ) : Display :=
  emit { d with calls := Function.update d.calls a (some ⟨d.epoch, 0, false⟩) } d.epoch (.opened a)

def readable (d : Display) (a : ℕ) : Bool :=
  match d.calls a with
  | none => false
  | some c => !c.stopped && d.enabled && decide (d.epoch = c.epoch)

/-- Observation stops at its first gap, shown once. -/
def unavailable (d : Display) (a : ℕ) : Display :=
  match d.calls a with
  | none => d
  | some c =>
    if c.stopped then d
    else emit { d with calls := Function.update d.calls a (some { c with stopped := true }) } c.epoch (.gap a)

/-- The body was read on to `next` with `n` new bytes. -/
def advance (d : Display) (a next n : ℕ) : Display :=
  match d.calls a with
  | none => d
  | some c =>
    if next = c.offset + n then { d with calls := Function.update d.calls a (some { c with offset := next }) }
    else unavailable d a

/-- Readable text, shown under the call's epoch. -/
def shown (d : Display) (a : ℕ) : Display :=
  match d.calls a with
  | none => d
  | some c => if readable d a = true then emit d c.epoch (.text a) else d

/-- The call's end, once; its state is gone after. -/
def final (d : Display) (a : ℕ) : Display :=
  match d.calls a with
  | none => d
  | some c => emit { d with calls := Function.update d.calls a none } c.epoch (.finished a)

theorem emit_other_epoch (d : Display) (e : ℕ) (r : Record) (h : d.epoch ≠ e) : emit d e r = d := by
  simp [emit, h]

theorem emit_off (d : Display) (e : ℕ) (r : Record) (h : d.enabled = false) : emit d e r = d := by
  simp [emit, h]

theorem nothing_shown_from_another_epoch (d : Display) (a : ℕ) (c : Call)
    (hc : d.calls a = some c) (h : d.epoch ≠ c.epoch) :
    (shown d a).written = d.written ∧ (final d a).written = d.written := by
  constructor
  · simp [shown, hc, readable, h]
  · simp [final, hc, emit, h]

theorem final_once (d : Display) (a : ℕ) : final (final d a) a = final d a := by
  unfold final
  cases hc : d.calls a with
  | none => simp [hc]
  | some c => simp [emit]; split_ifs <;> simp

theorem final_forgets (d : Display) (a : ℕ) : (final d a).calls a = none := by
  unfold final
  cases hc : d.calls a with
  | none => simpa using hc
  | some c => simp [emit]; split_ifs <;> simp

theorem stopped_stays_stopped (d : Display) (a : ℕ) (c : Call) (hc : d.calls a = some c)
    (hs : c.stopped = true) : unavailable d a = d ∧ readable d a = false := by
  simp [unavailable, readable, hc, hs]

theorem gap_written_once (d : Display) (a : ℕ) :
    unavailable (unavailable d a) a = unavailable d a := by
  unfold unavailable
  cases hc : d.calls a with
  | none => simp [hc]
  | some c =>
    by_cases hs : c.stopped = true
    · simp [hc, hs]
    · simp [hs, emit]; split_ifs <;> simp

theorem advance_contiguous (d : Display) (a next n : ℕ) (c : Call) (hc : d.calls a = some c)
    (h : next = c.offset + n) : (advance d a next n).calls a = some { c with offset := c.offset + n } := by
  simp [advance, hc, h]

theorem advance_gap_stops (d : Display) (a next n : ℕ) (c : Call) (hc : d.calls a = some c)
    (h : next ≠ c.offset + n) : readable (advance d a next n) a = false := by
  simp only [advance, hc, h, if_false]
  unfold unavailable readable
  simp only [hc]
  split_ifs with hs
  · simp [hc, hs]
  · simp [emit]; split_ifs <;> simp

/-! ## Counterexample: an end written without the epoch check -/

def finalUnchecked (d : Display) (a : ℕ) : Display :=
  match d.calls a with
  | none => d
  | some _ => { d with calls := Function.update d.calls a none, written := d.written ++ [.finished a] }

/-- Call 7 began in epoch 1; the console was reset to epoch 2. -/
def reset : Display := { (begin ⟨true, 1, fun _ => none, []⟩ 7) with epoch := 2, written := [] }

theorem checked_end_stays_out_of_the_new_epoch : (final reset 7).written = [] := by
  decide +kernel

theorem unchecked_end_lands_in_the_new_epoch : (finalUnchecked reset 7).written = [.finished 7] := by
  decide +kernel

end Mettapedia.Protocols.Agents.DisplayRecords
