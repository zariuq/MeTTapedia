import Mathlib.Tactic

/-!
# A command turn's commentary observer

The model's authored commentary is shared as a note of the worklog: a sink with
a sharing switch and an epoch, which keeps a note only while sharing is on and
only in the epoch the note is offered for. A call with commentary on reads the
worklog's state once, at its claim. A call that began while sharing was off
offers nothing; any other call offers at most one note, in the epoch it began
in. Blank commentary is no offer.

The note comes from the stream when the answer's text, up to its first comma
outside a JSON string, is the commentary field; else from the accepted output.
The stream arrives in pieces, so the observer scans each piece from the state
the previous pieces left: whether a string is open, and whether its next
character is escaped.

Invariants proved here:
* a call offers at most one note: once it offered, nothing it does adds a note;
* a call that began with sharing off adds no note, whatever the worklog does
  later;
* after the worklog's epoch moved on, an old call adds no note;
* blank commentary leaves the call able to offer;
* the first comma outside a string is found at the same place whether the
  text arrives whole or in any two pieces, the second scanned from the state
  the first left.

The counterexample publishes the accepted output's commentary without the
offered flag: after the streamed note, the call adds a second.

This is an abstract contract, not a refinement proof of
`src/commentary_observer_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.CommentaryObserver

/-! ## The worklog and a call's publication -/

structure Worklog where
  enabled : Bool
  epoch : ℕ
  notes : List String

/-- The worklog keeps a note only while sharing is on, in its own epoch. -/
def add (w : Worklog) (e : ℕ) (t : String) : Worklog :=
  if w.enabled = true ∧ w.epoch = e then { w with notes := w.notes ++ [t] } else w

/-- Switching sharing off or on starts a new epoch. -/
def toggle (w : Worklog) (on : Bool) : Worklog := { w with enabled := on, epoch := w.epoch + 1 }

/-- What a call keeps from its claim: the epoch it began in and whether it offered. -/
structure Call where
  epoch : ℕ
  offered : Bool

/-- A call with commentary on reads the worklog once, at its claim. -/
def claim (w : Worklog) : Option Call := if w.enabled = true then some ⟨w.epoch, false⟩ else none

/-- Offer `t` (`blank` says whether it is only whitespace): at most once a call. -/
def publish (w : Worklog) (c : Option Call) (t : String) (blank : Bool) : Worklog × Option Call :=
  match c with
  | none => (w, none)
  | some k =>
    if k.offered = true then (w, some k)
    else if blank = true then (w, some k)
    else (add w k.epoch t, some { k with offered := true })

theorem add_notes (w : Worklog) (e : ℕ) (t : String) :
    (add w e t).notes = w.notes ∨ (add w e t).notes = w.notes ++ [t] := by
  unfold add; split_ifs <;> simp

theorem toggle_notes (w : Worklog) (on : Bool) : (toggle w on).notes = w.notes := rfl

theorem offered_adds_nothing (w : Worklog) (k : Call) (hk : k.offered = true) (t : String) (b : Bool) :
    publish w (some k) t b = (w, some k) := by
  simp [publish, hk]

theorem offer_marks_offered (w : Worklog) (k : Call) (t : String) (hk : k.offered = false) :
    (publish w (some k) t false).2 = some { k with offered := true } := by
  simp [publish, hk]

/-- One offer at most: offering twice adds what offering once added. -/
theorem publish_once (w : Worklog) (k : Call) (t u : String) (b : Bool) :
    let first := publish w (some k) t false
    publish first.1 first.2 u b = first := by
  by_cases hk : k.offered = true
  · simp [publish, hk]
  · have hf : k.offered = false := by simpa using hk
    simp [publish, hf]

theorem off_at_claim_publishes_nothing (w w' : Worklog) (h : w.enabled = false) (t : String) (b : Bool) :
    publish w' (claim w) t b = (w', none) := by
  simp [claim, h, publish]

theorem old_epoch_adds_nothing (w : Worklog) (k : Call) (h : w.epoch ≠ k.epoch) (t : String) (b : Bool) :
    (publish w (some k) t b).1 = w := by
  cases hk : k.offered <;> cases b <;> simp [publish, hk, add, h]

/-- A call claimed while sharing was on, after any reset of the worklog. -/
theorem reset_refuses_the_old_call (w : Worklog) (h : w.enabled = true) (on : Bool) (t : String) (b : Bool) :
    (publish (toggle w on) (claim w) t b).1 = toggle w on := by
  simp only [claim, h, if_true]
  exact old_epoch_adds_nothing _ _ (by simp [toggle]) t b

theorem blank_keeps_the_offer (w : Worklog) (k : Call) (t : String) :
    publish w (some k) t true = (w, some k) := by
  cases hk : k.offered <;> simp [publish, hk]

/-! ## The commentary field's end in a stream of pieces -/

/-- The scanner's state: a string is open; its next character is escaped. -/
structure Scan where
  quoted : Bool
  escaped : Bool
  deriving DecidableEq

def step (s : Scan) (c : Char) : Scan :=
  if s.quoted = true then
    if s.escaped = true then { s with escaped := false }
    else if c = '\\' then { s with escaped := true }
    else if c = '"' then { s with quoted := false }
    else s
  else if c = '"' then { s with quoted := true } else s

/-- The index of the first comma outside a string, scanning from `s`. -/
def cut : Scan → List Char → Option ℕ
  | _, [] => none
  | s, c :: cs => if s.quoted = false ∧ c = ',' then some 0 else (cut (step s c) cs).map (· + 1)

/-- The state a text without a cut leaves. -/
def run : Scan → List Char → Scan
  | s, [] => s
  | s, c :: cs => run (step s c) cs

/-- Pieces find the comma the whole text has, the second piece scanned from the
state the first left. -/
theorem cut_in_pieces (a b : List Char) (s : Scan) :
    cut s (a ++ b) = match cut s a with
      | some i => some i
      | none => (cut (run s a) b).map (· + a.length) := by
  induction a generalizing s with
  | nil => simp [cut, run]
  | cons c cs ih =>
    simp only [List.cons_append, cut, run, List.length_cons]
    split_ifs with h
    · rfl
    · rw [ih (step s c)]
      cases cut (step s c) cs with
      | some i => rfl
      | none =>
        simp only [Option.map_map]
        congr 1

/-- A comma inside a string never cuts. -/
theorem quoted_comma_no_cut (s : Scan) (h : s.quoted = true) (cs : List Char) :
    cut s (',' :: cs) = (cut (step s ',') cs).map (· + 1) := by
  simp [cut, h]

/-! ## Counterexample: the accepted output published without the offered flag -/

def publishUnchecked (w : Worklog) (c : Option Call) (t : String) : Worklog :=
  match c with
  | none => w
  | some k => add w k.epoch t

def sharing : Worklog := ⟨true, 1, []⟩

/-- The streamed note, then the accepted output's: one note. -/
theorem checked_one_note :
    (publish (publish sharing (claim sharing) "Early" false).1
             (publish sharing (claim sharing) "Early" false).2 "Early" false).1.notes = ["Early"] := by
  decide +kernel

/-- Without the flag the call adds the same note twice. -/
theorem unchecked_two_notes :
    (publishUnchecked (publishUnchecked sharing (claim sharing) "Early") (claim sharing) "Early").notes
      = ["Early", "Early"] := by
  decide +kernel

end Mettapedia.Protocols.Agents.CommentaryObserver
