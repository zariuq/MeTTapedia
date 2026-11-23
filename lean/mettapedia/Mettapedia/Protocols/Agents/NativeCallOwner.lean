import Mathlib.Tactic

/-!
# A provider-call owner: one claim, at most one submission, spent after delivery

An owner moves `ready → claiming → claimed → submitted t`, or to `refused` when
admission is denied; delivery releases it to `spent`. A `begin` on any owner
that is not `ready` changes nothing: a replayed or concurrent begin is a
duplicate. Only a submitted owner owns its transport.

Invariants proved here, for every event trace:
* at most one submission, from any starting phase;
* `spent` is absorbing and owns no transport;
* a replayed `begin` never claims again.

The counterexample is the design choice it guards: if a released (absent) phase
record were read as `ready` again, one owner could submit twice. The native
port therefore reads an absent record as `spent`.

This is an abstract transition contract. It is not a refinement proof of the
MeTTa owner or of the provider ledger, and it says nothing about whether a
lost reply's remote effect happened; that remains an uncertain outcome.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.NativeCallOwner

inductive Phase (T : Type) where
  | ready | claiming | claimed | submitted (t : T) | refused | spent
  deriving DecidableEq

inductive Event (T : Type) where
  | begin | admitted | denied | submit (t : T) | deliver

variable {T : Type}

/-- One transition. Events with no rule leave the phase unchanged. -/
def step : Phase T → Event T → Phase T
  | .ready, .begin => .claiming
  | .claiming, .admitted => .claimed
  | .claiming, .denied => .refused
  | .claimed, .submit t => .submitted t
  | _, .deliver => .spent
  | p, _ => p

def submits : Phase T → Event T → Bool
  | .claimed, .submit _ => true
  | _, _ => false

/-- Submissions performed along a trace. -/
def submissions : Phase T → List (Event T) → Nat
  | _, [] => 0
  | p, e :: es => (if submits p e then 1 else 0) + submissions (step p e) es

def run (p : Phase T) (es : List (Event T)) : Phase T := es.foldl step p

/-- Only a submitted owner owns a transport. -/
def Owns (p : Phase T) (t : T) : Prop := p = .submitted t

/-- Phases from which no submission can follow. -/
def Settled : Phase T → Prop
  | .submitted _ | .refused | .spent => True
  | _ => False

theorem settled_step {p : Phase T} (h : Settled p) (e : Event T) : Settled (step p e) := by
  cases p <;> cases e <;> simp_all [Settled, step]

theorem settled_no_submissions {p : Phase T} (h : Settled p) (es : List (Event T)) :
    submissions p es = 0 := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    have hs : submits p e = false := by cases p <;> cases e <;> simp_all [Settled, submits]
    simp [submissions, hs, ih (settled_step h e)]

/-- One owner submits at most once, whatever the events and their order. -/
theorem at_most_one_submission (p : Phase T) (es : List (Event T)) :
    submissions p es ≤ 1 := by
  induction es generalizing p with
  | nil => simp [submissions]
  | cons e es ih =>
    cases p <;> cases e <;>
      simp_all [submissions, submits, step,
        settled_no_submissions (p := (Phase.submitted _ : Phase T)) (by simp [Settled])]

theorem spent_absorbing (es : List (Event T)) : run (.spent : Phase T) es = .spent := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simpa [run, step] using ih

theorem spent_owns_nothing (es : List (Event T)) (t : T) : ¬ Owns (run (.spent : Phase T) es) t := by
  simp [Owns, spent_absorbing]

/-- A replayed or concurrent begin is a duplicate: it changes nothing. -/
theorem replayed_begin_is_duplicate {p : Phase T} (h : p ≠ .ready) : step p .begin = p := by
  cases p <;> simp_all [step]

/-- The rejected design: an absent (released) record read as ready again. -/
def stepAbsentAsReady : Phase T → Event T → Phase T
  | .ready, .begin => .claiming
  | .claiming, .admitted => .claimed
  | .claiming, .denied => .refused
  | .claimed, .submit t => .submitted t
  | _, .deliver => .ready
  | p, _ => p

def submissionsAbsentAsReady : Phase T → List (Event T) → Nat
  | _, [] => 0
  | p, e :: es => (if submits p e then 1 else 0) + submissionsAbsentAsReady (stepAbsentAsReady p e) es

/-- Under that reading one owner, replayed after delivery, submits twice. -/
theorem absent_as_ready_submits_twice (a b : T) :
    submissionsAbsentAsReady (.ready : Phase T)
      [.begin, .admitted, .submit a, .deliver, .begin, .admitted, .submit b] = 2 := by
  simp [submissionsAbsentAsReady, stepAbsentAsReady, submits]

end Mettapedia.Protocols.Agents.NativeCallOwner
