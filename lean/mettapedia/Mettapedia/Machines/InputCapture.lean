import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-!
# Capture is private until publication is admitted

The account is ordered: committed bytes, private pending bytes, then unread
hardware bytes. Capture takes only a prefix fitting private capacity.
Publication moves only the admitted prefix; an internal epoch admits none.

The hardware-read and epoch-commit callbacks remain interpretation boundaries.
The model proves conservation and bounded private storage for arbitrary command
sequences, not infinite hardware buffering or correctness of a C compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.InputCapture

universe u
structure State (α : Type u) where
  committed : List α
  pending : List α
  unread : List α
  deriving Repr, DecidableEq

def account {α : Type u} (s : State α) := s.committed ++ s.pending ++ s.unread

def capture {α : Type u} (capacity : Nat) (s : State α) : State α :=
  let room := capacity - s.pending.length
  { s with pending := s.pending ++ s.unread.take room, unread := s.unread.drop room }

def publish {α : Type u} (internal : Bool) (quota : Nat) (s : State α) : State α :=
  if internal then s else
    { s with committed := s.committed ++ s.pending.take quota, pending := s.pending.drop quota }

theorem capture_conserves {α : Type u} (capacity : Nat) (s : State α) :
    account (capture capacity s) = account s := by
  have split := congrArg (fun xs => s.committed ++ s.pending ++ xs)
    (List.take_append_drop (capacity - s.pending.length) s.unread)
  simpa only [account, capture, List.append_assoc] using split

theorem publish_conserves {α : Type u} (internal : Bool) (quota : Nat) (s : State α) :
    account (publish internal quota s) = account s := by
  cases internal with
  | true => rfl
  | false =>
      have split := congrArg (fun xs => s.committed ++ xs ++ s.unread)
        (List.take_append_drop quota s.pending)
      simpa only [account, publish, Bool.false_eq_true, ↓reduceIte, List.append_assoc] using split

theorem capture_bounded {α : Type u} {capacity : Nat} (s : State α)
    (bounded : s.pending.length ≤ capacity) :
    (capture capacity s).pending.length ≤ capacity := by
  simp only [capture, List.length_append, List.length_take]
  omega

theorem publish_bounded {α : Type u} {capacity : Nat} (s : State α)
    (bounded : s.pending.length ≤ capacity) (internal : Bool) (quota : Nat) :
    (publish internal quota s).pending.length ≤ capacity := by
  cases internal <;> simp_all [publish]
  omega

theorem full_does_not_consume {α : Type u} {capacity : Nat} (s : State α)
    (full : s.pending.length = capacity) : (capture capacity s).unread = s.unread := by
  simp [capture, full]

inductive Command | capture | publish (internal : Bool) (quota : Nat)

def step {α : Type u} (capacity : Nat) (s : State α) : Command → State α
  | .capture => capture capacity s
  | .publish internal quota => publish internal quota s

def run {α : Type u} (capacity : Nat) : State α → List Command → State α
  | s, [] => s
  | s, c :: rest => run capacity (step capacity s c) rest

theorem run_conserves {α : Type u} (capacity : Nat) (s : State α) (commands : List Command) :
    account (run capacity s commands) = account s := by
  induction commands generalizing s with
  | nil => rfl
  | cons c rest ih =>
      rw [run, ih]
      cases c with
      | capture => exact capture_conserves capacity s
      | publish internal quota => exact publish_conserves internal quota s

theorem run_bounded {α : Type u} {capacity : Nat} (s : State α)
    (bounded : s.pending.length ≤ capacity) (commands : List Command) :
    (run capacity s commands).pending.length ≤ capacity := by
  induction commands generalizing s with
  | nil => exact bounded
  | cons c rest ih =>
      apply ih
      cases c with
      | capture => exact capture_bounded s bounded
      | publish internal quota => exact publish_bounded s bounded internal quota

/-- Reading the head before an unsuccessful publication, with no private
retention, loses one occurrence regardless of its value or duplicate bytes. -/
theorem direct_read_refusal_loses_head {α : Type u} (published tail : List α) (x : α) :
    account (State.mk published [] tail) ≠ account (State.mk published [] (x :: tail)) := by
  intro same
  have sizes := congrArg List.length same
  simp [account] at sizes

theorem keyboard_output_mask :
    ∀ status : Fin 256, status.val &&& 0x21 = 1 ↔
      status.val % 2 = 1 ∧ (status.val / 32) % 2 = 0 := by
  decide +kernel

#print axioms run_conserves
#print axioms run_bounded
#print axioms direct_read_refusal_loses_head
#print axioms keyboard_output_mask

end Mettapedia.Machines.InputCapture
