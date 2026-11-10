import Mettapedia.Machines.Cursor.Protocol

/-!
# First-answer demand over a resumable producer

A provider exposes progress, an answer, exhaustion, a raised fault or interruption.
Progress can change its world without answering. The client stops at its first
terminal reply. The existing cursor scheduler retains live state when its inspection
budget ends, so neither finite production nor eventual success is assumed.
One charged unit below counts a producer request, not a language fuel unit.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoreAndDemand.FirstAnswer

open Mettapedia.Machines.Cursor
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open CategoryTheory

variable (Answer Fault : Type)

inductive Reply (Answer Fault : Type) where
  | progress
  | answer (value : Answer)
  | exhausted
  | raised (fault : Fault)
  | interrupted
  deriving DecidableEq, Repr

inductive Result (Answer Fault : Type) where
  | answer (value : Answer)
  | exhausted
  | raised (fault : Fault)
  | interrupted
  deriving DecidableEq, Repr

def protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Reply Answer Fault
  next _ _ := ()

def accept : Reply Answer Fault → Option (Result Answer Fault)
  | .progress => none
  | .answer value => some (.answer value)
  | .exhausted => some .exhausted
  | .raised fault => some (.raised fault)
  | .interrupted => some .interrupted

def client : Client (P := protocol Answer Fault) (Return := fun _ _ => Result Answer Fault) where
  V _ _ := Option (Result Answer Fault)
  str := fun _ _ => ↾(fun state => match state with
    | some result => ⟨.inl result, nofun⟩
    | none => ⟨.inr (), accept Answer Fault⟩)

variable {Answer Fault} {State : Type}

/-- A provider owns the full state, which may include mutable stores and continuations. -/
def provider (next : State → Reply Answer Fault × State) : Provider (protocol Answer Fault) where
  State _ _ := State
  step state _ := let out := next state; ⟨out.1, out.2⟩

def start (next : State → Reply Answer Fault × State) (state : State) :
    Packet (provider next) (client Answer Fault) () := ⟨(), none, state⟩

theorem advance_start (next : State → Reply Answer Fault × State) (state : State) (budget : Nat) :
    advance (provider next) (client Answer Fault) (fun _ _ => 1) (budget + 1) (start next state) =
      let rest := advance (provider next) (client Answer Fault) (fun _ _ => 1) budget
        ⟨(), accept Answer Fault (next state).1, (next state).2⟩
      (1 + rest.1, rest.2) := rfl

/-- The first answering request leaves the actual reached state and never requests the tail. -/
theorem answer_stops (next : State → Reply Answer Fault × State)
    (before after : State) (value : Answer) (observed : next before = (.answer value, after))
    (extra : Nat) :
    advance (provider next) (client Answer Fault) (fun _ _ => 1) (extra + 2) (start next before) =
      (1, .done ⟨(), Result.answer value, after⟩) := by
  rw [advance_start, observed]
  rfl

/-- Progress before an answer may perform effects; its whole state is threaded onward. -/
inductive Progress (next : State → Reply Answer Fault × State) : State → Nat → State → Prop
  | nil (state : State) : Progress next state 0 state
  | step {before middle after : State} {count : Nat}
      (observed : next before = (.progress, middle))
      (tail : Progress next middle count after) : Progress next before (count + 1) after

theorem first_after_progress (next : State → Reply Answer Fault × State)
    {before ready after : State} {count : Nat} (progressRun : Progress next before count ready)
    (value : Answer) (observed : next ready = (.answer value, after)) :
    advance (provider next) (client Answer Fault) (fun _ _ => 1) (count + 2) (start next before) =
      (count + 1, .done ⟨(), Result.answer value, after⟩) := by
  induction progressRun with
  | nil state => simpa using answer_stops next state after value observed 0
  | @step first middle last count progressed tail ih =>
      rw [advance_start, progressed]
      change (1 + (advance (provider next) (client Answer Fault) (fun _ _ => 1)
          (count + 2) (start next middle)).1,
        (advance (provider next) (client Answer Fault) (fun _ _ => 1)
          (count + 2) (start next middle)).2) = _
      rw [ih observed]
      simp [Nat.add_comm]

/-- Once done, any later scheduler allowance leaves the provider state and account unchanged. -/
theorem no_requests_after_answer (next : State → Reply Answer Fault × State)
    (after : State) (value : Answer) (spent later : Nat) :
    resume (provider next) (client Answer Fault) (fun _ _ => 1) later (base := ())
      (spent, .done ⟨(), Result.answer value, after⟩) =
        (spent, .done ⟨(), Result.answer value, after⟩) := rfl

theorem interruption_is_not_exhaustion (next : State → Reply Answer Fault × State)
    (before after : State) (observed : next before = (.interrupted, after)) :
    advance (provider next) (client Answer Fault) (fun _ _ => 1) 2 (start next before) =
      (1, .done ⟨(), Result.interrupted, after⟩) := by
  rw [advance_start, observed]
  rfl

theorem exhaustion_stops (next : State → Reply Answer Fault × State)
    (before after : State) (observed : next before = (.exhausted, after)) :
    advance (provider next) (client Answer Fault) (fun _ _ => 1) 2 (start next before) =
      (1, .done ⟨(), Result.exhausted, after⟩) := by
  rw [advance_start, observed]
  rfl

/-- The producer may progress forever; a finite scheduler budget retains the residual. -/
theorem endless_progress_pauses (state count : Nat) :
    advance (provider (Answer := Answer) (Fault := Fault) (fun n => (.progress, n + 1)))
      (client Answer Fault) (fun _ _ => 1) count
      (start (fun n => (.progress, n + 1)) state) =
      (count, .paused (start (fun n => (.progress, n + 1)) (state + count))) := by
  induction count generalizing state with
  | zero => simp [advance]
  | succ count ih =>
      change (1 + (advance (provider (Answer := Answer) (Fault := Fault)
          (fun n => (.progress, n + 1))) (client Answer Fault) (fun _ _ => 1) count
          (start (fun n => (.progress, n + 1)) (state + 1))).1,
        (advance (provider (Answer := Answer) (Fault := Fault) (fun n => (.progress, n + 1)))
          (client Answer Fault) (fun _ _ => 1) count
          (start (fun n => (.progress, n + 1)) (state + 1))).2) = _
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

end Mettapedia.Machines.StoreAndDemand.FirstAnswer
