import Mettapedia.Machines.ResumableSearchRunner

/-! A resumable filter over independently supplied candidates. One outer
tick advances exactly one retained inner machine. Completed candidates are
classified before starting the next; the tick allowance is never reset.
The result classification is separate from search and scheduling.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResumableSearchFilter

open ResumableSearchRunner

inductive Decision (Answer Error : Type) where
  | accept (answer : Answer)
  | reject
  | fault (error : Error)

inductive State (Input σ Run Receipt Answer Error : Type) where
  | done (answers : List Answer)
  | active (remaining : List Input) (answers : List Answer) (machine : Machine σ Run Receipt)
  | failed (error : Error) (remaining : List Input) (answers : List Answer) (machine : Machine σ Run Receipt)

namespace State

variable {Input σ Run Receipt Answer Error : Type}

def answers : State Input σ Run Receipt Answer Error → List Answer
  | .done found => found
  | .active _ found _ => found
  | .failed _ _ found _ => found

end State

variable {Input σ Run Receipt Answer Error : Type}

def begin (search : Search σ Run Receipt) (request : Input → σ)
    (inputs : List Input) (answers : List Answer := []) : State Input σ Run Receipt Answer Error :=
  match inputs with
  | [] => .done answers
  | first :: rest => .active rest answers (Machine.begin search (request first))

def step (search : Search σ Run Receipt) (request : Input → σ) (read : σ → Decision Answer Error)
    (quantum : Nat) : State Input σ Run Receipt Answer Error → State Input σ Run Receipt Answer Error
  | .done answers => .done answers
  | .failed error remaining answers machine => .failed error remaining answers machine
  | .active remaining answers machine =>
      let next := Machine.tick search machine quantum
      if next.phase = .done then
        match read next.state with
        | .accept answer => begin search request remaining (answer :: answers)
        | .reject => begin search request remaining answers
        | .fault error => .failed error remaining answers next
      else .active remaining answers next

def advance (search : Search σ Run Receipt) (request : Input → σ) (read : σ → Decision Answer Error) :
    Nat → Nat → State Input σ Run Receipt Answer Error → State Input σ Run Receipt Answer Error
  | 0, _, state => state
  | ticks + 1, quantum, state => advance search request read ticks quantum (step search request read quantum state)

theorem advance_zero (search : Search σ Run Receipt) (request : Input → σ) (read : σ → Decision Answer Error)
    (quantum : Nat) (state : State Input σ Run Receipt Answer Error) :
    advance search request read 0 quantum state = state := rfl

theorem advance_add (search : Search σ Run Receipt) (request : Input → σ) (read : σ → Decision Answer Error)
    (first extra quantum : Nat) (state : State Input σ Run Receipt Answer Error) :
    advance search request read (first + extra) quantum state =
      advance search request read extra quantum (advance search request read first quantum state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, advance]
  | succ first ih =>
    rw [Nat.succ_add]
    exact ih _

theorem begin_answers (search : Search σ Run Receipt) (request : Input → σ)
    (inputs : List Input) (answers : List Answer) :
    (begin search request inputs answers : State Input σ Run Receipt Answer Error).answers = answers := by
  cases inputs <;> rfl

theorem step_retains_answers (search : Search σ Run Receipt) (request : Input → σ) (read : σ → Decision Answer Error)
    (quantum : Nat) (state : State Input σ Run Receipt Answer Error) :
    state.answers <:+ (step search request read quantum state).answers := by
  cases state with
  | done answers => exact ⟨[], rfl⟩
  | failed error remaining answers machine => exact ⟨[], rfl⟩
  | active remaining answers machine =>
    simp only [step]
    split
    · cases read (Machine.tick search machine quantum).state with
      | accept answer =>
        rw [begin_answers]
        exact ⟨[answer], rfl⟩
      | reject =>
        rw [begin_answers]
        exact ⟨[], rfl⟩
      | fault error => exact ⟨[], rfl⟩
    · exact ⟨[], rfl⟩

theorem advance_retains_answers (search : Search σ Run Receipt) (request : Input → σ) (read : σ → Decision Answer Error)
    (ticks quantum : Nat) (state : State Input σ Run Receipt Answer Error) :
    state.answers <:+ (advance search request read ticks quantum state).answers := by
  induction ticks generalizing state with
  | zero => exact ⟨[], rfl⟩
  | succ ticks ih =>
    exact (step_retains_answers search request read quantum state).trans (ih _)

#print axioms advance_add
#print axioms advance_retains_answers

end Mettapedia.Machines.ResumableSearchFilter
