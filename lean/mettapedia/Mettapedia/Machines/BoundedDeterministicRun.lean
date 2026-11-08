import Mathlib.Logic.Relation

/-!
# Bounded execution with explicit terminal observations

The transition function determines all executed steps. A separate answer
predicate classifies a terminal state. Reaching the fuel bound in a state
that still has a transition is exhaustion, not an answer or a failed proof.
Terminal states are inspected even at zero fuel, without taking another step.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BoundedDeterministicRun

universe u

inductive Outcome where
  | completed
  | stuck
  | exhausted
  deriving DecidableEq, Repr

structure Result (State : Type u) where
  state : State
  steps : Nat
  outcome : Outcome
  deriving Repr

variable {State : Type u}

def run (step : State → Option State) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match step state with
      | none => state
      | some next => run step fuel next

def execute (step : State → Option State) (answer : State → Bool) : Nat → State → Result State
  | 0, state =>
      match step state with
      | none => ⟨state, 0, if answer state then .completed else .stuck⟩
      | some _ => ⟨state, 0, .exhausted⟩
  | fuel + 1, state =>
      match step state with
      | none => ⟨state, 0, if answer state then .completed else .stuck⟩
      | some next =>
          let result := execute step answer fuel next
          ⟨result.state, result.steps + 1, result.outcome⟩

theorem run_reachable (step : State → Option State) (fuel : Nat) (state : State) :
    Relation.ReflTransGen (fun first second => step first = some second) state (run step fuel state) := by
  induction fuel generalizing state with
  | zero => exact .refl
  | succ fuel ih =>
      cases transition : step state with
      | none => simpa [run, transition] using (Relation.ReflTransGen.refl (a := state))
      | some next =>
          simpa [run, transition] using
            (Relation.ReflTransGen.head (r := fun first second => step first = some second) transition (ih next))

theorem execute_state (step : State → Option State) (answer : State → Bool) (fuel : Nat) (state : State) :
    (execute step answer fuel state).state = run step fuel state := by
  induction fuel generalizing state with
  | zero => cases transition : step state <;> simp [execute, transition, run]
  | succ fuel ih => cases transition : step state <;> simp [execute, transition, run, ih]

theorem execute_steps_le (step : State → Option State) (answer : State → Bool) (fuel : Nat) (state : State) :
    (execute step answer fuel state).steps ≤ fuel := by
  induction fuel generalizing state with
  | zero => cases transition : step state <;> simp [execute, transition]
  | succ fuel ih => cases transition : step state <;> simp [execute, transition, ih]

theorem exhausted_has_transition (step : State → Option State) (answer : State → Bool)
    (fuel : Nat) (state : State)
    (exhausted : (execute step answer fuel state).outcome = .exhausted) :
    ∃ next, step (execute step answer fuel state).state = some next := by
  induction fuel generalizing state with
  | zero =>
      cases transition : step state with
      | none => cases truth : answer state <;> simp [execute, transition, truth] at exhausted
      | some next => exact ⟨next, by simp [execute, transition]⟩
  | succ fuel ih =>
      cases transition : step state with
      | none => cases truth : answer state <;> simp [execute, transition, truth] at exhausted
      | some next =>
          have remaining := ih next (by simpa [execute, transition] using exhausted)
          simpa [execute, transition] using remaining

theorem exhausted_spends_fuel (step : State → Option State) (answer : State → Bool)
    (fuel : Nat) (state : State)
    (exhausted : (execute step answer fuel state).outcome = .exhausted) :
    (execute step answer fuel state).steps = fuel := by
  induction fuel generalizing state with
  | zero => cases transition : step state <;> simp [execute, transition]
  | succ fuel ih =>
      cases transition : step state with
      | none => cases truth : answer state <;> simp [execute, transition, truth] at exhausted
      | some next =>
          have remaining := ih next (by simpa [execute, transition] using exhausted)
          simpa [execute, transition] using congrArg Nat.succ remaining

theorem completed_is_answer (step : State → Option State) (answer : State → Bool)
    (fuel : Nat) (state : State)
    (completed : (execute step answer fuel state).outcome = .completed) :
    step (execute step answer fuel state).state = none ∧ answer (execute step answer fuel state).state = true := by
  induction fuel generalizing state with
  | zero =>
      cases transition : step state with
      | none => cases truth : answer state <;> simp_all [execute]
      | some next => simp [execute, transition] at completed
  | succ fuel ih =>
      cases transition : step state with
      | none => cases truth : answer state <;> simp_all [execute]
      | some next =>
          have remaining := ih next (by simpa [execute, transition] using completed)
          simpa [execute, transition] using remaining

theorem stuck_is_terminal (step : State → Option State) (answer : State → Bool)
    (fuel : Nat) (state : State)
    (stuck : (execute step answer fuel state).outcome = .stuck) :
    step (execute step answer fuel state).state = none ∧ answer (execute step answer fuel state).state = false := by
  induction fuel generalizing state with
  | zero =>
      cases transition : step state with
      | none => cases truth : answer state <;> simp_all [execute]
      | some next => simp [execute, transition] at stuck
  | succ fuel ih =>
      cases transition : step state with
      | none => cases truth : answer state <;> simp_all [execute]
      | some next =>
          have remaining := ih next (by simpa [execute, transition] using stuck)
          simpa [execute, transition] using remaining

end Mettapedia.Machines.BoundedDeterministicRun
