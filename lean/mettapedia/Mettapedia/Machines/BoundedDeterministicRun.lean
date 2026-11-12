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

theorem run_of_none (step : State → Option State) (state : State) (stopped : step state = none)
    (fuel : Nat) : run step fuel state = state := by
  cases fuel <;> simp [run, stopped]

/-- Continuing from the retained state executes the remaining suffix; it does
not revisit earlier transitions, including when execution is already stuck. -/
theorem run_add (step : State → Option State) (first second : Nat) (state : State) :
    run step (first + second) state = run step second (run step first state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih =>
      cases taken : step state with
      | none => simp [run, taken, run_of_none step state taken]
      | some next => simpa [run, taken, Nat.succ_add] using ih next

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

/-- Every finite executed path has an allowance after which all future
allowances continue from its actual endpoint. No termination is assumed. -/
theorem run_suffix_of_path (step : State → Option State) {before after : State}
    (path : Relation.ReflTransGen (fun first second => step first = some second) before after) :
    ∃ spent, ∀ remaining, run step (spent + remaining) before = run step remaining after := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0,fun _ => by simp only [Nat.zero_add]⟩
  | @head before middle edge tail ih =>
      obtain ⟨spent,continues⟩ := ih
      refine ⟨spent + 1,?_⟩
      intro remaining
      calc
        run step (spent + 1 + remaining) before = run step ((spent + remaining) + 1) before := by
          rw [Nat.add_right_comm spent 1 remaining]
        _ = run step (spent + remaining) middle := by simp only [run,edge]
        _ = run step remaining after := continues remaining

theorem reachable_iff_run (step : State → Option State) (before after : State) :
    Relation.ReflTransGen (fun first second => step first = some second) before after ↔
      ∃ fuel, run step fuel before = after := by
  constructor
  · intro path
    obtain ⟨spent,continues⟩ := run_suffix_of_path step path
    exact ⟨spent,by simpa only [Nat.add_zero,run] using continues 0⟩
  · rintro ⟨fuel,rfl⟩
    exact run_reachable step fuel before

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
