import Mettapedia.Languages.PartrecMachine.BoundedReduction
import Mettapedia.Languages.PartrecMachine.Realization

/-!
# Resumable bounded observation of the partial-recursive machine

The executable boundary uses the existing `PartrecMachine.frameStep` and
retains its actual final frame state when the observation budget is exhausted.
An exhausted result says only that this finite prefix has not halted. It is
not a refutation of the unbounded computation.

Answers are exactly the bounded reductions of the authored machine. Increasing
the budget by resuming the retained state agrees with a single combined budget;
successful answers persist. For every code and input, an answer occurs at some
budget exactly when it belongs to Mathlib's partial evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.SourceBudget

open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec

/-- A bounded observation either reports the halted output or retains the
exact machine state at which further work is required. -/
inductive Result where
  | answer (output : List Nat)
  | exhausted (state : FrameState)

def Result.state : Result → FrameState
  | .answer output => .inr (.inr output)
  | .exhausted state => state

/-- Inspect the existing frame representation without running another step. -/
def observe : FrameState → Result
  | .inr (.inr output) => .answer output
  | state => .exhausted state

@[simp] theorem state_observe (state : FrameState) : (observe state).state = state := by
  rcases state with _ | _ | _ <;> rfl

theorem observe_answer_iff (state : FrameState) (output : List Nat) :
    observe state = .answer output ↔ state = .inr (.inr output) := by
  rcases state with _ | _ | _ <;> simp [observe]

/-- Run a finite prefix of the existing machine and inspect its endpoint.
The absorbing halted frame permits unused budget without inventing a
reduction after the machine has halted. -/
def run (budget : Nat) (state : FrameState) : Result :=
  observe (frameStep^[budget] state)

def resume (budget : Nat) (result : Result) : Result := run budget result.state

/-- Starting a program supplies code, an empty continuation and its input. -/
def start (code : Code) (input : List Nat) : FrameState := .inl (code, [], input)

theorem run_answer_iff (budget : Nat) (state : FrameState) (output : List Nat) :
    run budget state = .answer output ↔
      ReducesWithin budget (encFrameState state) (encCfg (.halt output)) := by
  rw [run, observe_answer_iff, reducesWithin_halt_iff]

/-- Resumption retains exactly the work already performed. -/
theorem resume_run (first later : Nat) (state : FrameState) :
    resume later (run first state) = run (first + later) state := by
  simp only [resume, run, state_observe]
  rw [Nat.add_comm first later, Function.iterate_add_apply]

theorem run_halted (budget : Nat) (output : List Nat) :
    run budget (.inr (.inr output)) = .answer output := by
  simp [run, observe, Function.iterate_fixed (show frameStep (.inr (.inr output)) = _ from rfl)]

/-- A completed result remains the same under any further observation budget. -/
theorem answer_persists {first : Nat} {state : FrameState} {output : List Nat}
    (answered : run first state = .answer output) (later : Nat) :
    run (first + later) state = .answer output := by
  rw [← resume_run, answered]
  exact run_halted later output

/-- The exact retained state supports all later finite answers. -/
theorem exhausted_resume_iff {first : Nat} {state pending : FrameState}
    (exhausted : run first state = .exhausted pending) (later : Nat) (output : List Nat) :
    run later pending = .answer output ↔ run (first + later) state = .answer output := by
  rw [← resume_run, exhausted]
  rfl

/-- Exhaustion excludes only an answer within the inspected prefix. -/
theorem exhausted_no_answer_within {budget : Nat} {state pending : FrameState}
    (exhausted : run budget state = .exhausted pending) (output : List Nat) :
    ¬ ReducesWithin budget (encFrameState state) (encCfg (.halt output)) := by
  intro answered
  have same := (run_answer_iff budget state output).mpr answered
  rw [exhausted] at same
  cases same

/-- No bound is a boundary of the machine's meaning. -/
theorem eventually_answer_iff (code : Code) (input output : List Nat) :
    (∃ budget, run budget (start code input) = .answer output) ↔ output ∈ code.eval input := by
  rw [← adequacy]
  constructor
  · rintro ⟨budget, answered⟩
    exact reflTransGen_of_reducesWithin ((run_answer_iff budget (start code input) output).mp answered)
  · intro reduced
    obtain ⟨budget, within⟩ := exists_reducesWithin_of_reflTransGen reduced
    exact ⟨budget, (run_answer_iff budget (start code input) output).mpr within⟩

/-- Different budgets cannot manufacture different outputs for one code. -/
theorem answers_unique {code : Code} {input left right : List Nat} {first second : Nat}
    (one : run first (start code input) = .answer left)
    (two : run second (start code input) = .answer right) : left = right :=
  Part.mem_unique ((eventually_answer_iff code input left).mp ⟨first, one⟩)
    ((eventually_answer_iff code input right).mp ⟨second, two⟩)

namespace Controls

/-- A pending finite observation can still be followed by a valid answer. -/
theorem zero_budget_then_success :
    run 0 (start .succ []) = .exhausted (start .succ []) ∧
      run 2 (start .succ []) = .answer [1] := by
  constructor <;> rfl

/-- The same status also occurs for a computation that never answers. -/
theorem divergent_exhausts (budget : Nat) (input : List Nat) :
    ∃ pending, run budget (start silent input) = .exhausted pending := by
  cases found : run budget (start silent input) with
  | exhausted pending => exact ⟨pending, rfl⟩
  | answer output =>
      have member := (eventually_answer_iff silent input output).mp ⟨budget, found⟩
      rw [silent_eval] at member
      exact False.elim (Part.notMem_none _ member)

/-- A spent budget does not imply semantic failure. -/
theorem exhaustion_is_not_refusal :
    (∃ pending, run 0 (start .succ []) = .exhausted pending) ∧
      [1] ∈ Code.succ.eval [] := by
  exact ⟨⟨_, rfl⟩, (eventually_answer_iff .succ [] [1]).mp ⟨2, rfl⟩⟩

end Controls

#print axioms run_answer_iff
#print axioms resume_run
#print axioms answer_persists
#print axioms eventually_answer_iff
#print axioms answers_unique
#print axioms Controls.divergent_exhausts

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.SourceBudget
