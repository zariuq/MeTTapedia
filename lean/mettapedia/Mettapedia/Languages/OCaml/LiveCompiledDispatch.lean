import Mettapedia.Languages.OCaml.CompiledDispatch
import Mettapedia.Languages.OCaml.InstructionEquality

/-!
# Read-qualified reuse of prepared instruction handlers

A cached instruction is reused only when its exact current reading agrees.
The handler receives the current program for constructor/closure services;
it does not retain stale global declarations. Changed or missing readings
fall back to the current reference instruction. Unrelated code changes need
not discard this handler.

Programs here are immutable snapshots. A native concurrent caller must make
validation and use one stable read or provide the corresponding rely proof.
The check is structural, not asserted constant time or replaced by a hash.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.LiveCompiledDispatch

abbrev Handler := Program → CompiledDispatch.Handler

def prepare (saved : Program) : Array Handler :=
  saved.code.mapIdx fun reference instruction current =>
    CompiledDispatch.compileInstruction current reference instruction

def sameReading (saved current : Program) (reference : Code) : Bool :=
  match saved.instruction? reference, current.instruction? reference with
  | some old, some now => instructionEqual old now
  | _, _ => false

def attempt (saved current : Program) (reference : Code) (environment : Environment)
    (continuation : Continuation) : Option (Except InternalError MachineState) :=
  if sameReading saved current reference then
    (prepare saved)[reference]?.map fun handler => handler current environment continuation
  else none

theorem same_reading_iff (saved current : Program) (reference : Code) :
    sameReading saved current reference = true ↔
      ∃ instruction, saved.instruction? reference = some instruction ∧
        current.instruction? reference = some instruction := by
  cases old : saved.instruction? reference <;> cases now : current.instruction? reference <;>
    simp [sameReading, old, now, instructionEqual_iff]
  exact eq_comm

theorem matching_reading_accepts (saved current : Program) (reference : Code) (instruction : Instruction)
    (old : saved.instruction? reference = some instruction) (now : current.instruction? reference = some instruction)
    (environment : Environment) (continuation : Continuation) :
    attempt saved current reference environment continuation =
      some (evaluateInstruction current reference environment continuation) := by
  have same := (same_reading_iff saved current reference).mpr ⟨instruction, old, now⟩
  unfold attempt
  rw [same]
  simp only [↓reduceIte, prepare, Array.getElem?_mapIdx, Option.map_map, Function.comp_def]
  change (saved.instruction? reference).map (fun instruction =>
    CompiledDispatch.compileInstruction current reference instruction environment continuation) = _
  rw [old]
  exact congrArg some (CompiledDispatch.instruction_exact current reference instruction now environment continuation)

theorem accepted_exact (saved current : Program) (reference : Code) (environment : Environment)
    (continuation : Continuation) (result : Except InternalError MachineState)
    (accepted : attempt saved current reference environment continuation = some result) :
    result = evaluateInstruction current reference environment continuation := by
  by_cases same : sameReading saved current reference = true
  · obtain ⟨instruction, old, now⟩ := (same_reading_iff saved current reference).mp same
    rw [matching_reading_accepts saved current reference instruction old now environment continuation] at accepted
    exact (Option.some.inj accepted).symm
  · simp [attempt, same] at accepted

def evaluate (saved current : Program) (reference : Code) (environment : Environment)
    (continuation : Continuation) : Except InternalError MachineState :=
  (attempt saved current reference environment continuation).getD
    (evaluateInstruction current reference environment continuation)

theorem evaluate_exact (saved current : Program) (reference : Code) (environment : Environment)
    (continuation : Continuation) : evaluate saved current reference environment continuation =
      evaluateInstruction current reference environment continuation := by
  cases tried : attempt saved current reference environment continuation with
  | none => simp [evaluate, tried]
  | some result => simpa [evaluate, tried] using accepted_exact saved current reference environment continuation result tried

def step (saved current : Program) : MachineState → Except InternalError (Option MachineState)
  | .halted _ => .ok none
  | .evaluate reference environment continuation => (evaluate saved current reference environment continuation).map some
  | .returned value (.matchValue clauses environment :: continuation) =>
      (CompiledDispatch.returnFromMatch value (ConstructorDispatch.compile clauses) environment continuation).map some
  | .returned value continuation => (returnValue current value continuation).map some

theorem step_exact (saved current : Program) (state : MachineState) : step saved current state = machineStep current state := by
  cases state with
  | halted => rfl
  | evaluate => simp only [step, machineStep, evaluate_exact]
  | returned value continuation =>
      cases continuation with
      | nil => rfl
      | cons frame rest =>
          cases frame <;> try rfl
          simp only [step, machineStep]
          rw [CompiledDispatch.match_return_exact current]

def run (saved current : Program) : Nat → MachineState → RunResult
  | _, .halted result => .complete result
  | 0, state => .pending state
  | budget + 1, state => match step saved current state with
      | .error error => .invalid error
      | .ok none => .invalid .unexpectedStop
      | .ok (some next) => run saved current budget next

theorem run_exact (saved current : Program) (budget : Nat) (state : MachineState) :
    run saved current budget state = OCaml.run current budget state := by
  induction budget generalizing state with
  | zero => cases state <;> rfl
  | succ budget ih =>
      cases state with
      | halted => rfl
      | evaluate | returned => simp only [run, OCaml.run, step_exact, ih]; rfl

def resume (saved current : Program) (budget : Nat) : RunResult → RunResult
  | .pending state => run saved current budget state
  | result => result

theorem resume_exact (saved current : Program) (budget : Nat) (result : RunResult) :
    resume saved current budget result = OCaml.resume current budget result := by
  cases result <;> simp [resume, OCaml.resume, run_exact]

/-- Even between two different program snapshots, the second page sees its
current reference program and the first page's exact saved continuation. -/
theorem changed_program_pages (saved first second : Program) (left right : Nat) (state : MachineState) :
    resume saved second right (run saved first left state) =
      OCaml.resume second right (OCaml.run first left state) := by rw [run_exact, resume_exact]

namespace Controls

def saved : Program := {code := #[.literal (.integer 7), .literal (.integer 0)], entry := 0}
def changed : Program := {code := #[.literal (.integer 9), .literal (.integer 0)], entry := 0}
def unrelated : Program := {code := #[.literal (.integer 7), .literal (.integer 99)], entry := 0}

theorem changed_reading_refuses : attempt saved changed 0 [] [] = none := by rfl

theorem stale_cache_falls_back_to_current_meaning :
    run saved changed 2 (begin changed) = .complete (.ok (.literal (.integer 9))) := by rfl

theorem unrelated_code_change_keeps_handler :
    attempt saved unrelated 0 [] [] = some (.ok (.returned (.literal (.integer 7)) [])) := by rfl

theorem change_before_read_uses_new_instruction :
    resume saved changed 2 (run saved saved 0 (begin saved)) = .complete (.ok (.literal (.integer 9))) := by rfl

theorem change_after_read_preserves_captured_return :
    resume saved changed 1 (run saved saved 1 (begin saved)) = .complete (.ok (.literal (.integer 7))) := by rfl

def absentConstructor : Program := {code := #[.variant 0 0 []], entry := 0}
def presentConstructor : Program :=
  {constructors := [⟨0, 0, 0⟩], code := #[.variant 0 0 []], entry := 0}

theorem services_use_current_declarations :
    attempt absentConstructor presentConstructor 0 [] [] = some (.ok (.returned (.variant 0 0 []) [])) := by rfl

end Controls

end Mettapedia.Languages.OCaml.LiveCompiledDispatch
