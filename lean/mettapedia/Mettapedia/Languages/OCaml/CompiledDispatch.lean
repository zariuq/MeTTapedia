import Mettapedia.Languages.OCaml.ConstructorDispatch
import Mettapedia.Languages.OCaml.Machine

/-!
# Prepared instruction and ordered-clause dispatch for the OCaml CEK machine

Program preparation specializes every instruction to an environment/continuation
handler. Execution reads the prepared handler instead of decoding an instruction
constructor on each visit. Match-return states use the independently compiled
constructor screens, preserving first-match selection and binding order.

The proof retains exact source machine steps, pending states and errors. It is
a Lean realization and not a C speed claim: closure capture, preparation, lookup
and continuation costs need separate implementation accounts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.CompiledDispatch

abbrev Handler := Environment → Continuation → Except InternalError MachineState

def compileInstruction (program : Program) (reference : Code) : Instruction → Handler
  | .literal value => fun _ continuation => .ok (.returned (.literal value) continuation)
  | .variable index => fun environment continuation =>
      match environment[index]? with
      | some value => .ok (.returned value continuation)
      | none => .error (.unboundVariable index)
  | .lambda _ _ => fun environment continuation =>
      .ok (.returned (.closure (.lambda reference) environment) continuation)
  | .apply function argument => fun environment continuation =>
      .ok (.evaluate argument environment (.argument function environment :: continuation))
  | .letValue pattern value body => fun environment continuation =>
      .ok (.evaluate value environment (.letValue pattern body environment :: continuation))
  | .letRecursive definitions body => fun environment continuation =>
      .ok (.evaluate body (recursiveEnvironment reference definitions environment) continuation)
  | .branch condition yes no => fun environment continuation =>
      .ok (.evaluate condition environment (.branch yes no environment :: continuation))
  | .andThen left right => fun environment continuation =>
      .ok (.evaluate left environment (.andThen right environment :: continuation))
  | .orElse left right => fun environment continuation =>
      .ok (.evaluate left environment (.orElse right environment :: continuation))
  | .tuple fields => fun environment continuation => startArguments program .tuple fields environment continuation
  | .variant typeId constructor fields => fun environment continuation =>
      startArguments program (.variant typeId constructor) fields environment continuation
  | .primitive operator arguments => fun environment continuation =>
      startArguments program (.primitive operator) arguments environment continuation
  | .cons head tail => fun environment continuation =>
      .ok (.evaluate tail environment (.consTail head environment :: continuation))
  | .matchValue scrutinee clauses => fun environment continuation =>
      .ok (.evaluate scrutinee environment (.matchValue clauses environment :: continuation))

theorem instruction_exact (program : Program) (reference : Code) (instruction : Instruction)
    (found : program.instruction? reference = some instruction)
    (environment : Environment) (continuation : Continuation) :
    compileInstruction program reference instruction environment continuation =
      evaluateInstruction program reference environment continuation := by
  cases instruction <;> simp only [compileInstruction, evaluateInstruction, found]
  all_goals rfl

def prepare (program : Program) : Array Handler := program.code.mapIdx (compileInstruction program)

def evaluate (_program : Program) (handlers : Array Handler) (reference : Code)
    (environment : Environment) (continuation : Continuation) : Except InternalError MachineState :=
  match handlers[reference]? with
  | none => .error (.missingCode reference)
  | some handler => handler environment continuation

theorem prepared_evaluate_exact (program : Program) (reference : Code)
    (environment : Environment) (continuation : Continuation) :
    evaluate program (prepare program) reference environment continuation =
      evaluateInstruction program reference environment continuation := by
  simp only [evaluate, prepare, Array.getElem?_mapIdx]
  cases found : program.code[reference]? with
  | none => simp only [evaluateInstruction, Program.instruction?, found]; rfl
  | some instruction =>
      exact instruction_exact program reference instruction found environment continuation

def returnFromMatch (value : Value) (clauses : List ConstructorDispatch.Row)
    (environment : Environment) (continuation : Continuation) : Except InternalError MachineState :=
  match ConstructorDispatch.select clauses value with
  | none => .ok (.halted (.error .matchFailure))
  | some (body, bindings) => .ok (.evaluate body (extend environment bindings) continuation)

theorem match_return_exact (program : Program) (value : Value) (clauses : List Clause)
    (environment : Environment) (continuation : Continuation) :
    returnFromMatch value (ConstructorDispatch.compile clauses) environment continuation =
      returnValue program value (.matchValue clauses environment :: continuation) := by
  rw [returnFromMatch, ConstructorDispatch.compiled_select_exact]
  rfl

def step (program : Program) (handlers : Array Handler) : MachineState → Except InternalError (Option MachineState)
  | .halted _ => .ok none
  | .evaluate reference environment continuation =>
      (evaluate program handlers reference environment continuation).map some
  | .returned value (.matchValue clauses environment :: continuation) =>
      (returnFromMatch value (ConstructorDispatch.compile clauses) environment continuation).map some
  | .returned value continuation => (returnValue program value continuation).map some

theorem step_exact (program : Program) (state : MachineState) :
    step program (prepare program) state = machineStep program state := by
  cases state with
  | halted => rfl
  | evaluate reference environment continuation => simp only [step, machineStep, prepared_evaluate_exact]
  | returned value continuation =>
      cases continuation with
      | nil => rfl
      | cons frame rest =>
          cases frame <;> try rfl
          simp only [step, machineStep]
          rw [match_return_exact program]

def run (program : Program) (handlers : Array Handler) : Nat → MachineState → RunResult
  | _, .halted result => .complete result
  | 0, state => .pending state
  | fuel + 1, state => match step program handlers state with
      | .error error => .invalid error
      | .ok none => .invalid .unexpectedStop
      | .ok (some next) => run program handlers fuel next

theorem run_exact (program : Program) (fuel : Nat) (state : MachineState) :
    run program (prepare program) fuel state = OCaml.run program fuel state := by
  induction fuel generalizing state with
  | zero => cases state <;> rfl
  | succ fuel ih =>
      cases state with
      | halted result => rfl
      | evaluate reference environment continuation =>
          simp only [run, OCaml.run, step_exact, ih]
          rfl
      | returned value continuation =>
          simp only [run, OCaml.run, step_exact, ih]
          rfl

def resume (program : Program) (handlers : Array Handler) (budget : Nat) : RunResult → RunResult
  | .pending state => run program handlers budget state
  | result => result

theorem resume_exact (program : Program) (budget : Nat) (result : RunResult) :
    resume program (prepare program) budget result = OCaml.resume program budget result := by
  cases result <;> simp [resume, OCaml.resume, run_exact]

theorem pages_exact (program : Program) (first later : Nat) (state : MachineState) :
    resume program (prepare program) later (run program (prepare program) first state) =
      OCaml.run program (first + later) state := by
  rw [run_exact, resume_exact, run_resume]

/-- Every actual state transition is retained; this trace is stronger than
the final-value observation, including pending continuations at its end. -/
def trace (program : Program) (handlers : Array Handler) : Nat → MachineState → List MachineState
  | 0, _ => []
  | fuel + 1, state =>
      match step program handlers state with
      | .ok (some next) => next :: trace program handlers fuel next
      | _ => []

def referenceTrace (program : Program) : Nat → MachineState → List MachineState
  | 0, _ => []
  | fuel + 1, state =>
      match machineStep program state with
      | .ok (some next) => next :: referenceTrace program fuel next
      | _ => []

theorem trace_exact (program : Program) (fuel : Nat) (state : MachineState) :
    trace program (prepare program) fuel state = referenceTrace program fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rw [trace, referenceTrace, step_exact]
      cases machineStep program state with
      | error => rfl
      | ok next => cases next <;> simp only [ih]

end Mettapedia.Languages.OCaml.CompiledDispatch
