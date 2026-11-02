import Mettapedia.Languages.OCaml.PatternMatching
import Mettapedia.Languages.OCaml.Primitives

/-! A resumable environment machine for indexed OCaml code. Arguments and
tuple/constructor fields run right to left. Captured code and environments
are immutable; recursive closures refer to their group instead of carrying
cyclic environments. This is a Lean reference executor, not the emitted
GSLT realization or the source correspondence theorem. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

inductive Build where
  | tuple
  | variant (typeId constructor : Nat)
  | primitive (operator : Primitive)
  deriving Repr, DecidableEq, BEq

inductive Frame where
  | argument (function : Code) (environment : Environment)
  | function (argument : Value)
  | letValue (pattern : MatchPattern) (body : Code) (environment : Environment)
  | branch (yes no : Code) (environment : Environment)
  | andThen (right : Code) (environment : Environment)
  | orElse (right : Code) (environment : Environment)
  | booleanResult
  | consTail (head : Code) (environment : Environment)
  | consHead (tail : Value)
  | gather (kind : Build) (reversed : List Code) (environment : Environment) (suffix : List Value)
  | matchValue (clauses : List Clause) (environment : Environment)
  deriving Repr, BEq

abbrev Continuation := List Frame

inductive MachineState where
  | evaluate (code : Code) (environment : Environment) (continuation : Continuation)
  | returned (value : Value) (continuation : Continuation)
  | halted (result : Result)
  deriving Repr, BEq

def finishBuild (program : Program) (kind : Build) (values : List Value)
    (continuation : Continuation) : Except InternalError MachineState := do
  match kind with
  | .tuple =>
      if values.length < 2 then throw (.invalidTupleArity values.length)
      else pure (.returned (.tuple values) continuation)
  | .variant typeId constructor =>
      if program.constructors.any (fun declaration =>
          declaration.typeId == typeId && declaration.ordinal == constructor &&
            declaration.arity == values.length) then
        pure (.returned (.variant typeId constructor values) continuation)
      else throw (.invalidConstructor typeId constructor values.length)
  | .primitive operator =>
      match ← operator.eval values with
      | .ok value => pure (.returned value continuation)
      | .error fault => pure (.halted (.error fault))

def startArguments (program : Program) (kind : Build) (arguments : List Code)
    (environment : Environment) (continuation : Continuation) : Except InternalError MachineState :=
  match arguments.reverse with
  | [] => finishBuild program kind [] continuation
  | last :: rest => .ok (.evaluate last environment (.gather kind rest environment [] :: continuation))

def enterBody (parameter : MatchPattern) (argument : Value) (body : Code)
    (captured : Environment) (continuation : Continuation) : MachineState :=
  match matchPattern parameter argument with
  | none => .halted (.error .matchFailure)
  | some bindings => .evaluate body (extend captured bindings) continuation

def applyClosure (program : Program) (function argument : Value)
    (continuation : Continuation) : Except InternalError MachineState :=
  match function with
  | .closure (.lambda reference) captured =>
      match program.instruction? reference with
      | some (.lambda parameter body) => .ok (enterBody parameter argument body captured continuation)
      | _ => .error (.nonFunction function)
  | .closure (.recursive group slot) captured => do
      let some (.letRecursive definitions _) := program.instruction? group
        | throw (.invalidRecursiveGroup group slot)
      let some reference := definitions[slot]? | throw (.invalidRecursiveGroup group slot)
      let some (.lambda parameter body) := program.instruction? reference
        | throw (.invalidRecursiveGroup group slot)
      pure (enterBody parameter argument body
        (recursiveEnvironment group definitions captured) continuation)
  | _ => .error (.nonFunction function)

def evaluateInstruction (program : Program) (reference : Code) (environment : Environment)
    (continuation : Continuation) : Except InternalError MachineState := do
  let some instruction := program.instruction? reference | throw (.missingCode reference)
  match instruction with
  | .literal value => pure (.returned (.literal value) continuation)
  | .variable index =>
      match environment[index]? with
      | some value => pure (.returned value continuation)
      | none => throw (.unboundVariable index)
  | .lambda _ _ => pure (.returned (.closure (.lambda reference) environment) continuation)
  | .apply function argument =>
      pure (.evaluate argument environment (.argument function environment :: continuation))
  | .letValue pattern value body =>
      pure (.evaluate value environment (.letValue pattern body environment :: continuation))
  | .letRecursive definitions body =>
      pure (.evaluate body (recursiveEnvironment reference definitions environment) continuation)
  | .branch condition yes no =>
      pure (.evaluate condition environment (.branch yes no environment :: continuation))
  | .andThen left right => pure (.evaluate left environment (.andThen right environment :: continuation))
  | .orElse left right => pure (.evaluate left environment (.orElse right environment :: continuation))
  | .tuple fields => startArguments program .tuple fields environment continuation
  | .variant typeId constructor fields =>
      startArguments program (.variant typeId constructor) fields environment continuation
  | .primitive operator arguments =>
      startArguments program (.primitive operator) arguments environment continuation
  | .cons head tail => pure (.evaluate tail environment (.consTail head environment :: continuation))
  | .matchValue scrutinee clauses =>
      pure (.evaluate scrutinee environment (.matchValue clauses environment :: continuation))

def returnValue (program : Program) (value : Value) : Continuation → Except InternalError MachineState
  | [] => .ok (.halted (.ok value))
  | frame :: continuation => do
      match frame with
      | .argument function environment =>
          pure (.evaluate function environment (.function value :: continuation))
      | .function argument => applyClosure program value argument continuation
      | .letValue pattern body environment => pure (enterBody pattern value body environment continuation)
      | .branch yes no environment =>
          match value with
          | .literal (.boolean condition) => pure (.evaluate (if condition then yes else no) environment continuation)
          | _ => throw (.nonBoolean value)
      | .andThen right environment =>
          match value with
          | .literal (.boolean false) => pure (.returned value continuation)
          | .literal (.boolean true) => pure (.evaluate right environment (.booleanResult :: continuation))
          | _ => throw (.nonBoolean value)
      | .orElse right environment =>
          match value with
          | .literal (.boolean true) => pure (.returned value continuation)
          | .literal (.boolean false) => pure (.evaluate right environment (.booleanResult :: continuation))
          | _ => throw (.nonBoolean value)
      | .booleanResult =>
          match value with
          | .literal (.boolean _) => pure (.returned value continuation)
          | _ => throw (.nonBoolean value)
      | .consTail head environment => pure (.evaluate head environment (.consHead value :: continuation))
      | .consHead tail => pure (.returned (.cons value tail) continuation)
      | .gather kind [] _ suffix => finishBuild program kind (value :: suffix) continuation
      | .gather kind (next :: rest) environment suffix =>
          pure (.evaluate next environment (.gather kind rest environment (value :: suffix) :: continuation))
      | .matchValue clauses environment =>
          match selectClause clauses value with
          | none => pure (.halted (.error .matchFailure))
          | some (body, bindings) => pure (.evaluate body (extend environment bindings) continuation)

def machineStep (program : Program) : MachineState → Except InternalError (Option MachineState)
  | .halted _ => .ok none
  | .evaluate reference environment continuation =>
      (evaluateInstruction program reference environment continuation).map some
  | .returned value continuation => (returnValue program value continuation).map some

theorem machineStep_stops_iff (program : Program) (state : MachineState) :
    machineStep program state = .ok none ↔ ∃ result, state = .halted result := by
  cases state with
  | halted result => simp [machineStep]
  | evaluate reference environment continuation =>
      cases result : evaluateInstruction program reference environment continuation <;>
        simp [machineStep, result, Except.map]
  | returned value continuation =>
      cases result : returnValue program value continuation <;> simp [machineStep, result, Except.map]

inductive RunResult where
  | complete (result : Result)
  | pending (state : MachineState)
  | invalid (error : InternalError)
  deriving Repr, BEq

def run (program : Program) : Nat → MachineState → RunResult
  | _, .halted result => .complete result
  | 0, state => .pending state
  | budget + 1, state => match machineStep program state with
      | .error error => .invalid error
      | .ok none => .invalid .unexpectedStop
      | .ok (some next) => run program budget next

def begin (program : Program) : MachineState := .evaluate program.entry [] []

def resume (program : Program) (budget : Nat) : RunResult → RunResult
  | .pending state => run program budget state
  | result => result

theorem run_resume (program : Program) (first second : Nat) (state : MachineState) :
    resume program second (run program first state) = run program (first + second) state := by
  induction first generalizing state with
  | zero => cases state <;> simp [run, resume]
  | succ first ih =>
      cases state with
      | halted result => simp [run, resume]
      | evaluate reference environment continuation =>
          cases stepping : machineStep program (.evaluate reference environment continuation) with
          | error error => simp [run, stepping, resume, Nat.succ_add]
          | ok next => cases next with
              | none => simp [run, stepping, resume, Nat.succ_add]
              | some next => simpa [run, stepping, Nat.succ_add] using ih next
      | returned value continuation =>
          cases stepping : machineStep program (.returned value continuation) with
          | error error => simp [run, stepping, resume, Nat.succ_add]
          | ok next => cases next with
              | none => simp [run, stepping, resume, Nat.succ_add]
              | some next => simpa [run, stepping, Nat.succ_add] using ih next

end Mettapedia.Languages.OCaml
