import Mettapedia.Languages.Chaitin.Syntax
import Mettapedia.Languages.Chaitin.Reader
import Mettapedia.Computability.StreamingInput
import Mathlib.Data.Nat.Digits.Defs

/-!
# Chaitin's Lisp as a streaming abstract machine

The syntax and primitive names are those of *The Limits of Mathematics*.
The 1997 reference interpreter is the authority for argument evaluation,
dynamic bindings, clean `eval`, and nested `try`.

`Depth` is the language's bound on nested calls and re-evaluations. The
streaming executor's fuel is a separate bound on abstract-machine actions.
An outer read requests a bit; it never tests or catches outer exhaustion.
A `try` installs a private tape whose exhaustion is a language exception.
-/

namespace Mettapedia.Languages.Chaitin

open Mettapedia.Computability.StreamingInput

inductive Depth where
  | unlimited
  | bounded (remaining : Nat)
deriving DecidableEq, Repr

namespace Depth

def decrease : Depth → Option Depth
  | .unlimited => some .unlimited
  | .bounded 0 => none
  | .bounded (remaining + 1) => some (.bounded remaining)

def requested (value : SExpr) : Depth :=
  if value = .symbol "no-time-limit" then .unlimited else .bounded value.numeral

def minimum : Depth → Depth → Depth
  | .unlimited, other | other, .unlimited => other
  | .bounded first, .bounded second => .bounded (min first second)

def strictlyBelow : Depth → Depth → Bool
  | .bounded _, .unlimited => true
  | .bounded first, .bounded second => decide (first < second)
  | .unlimited, _ => false

@[simp] theorem decrease_unlimited : decrease .unlimited = some .unlimited := rfl
@[simp] theorem decrease_zero : decrease (.bounded 0) = none := rfl
@[simp] theorem decrease_succ (remaining : Nat) :
    decrease (.bounded (remaining + 1)) = some (.bounded remaining) := rfl

end Depth

inductive Error where
  | outOfData
  | outOfTime
deriving DecidableEq, Repr

def Error.expression : Error → SExpr
  | .outOfData => .symbol "out-of-data"
  | .outOfTime => .symbol "out-of-time"

inductive InputMode where
  | outer
  | privateTape (tape : SExpr)
deriving DecidableEq, Repr

inductive Frame where
  | function (operands : List SExpr) (environment : Environment) (depth : Depth)
  | conditional (positive negative : SExpr) (environment : Environment) (depth : Depth)
  | argument (function : SExpr) (reversed : List SExpr) (remaining : List SExpr)
      (environment : Environment) (depth : Depth)
  | sandbox (input : InputMode) (reversedOutput : List SExpr) (catchesTime : Bool)
deriving Repr

inductive Control where
  | eval (expression : SExpr) (environment : Environment) (depth : Depth)
  | apply (function : SExpr) (arguments : List SExpr) (environment : Environment) (depth : Depth)
  | returned (value : SExpr)
  | failed (error : Error)
  | readBit
  | reading (record : Reader.RecordState)
deriving Repr

structure State where
  control : Control
  frames : List Frame := []
  input : InputMode := .outer
  reversedOutput : List SExpr := []
  reversedDebug : List SExpr := []
deriving Repr

inductive Result where
  | success (value : SExpr)
  | failure (error : Error)
deriving DecidableEq, Repr

structure Observation where
  result : Result
  output : List SExpr
  debug : List SExpr
deriving DecidableEq, Repr

/-- Most-significant-first binary digits, including the digit zero for zero. -/
def binaryDigits (value : Nat) : SExpr :=
  .list ((if value = 0 then [0] else (Nat.digits 2 value).reverse).map SExpr.number)

/-- Exactly zero is a zero bit; every other element is a one bit. -/
def fromBinaryDigits (value : SExpr) : Nat :=
  value.elements.foldl (fun result bit => 2 * result + if bit = .number 0 then 0 else 1) 0

/-- Pure primitives do not consume a call-depth level. Missing arguments are
`nil`; extra arguments have already been evaluated before dispatch. -/
def purePrimitive (function : SExpr) (arguments : List SExpr) : Option SExpr :=
  let x := arguments.headD SExpr.nil
  let y := arguments.tail.headD SExpr.nil
  match function with
  | .symbol "bits" => some (SExpr.tape (Reader.bits x))
  | .symbol "car" => some x.car
  | .symbol "cdr" => some x.cdr
  | .symbol "cons" => some (SExpr.cons x y)
  | .symbol "size" => some (.number x.render.length)
  | .symbol "length" => some (.number x.elements.length)
  | .symbol "+" => some (.number (x.numeral + y.numeral))
  | .symbol "-" => some (.number (x.numeral - y.numeral))
  | .symbol "*" => some (.number (x.numeral * y.numeral))
  | .symbol "^" => some (.number (x.numeral ^ y.numeral))
  | .symbol "<" => some (SExpr.boolean (decide (x.numeral < y.numeral)))
  | .symbol ">" => some (SExpr.boolean (decide (y.numeral < x.numeral)))
  | .symbol ">=" => some (SExpr.boolean (decide (y.numeral ≤ x.numeral)))
  | .symbol "<=" => some (SExpr.boolean (decide (x.numeral ≤ y.numeral)))
  | .symbol "base10-to-2" => some (binaryDigits x.numeral)
  | .symbol "base2-to-10" => some (.number (fromBinaryDigits x))
  | .symbol "append" => some (SExpr.append x y)
  | .symbol "atom" => some (SExpr.boolean x.atom)
  | .symbol "=" => some (SExpr.boolean (decide (x = y)))
  | _ => none

def evaluateArguments (state : State) (function : SExpr) (reversed remaining : List SExpr)
    (environment : Environment) (depth : Depth) : State :=
  match remaining with
  | [] => { state with control := .apply function reversed.reverse environment depth }
  | first :: rest => { state with
      control := .eval first environment depth
      frames := .argument function reversed rest environment depth :: state.frames }

private def tryResult (result value : SExpr) (output : List SExpr) : SExpr :=
  .list [result, value, .list output.reverse]

/-- Supply a requested bit, either as a value or to the current record reader. -/
def supplyBit (state : State) (bit : Bool) : State :=
  match state.control with
  | .readBit => { state with control := .returned (SExpr.bitValue bit) }
  | .reading record =>
      match Reader.feedBit record bit with
      | .inl next => { state with control := .reading next }
      | .inr expression => { state with control := .returned expression }
  | _ => state

private def requestBit (state : State) : Action State Observation :=
  match state.input with
  | .outer => .read (supplyBit state)
  | .privateTape (.list (first :: rest)) =>
      .step (supplyBit { state with input := .privateTape (.list rest) } first.tapeBit)
  | .privateTape _ => .step { state with control := .failed .outOfData }

/-- One action of the historical evaluator, with the unread outer tape kept
outside the machine state. -/
def observe (state : State) : Action State Observation :=
  match state.control with
  | .eval expression environment depth =>
      match expression with
      | .list (first :: rest) => .step { state with
          control := .eval first environment depth
          frames := .function rest environment depth :: state.frames }
      | _ => .step { state with control := .returned (lookup environment expression) }
  | .returned value =>
      match state.frames with
      | [] => .halt ⟨.success value, state.reversedOutput.reverse, state.reversedDebug.reverse⟩
      | .function operands environment depth :: rest =>
          let resumed := { state with frames := rest }
          if value = .symbol "'" then
            .step { resumed with control := .returned (operands.headD SExpr.nil) }
          else if value = .symbol "if" then
            .step { resumed with
              control := .eval (operands.headD SExpr.nil) environment depth
              frames := .conditional (operands.tail.headD SExpr.nil)
                (operands.tail.tail.headD SExpr.nil) environment depth :: rest }
          else .step (evaluateArguments resumed value [] operands environment depth)
      | .conditional positive negative environment depth :: rest => .step { state with
          control := .eval (if value.truth then positive else negative) environment depth
          frames := rest }
      | .argument function reversed remaining environment depth :: rest =>
          .step (evaluateArguments { state with frames := rest } function (value :: reversed)
            remaining environment depth)
      | .sandbox input output _ :: rest => .step { state with
          control := .returned (tryResult (.symbol "success") value state.reversedOutput)
          frames := rest, input := input, reversedOutput := output }
  | .failed error =>
      match state.frames with
      | [] => .halt ⟨.failure error, state.reversedOutput.reverse, state.reversedDebug.reverse⟩
      | .sandbox input output catchesTime :: rest => .step { state with
          control := if error = .outOfData || catchesTime then
            .returned (tryResult (.symbol "failure") error.expression state.reversedOutput)
            else .failed error
          frames := rest, input := input, reversedOutput := output }
      | _ :: rest => .step { state with frames := rest }
  | .readBit | .reading _ => requestBit state
  | .apply function arguments environment depth =>
      let x := arguments.headD SExpr.nil
      let y := arguments.tail.headD SExpr.nil
      let z := arguments.tail.tail.headD SExpr.nil
      match function with
      | .symbol "read-bit" => .step { state with control := .readBit }
      | .symbol "read-exp" => .step { state with control := .reading Reader.initialRecord }
      | .symbol "display" => .step { state with
          control := .returned x, reversedOutput := x :: state.reversedOutput }
      | .symbol "debug" => .step { state with
          control := .returned x, reversedDebug := x :: state.reversedDebug }
      | _ =>
          match purePrimitive function arguments with
          | some value => .step { state with control := .returned value }
          | none =>
              match depth.decrease with
              | none => .step { state with control := .failed .outOfTime }
              | some nextDepth =>
                  if function = .symbol "eval" then
                    .step { state with control := .eval x cleanEnvironment nextDepth }
                  else if function = .symbol "try" then
                    let requested := Depth.requested x
                    .step { state with
                      control := .eval y cleanEnvironment (requested.minimum nextDepth)
                      frames := .sandbox state.input state.reversedOutput
                        (requested.strictlyBelow nextDepth) :: state.frames
                      input := .privateTape z, reversedOutput := [] }
                  else .step { state with
                    control := .eval function.caddr (bind function.cadr (.list arguments) environment)
                      nextDepth }

def machine : Machine State Observation := ⟨observe⟩

def initial (expression : SExpr) (depth : Depth := .unlimited)
    (environment : Environment := cleanEnvironment) : State :=
  ⟨.eval expression environment depth, [], .outer, [], []⟩

/-- All final observations, including output and debug order and unread input. -/
def Evaluates (expression : SExpr) (input : List Bool) (observation : Observation)
    (rest : List Bool) (depth : Depth := .unlimited)
    (environment : Environment := cleanEnvironment) : Prop :=
  Runs machine (initial expression depth environment) input observation rest

def execute (fuel : Nat) (expression : SExpr) (input : List Bool)
    (depth : Depth := .unlimited) (environment : Environment := cleanEnvironment) :=
  runFuel machine fuel (initial expression depth environment) input

theorem evaluates_iff_execute {expression input observation rest depth environment} :
    Evaluates expression input observation rest depth environment ↔
      ∃ fuel, execute fuel expression input depth environment = some (observation, rest) :=
  runs_iff_fuel

theorem Evaluates.deterministic {expression input first firstRest second secondRest depth environment}
    (firstRun : Evaluates expression input first firstRest depth environment)
    (secondRun : Evaluates expression input second secondRest depth environment) :
    first = second ∧ firstRest = secondRest := Runs.deterministic firstRun secondRun

theorem Evaluates.append {expression input observation rest depth environment}
    (run : Evaluates expression input observation rest depth environment) (suffix : List Bool) :
    Evaluates expression (input ++ suffix) observation (rest ++ suffix) depth environment :=
  Runs.append run suffix

def successfulPrograms (expression : SExpr) : Set (List Bool) :=
  {program | ∃ value output debug,
    Evaluates expression program ⟨.success value, output, debug⟩ []}

/-- Successful exact inputs form a prefix-free domain even when the program
uses private tapes and catches their failures. -/
theorem successfulPrograms_prefix_free (expression : SExpr) {first second : List Bool}
    (firstRun : first ∈ successfulPrograms expression)
    (secondRun : second ∈ successfulPrograms expression) (isPrefix : first <+: second) :
    first = second := by
  obtain ⟨firstValue, firstOutput, firstDebug, firstRun⟩ := firstRun
  obtain ⟨secondValue, secondOutput, secondDebug, secondRun⟩ := secondRun
  exact haltingPrograms_prefix_free machine (initial expression)
    ⟨_, firstRun⟩ ⟨_, secondRun⟩ isPrefix

end Mettapedia.Languages.Chaitin
