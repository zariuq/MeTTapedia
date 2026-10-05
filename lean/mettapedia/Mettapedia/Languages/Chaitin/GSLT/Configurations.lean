import Mettapedia.Languages.Chaitin.GSLT.Data
import Mettapedia.Languages.Chaitin.EvaluationLaws

/-!
# Explicit continuations of the effect-free historical evaluator

These are representations of the existing evaluator's unbounded pure states.
Dynamic environments and pending argument values are retained literally.
Quotation does not evaluate its operand; `eval` reinstalls the clean environment.
The effectful reader, output and sandbox operations are outside this carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT

open Mettapedia.OSLF.MeTTaIL.Syntax PureEvaluation

inductive Continuation where
  | done
  | function (operands : List SExpr) (environment : Environment) (rest : Continuation)
  | conditional (positive negative : SExpr) (environment : Environment) (rest : Continuation)
  | argument (function : SExpr) (reversed remaining : List SExpr)
      (environment : Environment) (rest : Continuation)
deriving DecidableEq

def Continuation.frames : Continuation → List Frame
  | .done => []
  | .function operands environment rest => .function operands environment .unlimited :: rest.frames
  | .conditional positive negative environment rest =>
      .conditional positive negative environment .unlimited :: rest.frames
  | .argument operator reversed remaining environment rest =>
      .argument operator reversed remaining environment .unlimited :: rest.frames

inductive Configuration where
  | eval (expression : SExpr) (environment : Environment) (continuation : Continuation)
  | apply (function : SExpr) (arguments : List SExpr) (environment : Environment)
      (continuation : Continuation)
  | returned (value : SExpr) (continuation : Continuation)
deriving DecidableEq

def Configuration.state : Configuration → State
  | .eval expression environment continuation =>
      { control := .eval expression environment .unlimited, frames := continuation.frames }
  | .apply function arguments environment continuation =>
      { control := .apply function arguments environment .unlimited, frames := continuation.frames }
  | .returned value continuation => { control := .returned value, frames := continuation.frames }

def encodeContinuation : Continuation → Pattern
  | .done => .apply "Done" []
  | .function operands environment rest =>
      .apply "Function" [encodeValues operands, encodeEnvironment environment, encodeContinuation rest]
  | .conditional positive negative environment rest =>
      .apply "Conditional" [encode positive, encode negative,
        encodeEnvironment environment, encodeContinuation rest]
  | .argument function reversed remaining environment rest =>
      .apply "Argument" [encode function, encodeValues reversed, encodeValues remaining,
        encodeEnvironment environment, encodeContinuation rest]

def encodeConfiguration : Configuration → Pattern
  | .eval expression environment continuation =>
      .apply "Eval" [encode expression, encodeEnvironment environment, encodeContinuation continuation]
  | .apply function arguments environment continuation =>
      .apply "Apply" [encode function, encodeValues arguments,
        encodeEnvironment environment, encodeContinuation continuation]
  | .returned value continuation => .apply "Returned" [encode value, encodeContinuation continuation]

def decodeContinuation : Pattern → Option Continuation
  | .apply "Done" [] => some .done
  | .apply "Function" [operands, environment, rest] => do
      let values ← decodeValues operands
      let bindings ← decodeEnvironment environment
      let continuation ← decodeContinuation rest
      pure (.function values bindings continuation)
  | .apply "Conditional" [positive, negative, environment, rest] => do
      let yes ← decode positive
      let no ← decode negative
      let bindings ← decodeEnvironment environment
      let continuation ← decodeContinuation rest
      pure (.conditional yes no bindings continuation)
  | .apply "Argument" [function, reversed, remaining, environment, rest] => do
      let operator ← decode function
      let values ← decodeValues reversed
      let expressions ← decodeValues remaining
      let bindings ← decodeEnvironment environment
      let continuation ← decodeContinuation rest
      pure (.argument operator values expressions bindings continuation)
  | _ => none

def decodeConfiguration : Pattern → Option Configuration
  | .apply "Eval" [expression, environment, continuation] => do
      let value ← decode expression
      let bindings ← decodeEnvironment environment
      let stack ← decodeContinuation continuation
      pure (.eval value bindings stack)
  | .apply "Apply" [function, arguments, environment, continuation] => do
      let value ← decode function
      let values ← decodeValues arguments
      let bindings ← decodeEnvironment environment
      let stack ← decodeContinuation continuation
      pure (.apply value values bindings stack)
  | .apply "Returned" [value, continuation] => do
      let expression ← decode value
      let stack ← decodeContinuation continuation
      pure (.returned expression stack)
  | _ => none

@[simp] theorem decodeContinuation_encodeContinuation (continuation : Continuation) :
    decodeContinuation (encodeContinuation continuation) = some continuation := by
  induction continuation <;> simp [encodeContinuation, decodeContinuation, *]

@[simp] theorem decodeConfiguration_encodeConfiguration (configuration : Configuration) :
    decodeConfiguration (encodeConfiguration configuration) = some configuration := by
  cases configuration <;> simp [encodeConfiguration, decodeConfiguration]

theorem encodeConfiguration_injective : Function.Injective encodeConfiguration := by
  intro first second same
  simpa only [decodeConfiguration_encodeConfiguration, Option.some.injEq] using
    congrArg decodeConfiguration same

def argumentsConfiguration (function : SExpr) (reversed remaining : List SExpr)
    (environment : Environment) (continuation : Continuation) : Configuration :=
  match remaining with
  | [] => .apply function reversed.reverse environment continuation
  | first :: rest => .eval first environment (.argument function reversed rest environment continuation)

/-- Independent control rules, read pointwise against the historical evaluator.
Data operations are shared; no rule calls the evaluator recursively. -/
inductive CoreStep : Configuration → Configuration → Prop where
  | atom {expression environment continuation} (atomic : expression.atom = true) :
      CoreStep (.eval expression environment continuation)
        (.returned (lookup environment expression) continuation)
  | call {head operands environment continuation} :
      CoreStep (.eval (.list (head :: operands)) environment continuation)
        (.eval head environment (.function operands environment continuation))
  | quote {operands environment continuation} :
      CoreStep (.returned (.symbol "'") (.function operands environment continuation))
        (.returned (operands.headD SExpr.nil) continuation)
  | conditional {operands environment continuation} :
      CoreStep (.returned (.symbol "if") (.function operands environment continuation))
        (.eval (operands.headD SExpr.nil) environment
          (.conditional (operands.tail.headD SExpr.nil)
            (operands.tail.tail.headD SExpr.nil) environment continuation))
  | function {function operands environment continuation}
      (notQuote : function ≠ .symbol "'") (notIf : function ≠ .symbol "if") :
      CoreStep (.returned function (.function operands environment continuation))
        (argumentsConfiguration function [] operands environment continuation)
  | branch {value positive negative environment continuation} :
      CoreStep (.returned value (.conditional positive negative environment continuation))
        (.eval (if value.truth then positive else negative) environment continuation)
  | argument {value function reversed remaining environment continuation} :
      CoreStep (.returned value (.argument function reversed remaining environment continuation))
        (argumentsConfiguration function (value :: reversed) remaining environment continuation)
  | primitive {function arguments environment continuation value}
      (computed : purePrimitive function arguments = some value) :
      CoreStep (.apply function arguments environment continuation) (.returned value continuation)
  | eval {arguments environment continuation} :
      CoreStep (.apply (.symbol "eval") arguments environment continuation)
        (.eval (arguments.headD SExpr.nil) cleanEnvironment continuation)
  | lambda {function arguments environment continuation}
      (dispatch : LambdaDispatch function arguments) :
      CoreStep (.apply function arguments environment continuation)
        (.eval function.caddr (bind function.cadr (.list arguments) environment) continuation)

theorem CoreStep.observed {configuration next : Configuration} (step : CoreStep configuration next) :
    observe configuration.state = .step next.state := by
  cases step with
  | atom atomic =>
      rename_i expression environment continuation
      cases expression with
      | symbol name => rfl
      | number number => rfl
      | list values => cases values <;> simp_all [SExpr.atom, Configuration.state, observe]
  | call => rfl
  | quote => simp [Configuration.state, Continuation.frames, observe]
  | conditional => simp [Configuration.state, Continuation.frames, observe]
  | function notQuote notIf =>
      rename_i function operands environment continuation
      cases operands <;>
        simp [Configuration.state, Continuation.frames, argumentsConfiguration,
          observe, notQuote, notIf, evaluateArguments]
  | branch => rfl
  | argument =>
      rename_i value function reversed remaining environment continuation
      cases remaining <;> rfl
  | primitive computed =>
      rename_i function arguments environment continuation value
      -- Dispatch can be checked without evaluating any recursive body.
      cases function with
      | number number => simp [purePrimitive] at computed
      | list values => simp [purePrimitive] at computed
      | symbol name =>
          by_cases readBit : name = "read-bit"
          · subst name; simp [purePrimitive] at computed
          by_cases readExp : name = "read-exp"
          · subst name; simp [purePrimitive] at computed
          by_cases display : name = "display"
          · subst name; simp [purePrimitive] at computed
          by_cases debug : name = "debug"
          · subst name; simp [purePrimitive] at computed
          simp [Configuration.state, observe, readBit, readExp, display, debug, computed]
  | eval => simp [Configuration.state, observe, purePrimitive, Depth.decrease]
  | lambda dispatch =>
      rcases dispatch with ⟨readBit, readExp, display, debug, notEval, notTry, primitive⟩
      rename_i function arguments environment continuation
      cases function <;>
        simp_all [Configuration.state, observe, Depth.decrease]

def CorePath : Configuration → Configuration → Prop := Relation.ReflTransGen CoreStep

theorem CorePath.observed {configuration next : Configuration} (path : CorePath configuration next) :
    InternalSteps configuration.state next.state := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact ih.tail step.observed

theorem returned_observe (value : SExpr) :
    observe (Configuration.returned value .done).state =
      .halt ⟨.success value, [], []⟩ := rfl

end Mettapedia.Languages.Chaitin.GSLT
