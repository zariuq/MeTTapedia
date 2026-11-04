import Mettapedia.Logic.ConstraintTypes
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Runtime predicate contracts for PeTTa calls

This adapter uses the existing source-atom carrier. Saturated direct,
variable-headed and completed partial calls resolve before selecting argument
evaluation modes. Incomplete-application values and general arity selection
remain a separate evaluator interface.
Captured values are not evaluated again. The evaluator, equation worker and
membership environment remain parameters: this is a call protocol specification,
not a proof of the Prolog translator or the complete PeTTa evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping

open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive ArgumentMode where
  | evaluate
  | hold
  deriving DecidableEq, Repr

/-- A literal Atom domain requests syntax before evaluation. Other membership
predicates and mode policies are supplied separately by the declaration layer. -/
def argumentMode : Atom → ArgumentMode
  | .symbol "Atom" => .hold
  | _ => .evaluate

structure FunctionKey where
  name : String
  arity : Nat
  deriving DecidableEq, Repr

inductive Argument where
  | syntax (term : Atom)
  | value (term : Atom)
  deriving Repr

structure Call where
  function : FunctionKey
  arguments : List Argument
  deriving Repr

inductive Request where
  | direct (function : FunctionKey) (arguments : List Argument)
  | indirect (variableName : String) (arguments : List Argument)
  | partialApply (function : FunctionKey) (captured supplied : List Argument)

/-- A head is classified as callable or as a value. An unbound source variable
also remains a source variable; it does not create an unresolved-function fault. -/
abbrev HeadEnvironment := String → Option (FunctionKey ⊕ Atom)

inductive Resolved where
  | call (application : Call)
  | data (head : Atom) (arguments : List Argument)

def resolve (environment : HeadEnvironment) : Request → Resolved
  | .direct f args => .call ⟨f, args⟩
  | .indirect variableName args => match environment variableName with
      | some (.inl f) => .call ⟨f, args⟩
      | some (.inr head) => .data head args
      | none => .data (.var variableName) args
  | .partialApply f captured supplied => .call ⟨f, captured ++ supplied⟩

structure Runtime (World Fault Effect : Type) where
  modes : World → FunctionKey → Nat → ArgumentMode
  evaluate : World → Atom → Trace (Atom × World) Fault Effect
  contract : World → FunctionKey → Option (StatefulBoundary.Contract World (List Atom) Atom)
  worker : World → FunctionKey → Boundary.Body World (List Atom) Atom Fault Effect
  wrongArity : FunctionKey → Nat → Fault

namespace Runtime

variable {W F E : Type}

def prepare (runtime : Runtime W F E) (mode : ArgumentMode) (world : W) :
    Argument → Trace (Atom × W) F E
  | .value value => .answer (value, world) .done
  | .syntax term => match mode with
      | .hold => .answer (term, world) .done
      | .evaluate => runtime.evaluate world term

def prepareArguments (runtime : Runtime W F E) (modes : Nat → ArgumentMode)
    (offset : Nat) (world : W) : List Argument → Trace (List Atom × W) F E
  | [] => .answer ([], world) .done
  | arg :: rest => (runtime.prepare (modes offset) world arg).bind fun first =>
      (runtime.prepareArguments modes (offset + 1) first.2 rest).map fun tail =>
        (first.1 :: tail.1, tail.2)

/-- The public entry is selected after argument evaluation, in its resulting
world. That invocation's worker is then retained; later nested calls use their
own worlds. Result checks receive the world returned by the worker. -/
def invoke (runtime : Runtime W F E) (world : W) (call : Call) : Trace (Atom × W) F E :=
  if call.arguments.length = call.function.arity then
    (runtime.prepareArguments (runtime.modes world call.function) 0 world call.arguments).bind
      (fun prepared => StatefulBoundary.install (runtime.contract prepared.2 call.function)
        (runtime.worker prepared.2 call.function) prepared.2 prepared.1)
  else .fault (runtime.wrongArity call.function call.arguments.length)

def run (runtime : Runtime W F E) (environment : W → HeadEnvironment)
    (world : W) (request : Request) : Trace (Atom × W) F E :=
  match resolve (environment world) request with
  | .call call => runtime.invoke world call
  | .data _ args =>
      (runtime.prepareArguments (fun _ => .evaluate) 0 world args).bind fun prepared =>
        match resolve (environment prepared.2) request with
        | .call application => runtime.invoke prepared.2
            ⟨application.function, prepared.1.map Argument.value⟩
        | .data currentHead _ => .answer (.expression (currentHead :: prepared.1), prepared.2) .done

theorem direct_indirect_agree (runtime : Runtime W F E)
    (environment : W → HeadEnvironment) (world : W)
    (variableName : String) (function : FunctionKey) (args : List Argument)
    (resolved : environment world variableName = some (.inl function)) :
    runtime.run environment world (.direct function args) =
      runtime.run environment world (.indirect variableName args) := by
  simp [run, resolve, resolved]

theorem partial_direct_agree (runtime : Runtime W F E)
    (environment : W → HeadEnvironment) (world : W)
    (function : FunctionKey) (captured supplied : List Argument) :
    runtime.run environment world (.partialApply function captured supplied) =
      runtime.run environment world (.direct function (captured ++ supplied)) := rfl

theorem nested_capture_associates (runtime : Runtime W F E)
    (environment : W → HeadEnvironment) (world : W)
    (function : FunctionKey) (first second supplied : List Argument) :
    runtime.run environment world (.partialApply function (first ++ second) supplied) =
      runtime.run environment world (.partialApply function first (second ++ supplied)) := by
  simp [run, resolve, List.append_assoc]

theorem held_syntax_never_evaluated (runtime : Runtime W F E) (world : W) (term : Atom) :
    runtime.prepare .hold world (.syntax term) = .answer (term, world) .done := rfl

theorem captured_value_never_reevaluated (runtime : Runtime W F E)
    (mode : ArgumentMode) (world : W) (term : Atom) :
    runtime.prepare mode world (.value term) = .answer (term, world) .done := rfl

theorem input_fault_is_not_a_type_mismatch (runtime : Runtime W F E)
    (world : W) (term : Atom) (error : F)
    (fault : runtime.evaluate world term = .fault error) :
    runtime.prepare .evaluate world (.syntax term) = .fault error := fault

end Runtime

/-- Return membership is checked against the result world. A body may add a
nominal member before returning it, without any snapshot environment. -/
theorem live_result_membership {W V F E : Type} (member : W → V → Bool)
    (before after : W) (value : V) (admitted : member after value = true) :
    Boundary.call (W := W) (Input := Unit) (Output := V) (Fault := F) (Effect := E)
      ⟨fun _ _ => true, fun world _ result => member world result⟩
      (fun _ _ => .answer (value, after) .done) before () = .answer (value, after) .done := by
  simp [Boundary.call, Trace.filter, admitted]

end Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping
