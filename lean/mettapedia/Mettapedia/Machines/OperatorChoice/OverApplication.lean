import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Batch arity admission, dynamic currying and qualified forwarding

The two controllers use the same body service. Bodies receive their actual
ordered arguments and return data or a captured callable together with an
ordered effect word and declared work. Batch admission refuses excess
arguments before the body. Dynamic currying runs the first call and applies
its callable result to the suffix; on a noncallable result, the prefix effects
remain visible even though the whole call fails.

Fuel bounds callable chaining, not a body's internal computation. Paused
results retain the actual next callable and arguments. This is an arity-control
component, not a full evaluator or a native timing model. Arguments are already
delivered; early refusal concerns body effects, not prior argument effects.
Qualification of forwarding, overload choice and the current program view
remains explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.OverApplication

variable {Fn Arg Value Effect : Type}

inductive Return (Fn Arg Value : Type) where
  | data (value : Value)
  | closure (target : Fn) (bound : List Arg)
  deriving DecidableEq, Repr

structure Execution (Fn Arg Value Effect : Type) where
  value : Return Fn Arg Value
  effects : List Effect
  work : Nat
  deriving DecidableEq, Repr

structure Body (Fn Arg Value Effect : Type) where
  arity : Nat
  run : List Arg → Execution Fn Arg Value Effect

abbrev Program (Fn Arg Value Effect : Type) := Fn → Option (Body Fn Arg Value Effect)

inductive Fault (Fn : Type) where
  | unknown (name : Fn)
  | over (name : Fn) (expected supplied : Nat)
  deriving DecidableEq, Repr

inductive Status (Fn Arg Value : Type) where
  | done (value : Return Fn Arg Value)
  | failed (fault : Fault Fn)
  | paused (next : Fn) (arguments : List Arg)
  deriving DecidableEq, Repr

structure Report (Fn Arg Value Effect : Type) where
  status : Status Fn Arg Value
  effects : List Effect
  work : Nat
  deriving DecidableEq, Repr

def attachPrefix (effects : List Effect) (work : Nat)
    (report : Report Fn Arg Value Effect) : Report Fn Arg Value Effect :=
  ⟨report.status, effects ++ report.effects, work + report.work⟩

def completed (execution : Execution Fn Arg Value Effect) : Report Fn Arg Value Effect :=
  ⟨.done execution.value, execution.effects, execution.work⟩

def batch (program : Program Fn Arg Value Effect) (name : Fn) (arguments : List Arg) :
    Report Fn Arg Value Effect :=
  match program name with
  | none => ⟨.failed (.unknown name), [], 0⟩
  | some body =>
      if arguments.length < body.arity then ⟨.done (.closure name arguments), [], 0⟩
      else if arguments.length = body.arity then completed (body.run arguments)
      else ⟨.failed (.over name body.arity arguments.length), [], 0⟩

def curried (program : Program Fn Arg Value Effect) : Nat → Fn → List Arg → Report Fn Arg Value Effect
  | 0, name, arguments => ⟨.paused name arguments, [], 0⟩
  | fuel + 1, name, arguments =>
      match program name with
      | none => ⟨.failed (.unknown name), [], 0⟩
      | some body =>
          if arguments.length < body.arity then ⟨.done (.closure name arguments), [], 0⟩
          else
            let execution := body.run (arguments.take body.arity)
            let rest := arguments.drop body.arity
            if rest.isEmpty then completed execution
            else match execution.value with
              | .data _ => ⟨.failed (.over name body.arity arguments.length),
                  execution.effects, execution.work⟩
              | .closure target bound => attachPrefix execution.effects execution.work
                  (curried program fuel target (bound ++ rest))

theorem under_application_agrees (program : Program Fn Arg Value Effect) (name : Fn)
    (body : Body Fn Arg Value Effect) (found : program name = some body)
    (arguments : List Arg) (short : arguments.length < body.arity) (fuel : Nat) :
    curried program (fuel + 1) name arguments = batch program name arguments := by
  simp [curried, batch, found, short]

theorem exact_application_agrees (program : Program Fn Arg Value Effect) (name : Fn)
    (body : Body Fn Arg Value Effect) (found : program name = some body)
    (arguments : List Arg) (exactArity : arguments.length = body.arity) (fuel : Nat) :
    curried program (fuel + 1) name arguments = batch program name arguments := by
  have takeAll : arguments.take body.arity = arguments := List.take_of_length_le (by omega)
  have dropAll : arguments.drop body.arity = [] := List.drop_eq_nil_of_le (by omega)
  simp [curried, batch, found, exactArity, takeAll, dropAll]

theorem batch_over_runs_no_body (program : Program Fn Arg Value Effect) (name : Fn)
    (body : Body Fn Arg Value Effect) (found : program name = some body)
    (arguments : List Arg) (excess : body.arity < arguments.length) :
    batch program name arguments = ⟨.failed (.over name body.arity arguments.length), [], 0⟩ := by
  have notShort : ¬ arguments.length < body.arity := by omega
  have notEqual : arguments.length ≠ body.arity := by omega
  simp [batch, found, notShort, notEqual]

theorem curried_over_data_retains_effects (program : Program Fn Arg Value Effect) (name : Fn)
    (body : Body Fn Arg Value Effect) (found : program name = some body)
    (arguments : List Arg) (excess : body.arity < arguments.length) (value : Value)
    (noncallable : (body.run (arguments.take body.arity)).value = .data value) (fuel : Nat) :
    curried program (fuel + 1) name arguments =
      ⟨.failed (.over name body.arity arguments.length),
        (body.run (arguments.take body.arity)).effects,
        (body.run (arguments.take body.arity)).work⟩ := by
  have notShort : ¬ arguments.length < body.arity := by omega
  have remaining : (arguments.drop body.arity).isEmpty = false := by
    cases rest : arguments.drop body.arity with
    | nil =>
        have bound := List.drop_eq_nil_iff.mp rest
        omega
    | cons first later => rfl
  simp [curried, found, notShort, remaining, noncallable]

/-- A forwarding certificate covers the actual body and current program.
The target invocation receives the captured prefix followed by the suffix;
already paid logical work is retained even if the native body can be fused. -/
theorem certified_forwarding (program : Program Fn Arg Value Effect) (name target : Fn)
    (body : Body Fn Arg Value Effect) (found : program name = some body)
    (arguments bound : List Arg) (excess : body.arity < arguments.length)
    (work : Nat) (forward : body.run (arguments.take body.arity) = ⟨.closure target bound, [], work⟩)
    (fuel : Nat) :
    curried program (fuel + 1) name arguments =
      attachPrefix [] work (curried program fuel target (bound ++ arguments.drop body.arity)) := by
  have notShort : ¬ arguments.length < body.arity := by omega
  have remaining : (arguments.drop body.arity).isEmpty = false := by
    cases rest : arguments.drop body.arity with
    | nil =>
        have bound := List.drop_eq_nil_iff.mp rest
        omega
    | cons first later => rfl
  simp [curried, found, notShort, remaining, forward]

namespace Controls

def effectful : Program Nat Nat Nat String
  | 0 => some ⟨1, fun arguments => ⟨.data arguments.sum, ["touch"], 5⟩⟩
  | _ => none

theorem failure_before_effects_and_dynamic_currying_disagree :
    batch effectful 0 [3, 4] = ⟨.failed (.over 0 1 2), [], 0⟩ ∧
      curried effectful 1 0 [3, 4] = ⟨.failed (.over 0 1 2), ["touch"], 5⟩ := by decide

def pureBody : Program Nat Nat Nat String
  | 0 => some ⟨1, fun arguments => ⟨.data arguments.sum, [], 5⟩⟩
  | _ => none

theorem ignoring_effects_does_not_erase_the_extra_work :
    (batch pureBody 0 [3, 4]).status = (curried pureBody 1 0 [3, 4]).status ∧
      (batch pureBody 0 [3, 4]).effects = (curried pureBody 1 0 [3, 4]).effects ∧
      (batch pureBody 0 [3, 4]).work = 0 ∧ (curried pureBody 1 0 [3, 4]).work = 5 := by decide

def forwarding : Program Nat Nat Nat String
  | 0 => some ⟨1, fun arguments => ⟨.closure 1 arguments, [], 1⟩⟩
  | 1 => some ⟨2, fun arguments => ⟨.data arguments.sum, ["sum"], 2⟩⟩
  | _ => none

theorem currying_can_succeed_where_batch_refuses :
    batch forwarding 0 [3, 4] = ⟨.failed (.over 0 1 2), [], 0⟩ ∧
      curried forwarding 2 0 [3, 4] = ⟨.done (.data 7), ["sum"], 3⟩ := by decide

theorem a_pause_retains_the_actual_forwarded_call :
    curried forwarding 1 0 [3, 4] = ⟨.paused 1 [3, 4], [], 1⟩ := by decide

end Controls

end Mettapedia.Machines.OperatorChoice.OverApplication
