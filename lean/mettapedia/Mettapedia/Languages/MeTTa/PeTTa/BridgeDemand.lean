import Mettapedia.Languages.MeTTa.PeTTa.BridgeForms

/-! Authored bridge calls with mixed raw and evaluated arguments follow
the target evaluator's declared argument demand at every position.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BridgeKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval

inductive ArgumentsReturn (program : Program) (caller : Subst) (head : String) :
    Nat → State → List Atom → State → List Atom → Prop where
  | nil (index : Nat) (state : State) : ArgumentsReturn program caller head index state [] state []
  | raw {index : Nat} {before after : State} {argument : Atom} {rest values : List Atom}
      (demand : argumentIsRaw program head index = true)
      (continued : ArgumentsReturn program caller head (index + 1) before rest after values) :
      ArgumentsReturn program caller head index before (argument :: rest) after (applySubst caller argument :: values)
  | evaluated {index : Nat} {before middle after : State} {argument value : Atom} {rest values : List Atom}
      (demand : argumentIsRaw program head index = false)
      (computed : PureReturns program caller before argument middle value)
      (continued : ArgumentsReturn program caller head (index + 1) middle rest after values) :
      ArgumentsReturn program caller head index before (argument :: rest) after (value :: values)

theorem ArgumentsReturn.length {program : Program} {caller : Subst} {head : String} {index : Nat}
    {before after : State} {arguments values : List Atom}
    (returned : ArgumentsReturn program caller head index before arguments after values) : arguments.length = values.length := by
  induction returned <;> simp_all

theorem ArgumentsReturn.continue {program : Program} {caller : Subst} {head : String} {index : Nat}
    {before middle : State} {arguments values : List Atom}
    (returned : ArgumentsReturn program caller head index before arguments middle values)
    (after : State) (answer : Atom) (accumulated : List Atom)
    (computed : (theory program).MultiStep
      {state := middle, control := .arguments caller (.function head) [] (accumulated ++ values) (index + arguments.length)}
      (finished after [answer] [] [])) :
    (theory program).MultiStep
      {state := before, control := .arguments caller (.function head) arguments accumulated index}
      (finished after [answer] [] []) := by
  induction returned generalizing accumulated with
  | nil => simpa using computed
  | @raw index before middle argument rest values demand continued ih =>
      apply raw_argument_answers program caller before after head argument rest accumulated index [answer] demand
      apply ih (accumulated ++ [applySubst caller argument])
      simpa only [List.length_cons, List.append_assoc, List.singleton_append, Nat.add_assoc, Nat.add_comm 1] using computed
  | @evaluated index before next middle argument value rest values demand first continued ih =>
      apply evaluated_argument_returns program caller before next after (.function head) argument value answer rest accumulated index demand first
      apply ih (accumulated ++ [value])
      simpa only [List.length_cons, List.append_assoc, List.singleton_append, Nat.add_assoc, Nat.add_comm 1] using computed

theorem authored_demand_call_returns (program : Program) (caller callee : Subst) (before middle after : State)
    (head : String) (arguments values : List Atom) (body answer : Atom)
    (notIO : ioHead head = false) (notNative : StdLib.known head = false)
    (registered : program.equations.any (·.head == head) = true)
    (ordinary : head ∉ specialForms)
    (argumentsReturned : ArgumentsReturn program caller head 0 before arguments middle values)
    (selected : clauses program head values = [.evaluate callee body])
    (computed : PureReturns program callee middle body after answer) :
    PureReturns program caller before (.expression (.symbol head :: arguments)) after answer := by
  apply call_returns program caller before after head arguments answer
    (by simp only [notIO, notNative, registered, Bool.false_or]) _ ordinary
  apply argumentsReturned.continue after answer []
  simpa only [List.nil_append, Nat.zero_add] using
    authored_function_arguments_return program caller callee middle after head values arguments.length body answer
      notIO notNative selected computed

#print axioms ArgumentsReturn.continue
#print axioms authored_demand_call_returns

end Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
