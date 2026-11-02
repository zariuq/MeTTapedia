import Mettapedia.Languages.MeTTa.PeTTa.CoreExecution

/-!
# Common source operations for original paths and conservative certificates

The two instances are existing execution relations. A certificate embeds in
either; an arbitrary original execution is not promoted to a certificate.
The operation laws permit one source proof to retain both interpretations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SharedSourceExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open Effects (State)

inductive Fragment where
  | original
  | conservative

abbrev PureReturns (fragment : Fragment) (program : Program) (bindings : Subst)
    (before : State) (expression : Atom) (after : State) (value : Atom) : Prop :=
  match fragment with
  | .original => Eval.PureReturns program bindings before expression after value
  | .conservative => BoundCalls.CorePath.PureReturns program bindings before expression after value

theorem from_certificate (fragment : Fragment) {program : Program} {bindings : Subst}
    {before after : State} {expression value : Atom}
    (computed : BoundCalls.CorePath.PureReturns program bindings before expression after value) :
    PureReturns fragment program bindings before expression after value := by
  cases fragment with
  | original => exact computed.original
  | conservative => exact computed

theorem variable_returns (fragment : Fragment) (program : Program) (bindings : Subst)
    (state : State) (name : String) :
    PureReturns fragment program bindings state (.var name) state (applySubst bindings (.var name)) :=
  from_certificate fragment (BoundCalls.CorePath.variable_returns program bindings state name)

theorem symbol_returns (fragment : Fragment) (program : Program) (bindings : Subst)
    (state : State) (name : String) :
    PureReturns fragment program bindings state (.symbol name) state (.symbol name) :=
  from_certificate fragment (BoundCalls.CorePath.symbol_returns program bindings state name)

/-- A data head is not a primitive, so it is not `match` either: it avoids every
special form. -/
private theorem data_head_not_form {program : Program} {head : String}
    (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"]) :
    head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"] := by
  have notMatch : head ≠ "match" := Eval.ne_match_of_not_known (by
    simp only [Bool.or_eq_false_iff] at inert
    exact inert.1.2)
  intro member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member ordinary
  tauto

theorem unary_constructor_of_returns (fragment : Fragment) (program : Program) (bindings : Subst)
    (before after : State) (head : String) (expression value : Atom)
    (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (computed : PureReturns fragment program bindings before expression after value) :
    PureReturns fragment program bindings before (.expression [.symbol head, expression]) after
      (.expression [.symbol head, value]) := by
  cases fragment with
  | original => exact Eval.unary_constructor_of_returns program bindings before after head expression value inert ordinary computed
  | conservative =>
      exact BoundCalls.CorePath.unary_constructor_of_returns program bindings before after head expression value
        inert (data_head_not_form inert ordinary) computed

theorem constructor_return (fragment : Fragment) (program : Program) (bindings : Subst)
    (state : State) (head : String) (expressions values : List Atom)
    (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (computed : List.Forall₂ (fun expression value =>
      PureReturns fragment program bindings state expression state value) expressions values) :
    PureReturns fragment program bindings state (.expression (.symbol head :: expressions)) state
      (.expression (.symbol head :: values)) := by
  have notForm := data_head_not_form inert ordinary
  cases fragment with
  | original => exact PureData.constructor_return program bindings state head expressions values inert notForm computed
  | conservative => exact BoundCalls.CorePath.constructor_return program bindings state head expressions values inert notForm computed

theorem case_returns (fragment : Fragment) (program : Program) (bindings bound : Subst)
    (before middle after : State) (expression value body answer : Atom)
    (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : Eval.readCases rows = some cases)
    (computed : PureReturns fragment program bindings before expression middle value)
    (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body))
    (continued : PureReturns fragment program bound middle body after answer) :
    PureReturns fragment program bindings before
      (.expression [.symbol "case", expression, .expression rows]) after answer := by
  cases fragment with
  | original => exact Eval.case_returns program bindings bound before middle after expression value body answer rows cases decoded computed selected continued
  | conservative => exact BoundCalls.CorePath.case_returns program bindings bound before middle after expression value body answer rows cases decoded computed selected continued

theorem if_returns (fragment : Fragment) (program : Program) (bindings : Subst)
    (before middle after : State) (condition value yes no answer : Atom)
    (computed : PureReturns fragment program bindings before condition middle value)
    (continued : PureReturns fragment program bindings middle
      (if value == Effects.boolean true then yes else no) after answer) :
    PureReturns fragment program bindings before
      (.expression [.symbol "if", condition, yes, no]) after answer := by
  cases fragment with
  | original => exact Eval.if_returns program bindings before middle after condition value yes no answer computed continued
  | conservative => exact BoundCalls.CorePath.if_returns program bindings before middle after condition value yes no answer computed continued

end Mettapedia.Languages.MeTTa.PeTTa.SharedSourceExecution
