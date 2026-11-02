import Mettapedia.Languages.MeTTa.PeTTa.CoreExecution

/-!
# Captured data construction in source execution

An inert source constructor evaluates its variable leaves once and collects
their values in order. Executable heads inside a captured value stay data.
This is a law of the existing configuration evaluator, not another evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SourceData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open Effects (State)

inductive Tree (program : Program) : Atom → Prop where
  | capture (name : String) : Tree program (.var name)
  | grounded (value) : Tree program (.grounded value)
  | symbol (name : String) : Tree program (.symbol name)
  | constructor (head : String) (arguments : List Atom)
      (inert : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
      (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
      (children : ∀ argument ∈ arguments, Tree program argument) :
      Tree program (.expression (.symbol head :: arguments))

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

private theorem mapped_arguments (program : Program) (bindings : Subst) (state : State)
    (arguments : List Atom)
    (computed : ∀ argument ∈ arguments, BoundCalls.CorePath.PureReturns program bindings state
      argument state (applySubst bindings argument)) :
    List.Forall₂ (fun expression value => BoundCalls.CorePath.PureReturns program bindings state
      expression state value) arguments (arguments.map (applySubst bindings)) := by
  induction arguments with
  | nil => exact .nil
  | cons argument rest ih =>
      exact .cons (computed argument List.mem_cons_self)
        (ih (fun item member => computed item (List.mem_cons_of_mem _ member)))

theorem returns (program : Program) (bindings : Subst) (state : State) (expression : Atom)
    (tree : Tree program expression) :
    BoundCalls.CorePath.PureReturns program bindings state expression state (applySubst bindings expression) := by
  induction tree with
  | capture name => exact BoundCalls.CorePath.variable_returns program bindings state name
  | grounded value => exact BoundCalls.CorePath.grounded_returns program bindings state value
  | symbol name => exact BoundCalls.CorePath.symbol_returns program bindings state name
  | constructor head arguments inert ordinary _ ih =>
      have list_substitution : ∀ items : List Atom,
          applySubst.applySubstList bindings items = items.map (applySubst bindings) := by
        intro items
        induction items with
        | nil => rfl
        | cons argument rest ih => simp only [applySubst.applySubstList, List.map_cons, ih]
      simp only [applySubst, applySubst.applySubstList, list_substitution arguments]
      exact BoundCalls.CorePath.constructor_return program bindings state head arguments
        (arguments.map (applySubst bindings)) inert (data_head_not_form inert ordinary)
        (mapped_arguments program bindings state arguments ih)

/-- Interpreted control cannot be admitted as an inert constructor. -/
theorem interpreted_head_refused (program : Program) (head : String) (arguments : List Atom)
    (interpreted : StdLib.known head = true) :
    ¬ Tree program (.expression (.symbol head :: arguments)) := by
  intro tree
  cases tree with
  | constructor _ _ inert _ _ => simp [interpreted] at inert

end Mettapedia.Languages.MeTTa.PeTTa.SourceData
