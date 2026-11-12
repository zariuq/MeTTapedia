import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanProgramFormation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnFunction

/-!
# Return admission indexed by the compiler's body-entry policy

An evaluated body may return its input through a recognized continuation.
A held body must itself be the input recipe: an empty computation or a let
return position is still ordinary syntax when held. The mode is read from
the existing head-and-source-arity policy, not inferred from result-guard
absence or from an assumed successful body run.

This is the existing source compiler's profile. Native explicit-function
execution escapes require additional body-entry correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FormedBodyReturnAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open DestinationDataRecipe (Recipe)

inductive Certificate (program : SpaceSemantics.Program) (equation : SpaceSemantics.Equation) (recipe : Atom) : Prop where
  | held (raw : OutputPlan.rawOutput program equation.head equation.arguments.length = true)
      (same : equation.body = recipe) : Certificate program equation recipe
  | evaluated (notRaw : OutputPlan.rawOutput program equation.head equation.arguments.length = false)
      (data : Recipe program recipe) (returns : ScopedReturnSyntax.Returns recipe equation.body) :
      Certificate program equation recipe

def checksClause (program : SpaceSemantics.Program) (index fuel : Nat) (equation : SpaceSemantics.Equation) : Bool :=
  match equation.arguments[index]? with
  | none => false
  | some recipe =>
      if OutputPlan.rawOutput program equation.head equation.arguments.length then equation.body == recipe
      else DestinationDataReturnFunction.checksData program recipe &&
        ScopedReturnSyntax.checksSurfaceReturn recipe fuel equation.body

def checksHead (program : SpaceSemantics.Program) (head : String) (index fuel : Nat) : Bool :=
  program.equations.any (fun equation => equation.head == head) &&
    program.equations.all (fun equation => equation.head != head || checksClause program index fuel equation)

theorem checked_clause (program : SpaceSemantics.Program) (index fuel : Nat) (equation : SpaceSemantics.Equation)
    (checked : checksClause program index fuel equation = true) :
    ∃ recipe, equation.arguments[index]? = some recipe ∧ Certificate program equation recipe := by
  cases formal : equation.arguments[index]? with
  | none => simp [checksClause, formal] at checked
  | some recipe =>
      refine ⟨recipe, rfl, ?_⟩
      cases raw : OutputPlan.rawOutput program equation.head equation.arguments.length with
      | true =>
          apply Certificate.held raw
          simpa only [checksClause, formal, raw, if_true, beq_iff_eq] using checked
      | false =>
          have accepted : DestinationDataReturnFunction.checksData program recipe = true ∧
              ScopedReturnSyntax.checksSurfaceReturn recipe fuel equation.body = true := by
            simpa only [checksClause, formal, raw, Bool.false_eq_true, if_false, Bool.and_eq_true] using checked
          exact .evaluated raw (DestinationDataReturnFunction.checksData_sound program recipe accepted.1)
            (ScopedReturnSyntax.checksSurfaceReturn_sound recipe fuel equation.body accepted.2)

theorem checked_row (program : SpaceSemantics.Program) (head : String) (index fuel : Nat)
    (checked : checksHead program head index fuel = true) (equation : SpaceSemantics.Equation)
    (present : equation ∈ program.equations) (named : equation.head = head) :
    ∃ recipe, equation.arguments[index]? = some recipe ∧ Certificate program equation recipe := by
  have accepted := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 equation present
  simp only [named, bne_self_eq_false, Bool.false_or] at accepted
  exact checked_clause program index fuel equation accepted

theorem checked_held_payload (program : SpaceSemantics.Program) (index fuel : Nat) (equation : SpaceSemantics.Equation)
    (checked : checksClause program index fuel equation = true)
    (raw : OutputPlan.rawOutput program equation.head equation.arguments.length = true) :
    ∃ recipe, equation.arguments[index]? = some recipe ∧ equation.body = recipe := by
  obtain ⟨recipe, formal, certificate⟩ := checked_clause program index fuel equation checked
  refine ⟨recipe, formal, ?_⟩
  cases certificate with
  | held mode same => exact same
  | evaluated mode data returns => rw [raw] at mode; cases mode

theorem checked_held_row (program : SpaceSemantics.Program) (head : String) (index fuel : Nat)
    (checked : checksHead program head index fuel = true) (equation : SpaceSemantics.Equation)
    (present : equation ∈ program.equations) (named : equation.head = head)
    (raw : OutputPlan.rawOutput program equation.head equation.arguments.length = true) :
    ∃ recipe, equation.arguments[index]? = some recipe ∧ equation.body = recipe := by
  obtain ⟨recipe, formal, certificate⟩ := checked_row program head index fuel checked equation present named
  refine ⟨recipe, formal, ?_⟩
  cases certificate with
  | held mode same => exact same
  | evaluated mode data returns => rw [raw] at mode; cases mode

theorem checked_evaluated_payload (program : SpaceSemantics.Program) (index fuel : Nat) (equation : SpaceSemantics.Equation)
    (checked : checksClause program index fuel equation = true)
    (notRaw : OutputPlan.rawOutput program equation.head equation.arguments.length = false) :
    ∃ recipe, equation.arguments[index]? = some recipe ∧ Recipe program recipe ∧
      ScopedReturnSyntax.Returns recipe equation.body := by
  obtain ⟨recipe, formal, certificate⟩ := checked_clause program index fuel equation checked
  cases certificate with
  | held mode same => rw [notRaw] at mode; cases mode
  | evaluated mode data returns => exact ⟨recipe, formal, data, returns⟩

namespace Controls

private def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private def declaration (range : Atom) : Atom := call ":" [.symbol "f", call "->" [.symbol "Atom", range]]
private def equation (body : Atom) : SpaceSemantics.Equation := ⟨"f", [.var "x"], body⟩
private def held (body : Atom) : SpaceSemantics.Program :=
  {equations := [equation body], declarations := [declaration (.symbol "Atom")]}
private def eager (body : Atom) : SpaceSemantics.Program :=
  {equations := [equation body], declarations := [declaration (.symbol "%Undefined%")]}
private def prefixBody : Atom := call "let" [.var "ignored", call "println!" [.symbol "effect"], .var "x"]

theorem held_leaf_is_admitted : checksHead (held (.var "x")) "f" 0 2 = true := by cbv

theorem held_empty_is_not_an_input_alias : checksHead (held (call "empty" [])) "f" 0 2 = false := by cbv

theorem eager_empty_is_a_valid_no_answer_return_branch : checksHead (eager (call "empty" [])) "f" 0 2 = true := by cbv

theorem held_prefix_cannot_borrow_an_eager_return_certificate : checksHead (held prefixBody) "f" 0 3 = false := by cbv

theorem evaluated_prefix_is_admitted : checksHead (eager prefixBody) "f" 0 3 = true := by cbv

theorem missing_head_is_not_vacuously_admitted : checksHead (held (.var "x")) "missing" 0 2 = false := by cbv

theorem other_arity_does_not_change_evaluated_admission :
    checksHead {eager prefixBody with declarations :=
      (eager prefixBody).declarations ++ [call ":" [.symbol "f", call "->" [.symbol "Atom"]]]} "f" 0 3 = true := by cbv

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FormedBodyReturnAdmission
