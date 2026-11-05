import Mettapedia.Languages.MeTTa.PeTTa.StreamSource
import Mettapedia.Tools.KernelReflexivity

/-! Literal versus dynamic superposition, stable uniqueness, effects and residuals.
The tests use closed values; generative open-variable identities belong to the
separate scoped-unifier profile. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StreamSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces

def number (value : Int) : Atom := .grounded (.int value)
def app (head : String) (args : List Atom) : Atom := .expression (.symbol head :: args)
def quoted (value : Atom) : Atom := app "quote" [value]
def options (items : List Atom) : Atom := app "superpose" [.expression items]
def program : Program := {equations := [⟨"answer-code", [], number 9⟩], declarations := []}
def code : Atom := app "answer-code" []

theorem literal_branches_are_executed : evaluate program 100 Effects.empty (options [code, code]) =
    .complete Effects.empty [number 9, number 9] [] [] := by kernel_reflexivity

theorem captured_list_values_are_not_executed :
    run program 100 {state := Effects.empty, control := .evaluate [("xs", .expression [code, code])] (app "superpose" [.var "xs"])} =
      .complete Effects.empty [code, code] [] [] := by kernel_reflexivity

theorem literal_and_dynamic_are_distinct : [code, code] ≠ [number 9, number 9] := by decide +kernel

theorem unique_does_not_reexecute_returned_code :
    evaluate program 100 Effects.empty (unique (options [quoted code, quoted code])) =
      .complete Effects.empty [code] [] [] := by kernel_reflexivity

def values : List Atom := [number 3, number 1, number 3, number 2, number 1]

theorem stable_first_occurrence_order : evaluate program 100 Effects.empty (unique (options values)) =
    .complete Effects.empty [number 3, number 1, number 2] [] [] := by kernel_reflexivity

theorem dynamic_scalar_fails_without_an_answer : evaluate program 100 Effects.empty (app "superpose" [number 7]) =
    .complete Effects.empty [] [] [] := by kernel_reflexivity

theorem unique_atom_scalar_returns_an_empty_tuple : StdLib.apply Effects.empty "unique-atom" [number 7] =
    .ok (Effects.empty, [.expression []]) := rfl

def markingBody : Atom := app "let" [.var "value", options [number 1, number 1, number 2],
  app "let" [.var "written", app "add-atom" [Effects.handleValue .self, app "seen" [.var "value"]], .var "value"]]
def marked : Effects.State := Store.new [app "seen" [number 1], app "seen" [number 1], app "seen" [number 2]] []

theorem deduplication_keeps_all_producer_effects :
    evaluate program 200 Effects.empty (unique markingBody) = .complete marked [number 1, number 2] [] [] := by kernel_reflexivity

def silentBody : Atom := app "let" [.var "written", app "add-atom" [Effects.handleValue .self, .symbol "mark"], app "empty" []]
def silentlyMarked : Effects.State := Store.new [.symbol "mark"] []

theorem empty_unique_result_can_have_an_effect :
    evaluate program 100 Effects.empty (unique silentBody) = .complete silentlyMarked [] [] [] := by kernel_reflexivity

def printingBody : Atom := app "let" [.var "value", options [number 1, number 1, number 2],
  app "let" [.var "printed", app "println!" [.var "value"], number 7]]

theorem producer_output_is_not_deduplicated :
    run program 200 {state := Effects.empty, control := .evaluate [] (unique printingBody), input := [number 8]} =
      .complete Effects.empty [number 7] [number 8] [number 1, number 1, number 2] := by kernel_reflexivity

def paused : Configuration :=
  {state := Effects.empty, control := .sequence (values.map (.evaluate [])) [], frames := uniqueFrames []}

theorem pause_retains_collection_and_caller : evaluate program 2 Effects.empty (unique (options values)) = .exhausted paused := by
  kernel_reflexivity

theorem resume_returns_each_distinct_value_once : run program 100 paused =
    .complete Effects.empty [number 3, number 1, number 2] [] [] := by kernel_reflexivity

def faultingBody : Atom := app "let" [.var "written", app "add-atom" [Effects.handleValue .self, .symbol "committed"],
  app "+" [.symbol "datum", number 1]]

def faultObservation : Outcome → Option (Effects.Fault × List Atom)
  | .fault reason configuration => some (reason, configuration.state.core)
  | _ => none

theorem fault_keeps_the_published_prefix : faultObservation (evaluate program 100 Effects.empty (unique faultingBody)) =
    some (.invalidArguments "+", [.symbol "committed"]) := by kernel_reflexivity

theorem io_exclusion_accounts_for_macro_dependencies : InputOutput.blocked ["superpose"] "unique" = true := rfl

theorem hidden_helpers_are_part_of_the_source_footprint :
    expressionHeadWithin (fun head => head == "unique") [.symbol "unique", .symbol "body"] = false := rfl

end Mettapedia.Languages.MeTTa.PeTTa.StreamSource.Controls
