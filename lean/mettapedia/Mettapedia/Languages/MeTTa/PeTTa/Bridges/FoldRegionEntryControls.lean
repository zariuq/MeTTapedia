import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntry

/-! Controls for operand sequencing, captured fallback and source-visible
I/O/residuals at the host-fold specialization boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntry.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics FoldSourceBoundary
open MeTTaIL.WireKit

inductive View
  | reference
  | handoff (phase : Nat) (core output : List Atom)
  | paused (phase : Nat) (core output : List Atom)
  | faulted (phase : Nat) (core output : List Atom)
  | referenceFold (core items : List Atom) (initial : Atom)
  | completed (core : List Atom) (value : Atom)
  deriving DecidableEq

def outcomeView (phase : Nat) : Eval.Outcome → View
  | .complete after _ _ output => .handoff phase after.core output
  | .exhausted saved => .paused phase saved.state.core saved.output
  | .fault _ saved => .faulted phase saved.state.core saved.output

def view {request : Request} : Result request → View
  | .reference => .reference
  | .handoff (.listOperand outcome) => outcomeView 0 outcome
  | .handoff (.initialOperand _ _ outcome) => outcomeView 1 outcome
  | .referenceFold captured => .referenceFold captured.after.core captured.items captured.initial
  | .completed answer => .completed answer.after.core answer.value

def program : Program := {equations := [], declarations := []}
def before : Effects.State := NamedSpaces.Store.new [number 1, number 2] []
def listSource : Atom := apply "collapse" [apply "get-atoms" [.symbol "&self"]]
def initialSource : Atom := apply "let" [.var "ignored", apply "add-atom" [.symbol "&self", number 9], number 0]
def request : Request := ⟨program, [], .named listSource initialSource "+", before⟩

theorem operand_effect_once_and_old_list_snapshot :
    view (run .completed 100 100 6 request) =
      .completed [number 1, number 2, number 9] (number 3) := by decide +kernel

def effects : Program := {equations := [
  ⟨"emit", [.var "a", .var "x"], apply "println!" [.var "x"]⟩], declarations := []}
def declined : Request := ⟨effects, [], .named listSource initialSource "emit", before⟩

theorem decline_keeps_operand_effect_and_inputs :
    view (run .completed 100 100 6 declined) =
      .referenceFold [number 1, number 2, number 9] [number 1, number 2] (number 0) := by decide +kernel

def initialPrint : Request := ⟨program, [], .named listSource (apply "println!" [number 7]) "+", before⟩

theorem printed_operand_is_a_handoff_not_a_restart :
    view (run .completed 100 100 6 initialPrint) =
      .handoff 1 [number 1, number 2] [number 7] := by decide +kernel

theorem exhausted_first_operand_keeps_its_phase :
    view (run .completed 0 100 6 request) = .paused 0 [number 1, number 2] [] := by decide +kernel

theorem source_page_observer_does_not_execute_operands :
    view (run .sourcePage 100 100 6 request) = .reference := rfl

def overflow : Request :=
  ⟨program, [("list", .expression [number UInt64.size])],
    .inline (.var "list") (number 0) "a" "x" (apply "+" [.var "a", .var "x"]), before⟩

theorem overflow_returns_to_captured_fold_not_original_expression :
    view (run .completed 100 100 6 overflow) =
      .referenceFold [number 1, number 2] [number UInt64.size] (number 0) := by decide +kernel

def sumInline : Request :=
  ⟨program, [], .inline listSource initialSource "a" "x" (apply "+" [.var "a", .var "x"]), before⟩

theorem source_derived_word_fold_preserves_operand_effect :
    view (run .completed 100 100 6 sumInline) =
      .completed [number 1, number 2, number 9] (number 3) := by decide +kernel

theorem whole_source_is_the_requested_host_call :
    request.code.source = apply "foldl-atom" [listSource, initialSource, .symbol "+"] := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntry.Controls
