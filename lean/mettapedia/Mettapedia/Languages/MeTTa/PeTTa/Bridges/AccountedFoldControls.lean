import Mettapedia.Languages.MeTTa.PeTTa.Bridges.AccountedFoldEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FoldRegionEntryControls

/-! Complete operand receipts, callback pages and paid fallback controls. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.AccountedFoldControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MeTTaIL.WireKit AccountedFoldEntry

inductive View
  | reference
  | handoff (phase : Nat) (core output : List Atom) (paid : Nat)
  | referenceFold (core items : List Atom) (initial : Atom) (listDebit initialDebit : Nat)
  | active
  | completed (core : List Atom) (value : Atom) (sourceDebit hostDebit : Nat)
  deriving DecidableEq

def outcomeView (phase paid : Nat) : Eval.Outcome → View
  | .complete world _ _ output => .handoff phase world.core output paid
  | .exhausted current | .fault _ current => .handoff phase current.state.core current.output paid

def view {request : FoldSourceBoundary.Request} : Result request → View
  | .reference => .reference
  | .handoff (.listOperand outcome) paid => outcomeView 0 paid outcome
  | .handoff (.initialOperand _ _ outcome) paid => outcomeView 1 paid outcome
  | .referenceFold captured =>
      .referenceFold captured.values.after.core captured.values.items captured.values.initial
        captured.listDebit captured.initialDebit
  | .running session =>
      let after := session.advance 100
      match after.execution.execution.current.phase with
      | .done world value => .completed world.core value after.sourceDebit after.execution.execution.current.hostDebit
      | _ => .active

theorem operand_mutation_and_source_work_survive_callback_pages :
    view (enter 100 100 6 FoldRegionEntry.Controls.request) =
      .completed [number 1, number 2, number 9] (number 3) 57 5 := by decide +kernel

theorem callback_refusal_keeps_both_operands_and_both_debits :
    view (enter 100 100 6 FoldRegionEntry.Controls.declined) =
      .referenceFold [number 1, number 2, number 9] [number 1, number 2] (number 0) 10 19 := by decide +kernel

theorem printed_operand_has_a_paid_handoff :
    view (enter 100 100 6 FoldRegionEntry.Controls.initialPrint) =
      .handoff 1 [number 1, number 2] [number 7] 18 := by decide +kernel

theorem zero_first_budget_retains_its_unexecuted_receiver :
    view (enter 0 100 6 FoldRegionEntry.Controls.request) =
      .handoff 0 [number 1, number 2] [] 0 := by decide +kernel

theorem zero_second_budget_does_not_erase_first_operand_work :
    view (enter 100 0 6 FoldRegionEntry.Controls.request) =
      .handoff 1 [number 1, number 2] [] 10 := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.AccountedFoldControls
