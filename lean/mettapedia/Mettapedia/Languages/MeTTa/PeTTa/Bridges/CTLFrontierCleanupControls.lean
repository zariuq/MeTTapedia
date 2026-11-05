import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagErasure
import Mettapedia.Tools.KernelReflexivity

/-! The source cleanup used between CTL frontier rounds, with captured
duplicates, other rounds and other formula labels kept distinct. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagErasure.CTLControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics NamedSpaces

def frontier (label : String) (round node : Nat) : Atom :=
  .expression [.symbol "fr", .symbol label, .grounded (.int round), .grounded (.int node)]
def fields : List Atom := [.symbol "fr", .symbol "f", .grounded (.int 0), .var "node"]
def pattern : Atom := .expression fields
def rows : List Atom := [frontier "f" 0 1, frontier "f" 0 1, frontier "f" 0 2,
  frontier "f" 1 3, frontier "g" 0 4]
def remaining : List Atom := [frontier "f" 1 3, frontier "g" 0 4]
def caller : Subst := [("space", Effects.handleValue .self)]
def before : Effects.State := Store.new rows []
def after : Effects.State := Store.new remaining []
def program : Program := {equations := [], declarations := []}

theorem three_captured_removals :
    execute "space" .self pattern fields caller before =
      some (after, List.replicate 3 (Effects.boolean true)) := by kernel_reflexivity

theorem actual_drop_source :
    Eval.PureReturns program caller before (source "space" pattern fields) after (.grounded (.int 3)) :=
  execute_source program "space" .self pattern fields caller before after _ three_captured_removals

theorem repeats_keep_the_captured_count :
    (EffectfulQuerySource.choices caller pattern rows).length = 3 ∧
      ([frontier "f" 0 1, frontier "f" 0 1, frontier "f" 0 2].toFinset.card = 2) := by
  constructor
  · kernel_reflexivity
  · decide +kernel

theorem absent_round_returns_zero :
    execute "space" .self pattern fields caller after = some (after, []) := by kernel_reflexivity

theorem both_other_round_and_other_label_survive :
    after.core = [frontier "f" 1 3, frontier "g" 0 4] := rfl

theorem relevant_open_stored_row_refuses :
    execute "space" .self pattern fields caller (Store.new [pattern] []) = none := by kernel_reflexivity

theorem missing_space_refuses :
    execute "space" (.privateSpace 0) pattern fields
      [("space", Effects.handleValue (.privateSpace 0))] before = none := by kernel_reflexivity

theorem open_removal_payload_refuses :
    execute "space" .self pattern [.symbol "fr", .var "unbound"] caller before = none := by kernel_reflexivity

theorem declaration_removal_requires_another_profile :
    execute "space" .self pattern [.symbol "=", .symbol "f", .symbol "g"] caller before = none := by
  kernel_reflexivity

theorem open_destination_is_checked_even_when_query_head_differs :
    execute "space" .self pattern [.symbol "sat", .var "node"] caller
      (Store.new (rows ++ [.expression [.symbol "sat", .var "stored"]]) []) = none := by
  kernel_reflexivity

def plan := region "frontier-cleanup" program "space" .self pattern fields caller

theorem plan_keeps_producer_count :
    plan.attempt before = .committed (PureCallPortfolio.complete after (.grounded (.int 3))) := by kernel_reflexivity

theorem declined_open_rows_keep_entrance :
    plan.attempt (Store.new [pattern] []) = .declined (Store.new [pattern] []) := by kernel_reflexivity

theorem declined_open_rows_select_reference :
    plan.execute (Store.new [pattern] []) =
      PureCallPortfolio.sourceMeaning program caller (source "space" pattern fields) (Store.new [pattern] []) :=
  congrFun plan.execute_eq_reference _

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagErasure.CTLControls
