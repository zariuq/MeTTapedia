import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageExecution
import Mettapedia.Tools.KernelReflexivity

/-! Producer counts, bag multiplicity, logical predecessor support and live refusal. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageExecution.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics NamedSpaces CTLPreimageSource

def names : Names := ⟨"space", "input", "output", "x", "y", by decide⟩
def program : Program := {equations := [], declarations := []}
def satRows : List Atom := [satisfaction "sat" "a" 1, satisfaction "sat" "a" 2]
def graphRows : List Atom := [reverseEdge "rt" (0, 1), reverseEdge "rt" (0, 2)]
def before : Effects.State := ((Store.new satRows []).allocate graphRows).2
def after : Effects.State := {before with core := satRows ++ [satisfaction "sat" "f" 0, satisfaction "sat" "f" 0]}
def deduplicated : Effects.State := {before with core := satRows ++ [satisfaction "sat" "f" 0]}
def caller : Subst := [(names.space, Effects.handleValue .self), (names.input, .symbol "a"), (names.output, .symbol "f")]

theorem two_producers_remain_two_insertions :
    execute "sat" "rt" names .self (.privateSpace 0) caller before = some (after, [Effects.boolean true, Effects.boolean true]) := by
  kernel_reflexivity

theorem actual_source_returns_two :
    Eval.PureReturns program caller before (source "sat" "rt" names .self (.privateSpace 0)) after (.grounded (.int 2)) :=
  execute_source program "sat" "rt" names .self (.privateSpace 0) caller before after _ two_producers_remain_two_insertions

theorem logical_predecessor_support_is_singleton :
    {state | state ∈ produced [(0, 1), (0, 2)] [1, 2]} = ({0} : Set Nat) := by
  ext state
  simp [produced, predecessors]

theorem same_support_does_not_preserve_the_bag :
    after.core.toFinset = deduplicated.core.toFinset ∧ after.core.length ≠ deduplicated.core.length := by decide +kernel

theorem bag_count_is_not_logical_set_cardinality :
    (produced [(0, 1), (0, 2)] [1, 2]).length = 2 ∧
      (produced [(0, 1), (0, 2)] [1, 2]).toFinset.card = 1 := by decide +kernel

theorem invalid_source_state_cannot_be_silently_clipped :
    ({state | state ∈ produced [(7, 1)] [1]} : Set Nat) ≠
      ({state | state < 2} ∩ Mettapedia.Logic.CTLFixedPoints.pre
        (fun prior next => (prior, next) ∈ ([(7, 1)] : List (Nat × Nat))) {state | state = 1}) := by
  intro same
  have member : 7 ∈ ({state | state ∈ produced [(7, 1)] [1]} : Set Nat) := by decide
  rw [same] at member
  have bound : (7 : Nat) < 2 := member.1
  omega

theorem parallel_edge_occurrences_survive : produced [(0, 1), (0, 1)] [1] = [0, 0] := by decide +kernel

theorem ordered_outer_targets_are_not_reordered :
    produced [(0, 1), (3, 2)] [1, 2] = [0, 3] ∧ produced [(0, 1), (3, 2)] [2, 1] = [3, 0] := by decide +kernel

theorem missing_graph_is_not_absence :
    execute "sat" "rt" names .self (.privateSpace 0) caller (Store.new satRows []) = none := by kernel_reflexivity

theorem relevant_open_reverse_edge_refuses :
    execute "sat" "rt" names .self (.privateSpace 0) caller
      ((Store.new satRows []).allocate [.expression [.symbol "rt", .var "stored", .grounded (.int 0)]]).2 = none := by
  kernel_reflexivity

theorem uncaptured_output_label_refuses :
    execute "sat" "rt" names .self (.privateSpace 0) [(names.space, Effects.handleValue .self), (names.input, .symbol "a")] before = none := by
  kernel_reflexivity

theorem aliasing_graph_requires_a_separate_stability_proof :
    execute "sat" "rt" names .self .self caller before = none := by kernel_reflexivity

theorem writes_keep_the_captured_reverse_graph : after.read (.privateSpace 0) = before.read (.privateSpace 0) := rfl

def plan := region "relational-preimage" program "sat" "rt" names .self (.privateSpace 0) caller

theorem region_keeps_the_bag_and_producer_count :
    plan.attempt before = .committed (PureCallPortfolio.complete after (.grounded (.int 2))) := by kernel_reflexivity

theorem missing_graph_restores_entrance :
    plan.attempt (Store.new satRows []) = .declined (Store.new satRows []) := by kernel_reflexivity

theorem missing_graph_selects_reference :
    plan.execute (Store.new satRows []) =
      PureCallPortfolio.sourceMeaning program caller (source "sat" "rt" names .self (.privateSpace 0)) (Store.new satRows []) :=
  congrFun plan.execute_eq_reference _

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageExecution.Controls
