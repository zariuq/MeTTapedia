import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementControls

/-! Source addition, mutable nested reads, parallel edges and self-loops. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics NamedSpaces KeyedImprovementSource
open KeyedImprovementSource.Controls (names program equation distance)

def edge (origin into cost : Nat) : Atom := .expression [.symbol "e", number origin, number into, number cost]
def edges : List Atom := [edge 0 1 3, edge 0 1 3, edge 0 2 4, edge 0 0 0]
def before : Effects.State := ((Store.new [distance 0 0, distance 1 10] []).allocate edges).2
def after : Effects.State := {before with core := [distance 0 0, distance 1 3, distance 2 4]}
def caller : Subst := [(names.space, Effects.handleValue .self), ("u", number 0)]
def legs : List NestedQuerySource.Leg := [(.self, row "sd" (.var "u") (.var "d")),
  (.privateSpace 0, .expression [.symbol "e", .var "u", .var names.vertex, .var "w"])]
def worker : EffectfulQuerySource.Body := body program "improve" names "sd" "d" "w" .self

theorem nested_relaxation_retains_changed_occurrences :
    NestedQuerySource.run worker legs caller before = some (after, [number 1, number 2]) := by kernel_reflexivity

theorem actual_nested_source_returns :
    Eval.Returns program caller before (NestedQuerySource.source legs (call "improve" names "d" "w")) after [number 1, number 2] :=
  nested_returns program "improve" names "sd" "d" "w" .self legs caller before after [number 1, number 2]
    nested_relaxation_retains_changed_occurrences

theorem repeated_relaxation_is_silent : NestedQuerySource.run worker legs caller after = some (after, []) := by kernel_reflexivity

theorem quiet_phase_has_complete_nested_coverage : NestedQuerySource.QuietAt worker after legs caller :=
  (nested_quiet_iff program "improve" names "sd" "d" "w" .self legs caller after).mp repeated_relaxation_is_silent

theorem missing_live_graph_is_not_an_empty_phase :
    NestedQuerySource.run worker legs caller (Store.new [distance 0 0] []) = none := by kernel_reflexivity

theorem unreached_graph_needs_no_read :
    NestedQuerySource.run worker legs caller Effects.empty = some (Effects.empty, []) := by kernel_reflexivity

theorem edge_store_is_not_rewritten : after.read (.privateSpace 0) = before.read (.privateSpace 0) := rfl

def leaf : Subst := [("d", number 0), ("w", number 3), (names.vertex, number 1), (names.space, Effects.handleValue .self)]

theorem exact_addition_operand :
    Eval.PureReturns program leaf before (sum "d" "w") before (number 3) :=
  sum_returns program leaf before "d" "w" 0 3 rfl rfl

theorem large_addition_is_exact :
    Eval.PureReturns program [("d", number (2^64)), ("w", number 1)] before (sum "d" "w") before (number (2^64 + 1)) :=
  sum_returns program _ before "d" "w" (2^64) 1 rfl rfl

theorem wrapping_changes_the_source_candidate : number (2^64 + 1) ≠ number 1 := by decide +kernel

def raw : Program := {program with declarations := [
  .expression [.symbol ":", .symbol "improve",
    .expression [.symbol "->", .symbol "Space", .symbol "Number", .symbol "Atom", .symbol "Number"]]]}

theorem raw_candidate_is_not_an_addition : Eval.argumentIsRaw raw "improve" 2 = true := by decide +kernel

theorem changed_candidate_demand_refuses : body raw "improve" names "sd" "d" "w" .self leaf before = none := by kernel_reflexivity

theorem negative_edge_weight_refuses :
    worker (("w", .grounded (.int (-1))) :: leaf) before = none := by kernel_reflexivity

theorem boolean_edge_weight_refuses : worker (("w", Effects.boolean true) :: leaf) before = none := by kernel_reflexivity

theorem missing_capture_refuses : worker [] before = none := by kernel_reflexivity

theorem changed_destination_capture_refuses : worker ((names.space, Effects.handleValue (.privateSpace 0)) :: leaf) before = none := by
  kernel_reflexivity

def store : Mettapedia.Machines.KeyedImprovement.Store Nat Nat := fun key => if key = 0 then some 0 else if key = 1 then some 10 else none
def arc : Mettapedia.Machines.WeightedRelaxation.Arc Nat := ⟨0, 1, 3⟩

theorem source_candidate_has_min_plus_meaning :
    Mettapedia.Machines.KeyedImprovement.denote (Mettapedia.Machines.KeyedImprovement.improve store 1 3).1 =
      Mettapedia.Machines.WeightedRelaxation.relax (Mettapedia.Machines.KeyedImprovement.denote store) arc :=
  improvement_denotes_relaxation store arc 0 rfl

theorem zero_cost_self_loop_keeps_the_captured_distance :
    (Mettapedia.Machines.KeyedImprovement.improve store 0 0).1 0 = some 0 :=
  improvement_preserves_source store ⟨0, 0, 0⟩ 0 rfl

theorem parallel_edges_are_not_two_improvements :
    NestedQuerySource.run worker legs caller before ≠ some (after, [number 1, number 1, number 2]) := by
  rw [nested_relaxation_retains_changed_occurrences]
  simp [number]

def frontierCaller : Subst := [(names.space, Effects.handleValue .self), ("front", .expression [number 0])]
def frontierWorker : EffectfulQuerySource.Body := frontierRun program "improve" names "sd" "d" "w" "front" "u" .self legs

theorem captured_frontier_collects_changed_vertices :
    frontierWorker frontierCaller before = some (after, [number 1, number 2]) := by kernel_reflexivity

theorem actual_frontier_source_returns :
    Eval.PureReturns program frontierCaller before (frontierBody "improve" names "d" "w" "front" "u" legs)
      after (.expression [number 1, number 2]) :=
  frontier_returns program "improve" names "sd" "d" "w" "front" "u" .self legs frontierCaller before after _
    captured_frontier_collects_changed_vertices

def twiceBefore : Effects.State :=
  ((Store.new [distance 0 0, distance 1 10] []).allocate [edge 0 1 9, edge 0 1 3, edge 0 2 4]).2
def twiceAfter : Effects.State := {twiceBefore with core := [distance 0 0, distance 1 3, distance 2 4]}

theorem repeated_target_retains_both_improvement_events :
    EffectfulQuerySource.traverse (NestedQuerySource.run worker legs)
      (FrontierCollectionSource.environments frontierCaller "u" [number 0]) (twiceBefore, []) =
      some (twiceAfter, [number 1, number 1, number 2]) := by kernel_reflexivity

theorem only_next_frontier_is_deduplicated :
    frontierWorker frontierCaller twiceBefore = some (twiceAfter, [number 1, number 2]) := by kernel_reflexivity

theorem deduplicated_frontier_has_actual_source_execution :
    Eval.PureReturns program frontierCaller twiceBefore (frontierBody "improve" names "d" "w" "front" "u" legs)
      twiceAfter (.expression [number 1, number 2]) :=
  frontier_returns program "improve" names "sd" "d" "w" "front" "u" .self legs frontierCaller twiceBefore twiceAfter _
    only_next_frontier_is_deduplicated

theorem occupied_iteration_binding_refuses :
    frontierWorker (("u", number 0) :: frontierCaller) before = none := by kernel_reflexivity

theorem absent_frontier_refuses : frontierWorker [(names.space, Effects.handleValue .self)] before = none := by kernel_reflexivity

theorem empty_frontier_needs_no_graph :
    frontierWorker [(names.space, Effects.handleValue .self), ("front", .expression [])] Effects.empty =
      some (Effects.empty, []) := by kernel_reflexivity

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementSource.Controls
