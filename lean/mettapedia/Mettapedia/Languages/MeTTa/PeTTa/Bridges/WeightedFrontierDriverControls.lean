import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationRegion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierRefinement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierDriver

/-! Actual recursive weighted source execution, including order-sensitive round counts. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierDriverControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces
open KeyedImprovementSource (number)
open KeyedImprovementSource.Controls (names distance equation)
open WeightedImprovementSource.Controls (edge legs)

def driverNames : FrontierIterationSource.Names := ⟨"front", "round", "next", by decide⟩
def phase : Atom := .expression [.symbol "let", .var names.space,
  .expression [.symbol "quote", Effects.handleValue .self],
  WeightedImprovementSource.frontierBody "improve" names "d" "w" "front" "u" legs]
def driverEquation : Equation := ⟨"sssp", [.var "front", .var "round"], FrontierIterationSource.body "sssp" driverNames phase⟩
def program : Program := {equations := [equation, driverEquation], declarations := []}

def phaseWorker : EffectfulQuerySource.Body := fun bindings state =>
  if Subst.lookup bindings names.space = none then
    WeightedImprovementSource.frontierRun program "improve" names "sd" "d" "w" "front" "u" .self legs
      ((names.space, Effects.handleValue .self) :: bindings) state
  else none

theorem phase_returns (bindings : Subst) (before after : Effects.State) (next : List Atom)
    (completed : phaseWorker bindings before = some (after, next)) :
    PureReturns program bindings before phase after (.expression next) := by
  unfold phaseWorker at completed
  split at completed
  next fresh =>
    apply BridgeKit.fresh_let_returns program bindings before before after names.space _ (Effects.handleValue .self) _ _ fresh
      (quote_returns program bindings before (Effects.handleValue .self))
    exact WeightedImprovementSource.frontier_returns program "improve" names "sd" "d" "w" "front" "u" .self legs _ _ _ _ completed
  next => cases completed

def certificate : FrontierIterationSource.Certificate program "sssp" driverNames phase where
  notIO := by decide
  notNative := by decide
  notControl := by decide
  registered := by decide
  counterDemanded := by decide
  selected := by
    intro frontier count
    simp [clauses, program, equation, driverEquation, driverNames, FrontierIterationSource.callee,
      matchValue.matchValues, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Subst.lookup]

def graph : List Atom := [edge 0 1 2, edge 0 2 9, edge 1 2 3, edge 2 3 1]
def reversedGraph : List Atom := [edge 0 2 9, edge 0 1 2, edge 1 2 3, edge 2 3 1]
def initial (rows : List Atom) : Effects.State := ((Store.new [distance 0 0] []).allocate rows).2
def final (rows : List Atom) : Effects.State :=
  {initial rows with core := [distance 0 0, distance 1 2, distance 2 5, distance 3 6]}

theorem ordered_rounds_complete :
    FrontierIterationSource.iterate phaseWorker driverNames 3 [number 0] 0 (initial graph) = some (final graph, 2) := by kernel_reflexivity

theorem reversed_rounds_complete :
    FrontierIterationSource.iterate phaseWorker driverNames 4 [number 0] 0 (initial reversedGraph) = some (final reversedGraph, 3) := by kernel_reflexivity

theorem actual_forward_source_call :
    PureReturns program (FrontierIterationSource.callee driverNames [number 0] 0) (initial graph)
      (.expression [.symbol "sssp", .var "front", .var "round"]) (final graph) (number 2) :=
  FrontierIterationSource.call_returns certificate phaseWorker phase_returns 3 [number 0] 0 (initial graph) (final graph) 2 ordered_rounds_complete

theorem actual_reversed_source_call :
    PureReturns program (FrontierIterationSource.callee driverNames [number 0] 0) (initial reversedGraph)
      (.expression [.symbol "sssp", .var "front", .var "round"]) (final reversedGraph) (number 3) :=
  FrontierIterationSource.call_returns certificate phaseWorker phase_returns 4 [number 0] 0 (initial reversedGraph) (final reversedGraph) 3 reversed_rounds_complete

theorem equal_distances_do_not_certify_equal_source_results :
    (final graph).core = (final reversedGraph).core ∧ number 2 ≠ number 3 := by decide +kernel

theorem insufficient_allowance_is_not_termination :
    FrontierIterationSource.iterate phaseWorker driverNames 2 [number 0] 0 (initial graph) = none := by kernel_reflexivity

theorem missing_graph_is_not_an_empty_next_frontier :
    FrontierIterationSource.iterate phaseWorker driverNames 3 [number 0] 0 (Store.new [distance 0 0] []) = none := by kernel_reflexivity

theorem already_occupied_space_capture_refuses :
    phaseWorker [(names.space, Effects.handleValue .self), ("front", .expression [number 0])] (initial graph) = none := by
  kernel_reflexivity

theorem empty_frontier_preserves_counter :
    FrontierIterationSource.iterate phaseWorker driverNames 1 [] 7 (initial graph) = some (initial graph, 7) := by kernel_reflexivity

def plan (allowance : Nat) := FrontierIterationRegion.region "improvement" certificate phaseWorker phase_returns allowance [number 0] 0

theorem completed_region_retains_counter_and_state :
    (plan 3).attempt (initial graph) = .committed (PureCallPortfolio.complete (final graph) (number 2)) := by
  kernel_reflexivity

theorem unfinished_private_attempt_restores_exact_entrance :
    (plan 2).attempt (initial graph) = .declined (initial graph) := by kernel_reflexivity

theorem unfinished_private_attempt_executes_reference :
    (plan 2).execute (initial graph) = {PureCallPortfolio.complete (final graph) (number 2)} := by
  rw [plan, FrontierIterationRegion.execute_exact]
  exact FrontierIterationRegion.source_meaning certificate phaseWorker phase_returns 3 [number 0] 0
    (initial graph) (final graph) 2 ordered_rounds_complete

theorem source_page_observation_refuses :
    (FrontierIterationRegion.admission .exactPage "improvement" certificate phaseWorker phase_returns 3 [number 0] 0).isNone = true := rfl

def graphQuery : WeightedFrontierRefinement.Query :=
  ⟨names, "sd", "e", "u", "d", "w", .self, .privateSpace 0, by decide, by decide, by decide, by decide⟩

def improvementCertificate (key candidate : Nat) :
    KeyedImprovementEntry.Certificate program "improve" names "sd" .self key candidate where
  notIO := by decide
  notNative := by decide
  notControl := by decide
  registered := by decide
  selected := by
    simp [clauses, program, equation, driverEquation, names, KeyedImprovementSource.bindings,
      matchValue.matchValues, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Subst.lookup]

def rootStore : Nat → Option Nat := fun vertex => if vertex = 0 then some 0 else none
def initialCaller : Subst := [(names.space, Effects.handleValue .self), ("front", .expression [number 0])]

theorem initial_rows_represent (rows : List Atom) : KeyedImprovementRows.Represents "sd" (initial rows) .self rootStore := by
  refine ⟨[(0, 0)], rfl, ?_⟩
  intro key
  by_cases zero : key = 0 <;>
    simp [Mettapedia.Machines.KeyedImprovement.OrderedRows.fibre, rootStore, zero, eq_comm]

/-- A concrete authored program, but an arbitrary finite graph, not one
closed evaluator example. -/
theorem arbitrary_graph_initial_phase (edges : List (Mettapedia.Machines.WeightedRelaxation.Arc Nat)) :
    ∃ after nextStore,
      FrontierCollectionSource.run (graphQuery.worker program "improve") "front" "u" initialCaller
          (initial (edges.map (WeightedQueryRows.encodeEdge "e"))) =
        some (after, (Mettapedia.Machines.WeightedRelaxation.Rounds.pass edges
          (Mettapedia.Machines.KeyedImprovement.denote rootStore) [0]).2.map number) ∧
      PureReturns program initialCaller (initial (edges.map (WeightedQueryRows.encodeEdge "e")))
        (FrontierCollectionSource.source "front" "u" (NestedQuerySource.source graphQuery.legs
          (WeightedImprovementSource.call "improve" names "d" "w"))) after
        (.expression ((Mettapedia.Machines.WeightedRelaxation.Rounds.pass edges
          (Mettapedia.Machines.KeyedImprovement.denote rootStore) [0]).2.map number)) ∧
      KeyedImprovementRows.Represents "sd" after .self nextStore ∧
      Mettapedia.Machines.KeyedImprovement.denote nextStore =
        (Mettapedia.Machines.WeightedRelaxation.Rounds.pass edges
          (Mettapedia.Machines.KeyedImprovement.denote rootStore) [0]).1 := by
  obtain ⟨after, nextStore, completed, represented, labels, _, _⟩ :=
    WeightedFrontierRefinement.pass_refines graphQuery program "improve" improvementCertificate (by decide)
      edges initialCaller (by decide) "front" [0] rfl _ rootStore (initial_rows_represent _) rfl
      (by intro vertex member; simp only [List.mem_singleton] at member; subst vertex; exact ⟨0, rfl⟩)
  exact ⟨after, nextStore, completed,
    WeightedFrontierRefinement.source_phase_returns graphQuery program "improve" initialCaller "front" _ _ _ completed,
    represented, labels⟩

theorem duplicate_graph_occurrences_survive_matching :
    EffectfulQuerySource.choices [("u", number 0)] (WeightedQueryRows.edgePattern "e" "u" "vertex" "w")
      [edge 0 1 3, edge 0 1 3] =
      [[("w", number 3), ("vertex", number 1), ("u", number 0)],
       [("w", number 3), ("vertex", number 1), ("u", number 0)]] := by kernel_reflexivity

theorem captured_destination_filters_instead_of_becoming_fresh :
    EffectfulQuerySource.choices [("u", number 0), ("vertex", number 2)]
      (WeightedQueryRows.edgePattern "e" "u" "vertex" "w") [edge 0 1 3] = [] := by kernel_reflexivity

theorem overlapping_origin_capture_is_not_ready :
    ¬ graphQuery.Ready (("u", number 0) :: initialCaller) := by decide +kernel

def driverConfig : WeightedFrontierDriver.Configuration := ⟨graphQuery, driverNames, by decide, by decide⟩

theorem root_labels_are_initial : Mettapedia.Machines.KeyedImprovement.denote rootStore =
    Mettapedia.Machines.WeightedRelaxation.initial 0 := by
  funext vertex
  by_cases zero : vertex = 0 <;>
    simp [Mettapedia.Machines.KeyedImprovement.denote, rootStore, Mettapedia.Machines.WeightedRelaxation.initial, zero]

/-- A complete recursive source call for every finite natural-weight graph,
with distances defined independently by weighted paths. -/
theorem arbitrary_graph_source_shortest_paths (edges : List (Mettapedia.Machines.WeightedRelaxation.Arc Nat)) :
    ∃ after nextStore rounds,
      PureReturns program (FrontierIterationSource.callee driverNames [number 0] 0)
        (initial (edges.map (WeightedQueryRows.encodeEdge "e")))
        (.expression [.symbol "sssp", .var "front", .var "round"]) after (number rounds) ∧
      KeyedImprovementRows.Represents "sd" after .self nextStore ∧
      Mettapedia.Machines.KeyedImprovement.denote nextStore = Mettapedia.Machines.WeightedRelaxation.distance edges 0 ∧
      (∀ other, other ≠ .self → after.read other = (initial (edges.map (WeightedQueryRows.encodeEdge "e"))).read other) ∧
      after.cells = (initial (edges.map (WeightedQueryRows.encodeEdge "e"))).cells :=
  WeightedFrontierDriver.source_shortest_paths driverConfig program "improve" "sssp" improvementCertificate (by decide)
    certificate edges 0 _ rootStore (initial_rows_represent _) rfl root_labels_are_initial

theorem checked_driver_retains_the_source_counter :
    FrontierIterationSource.iterate (driverConfig.worker program "improve") driverNames 3 [number 0] 0 (initial graph) =
      some (final graph, 2) := by kernel_reflexivity

theorem stored_open_edge_selects_no_private_execution :
    driverConfig.worker program "improve" (FrontierIterationSource.callee driverNames [number 0] 0)
      (initial [.expression [.symbol "e", .var "stored-origin", number 1, number 3]]) = none := by kernel_reflexivity

theorem stored_open_distance_selects_no_private_execution :
    driverConfig.worker program "improve" (FrontierIterationSource.callee driverNames [number 0] 0)
      {initial graph with core := [.expression [.symbol "sd", .var "stored-origin", number 0]]} = none := by kernel_reflexivity

theorem open_frontier_selects_no_private_execution :
    driverConfig.worker program "improve" (FrontierIterationSource.callee driverNames [.var "unknown"] 0) (initial graph) = none := by
  kernel_reflexivity

theorem negative_frontier_selects_no_private_execution :
    driverConfig.worker program "improve" (FrontierIterationSource.callee driverNames [.grounded (.int (-1))] 0) (initial graph) = none := by
  kernel_reflexivity

def checkedPlan := FrontierIterationRegion.region "improvement" certificate (driverConfig.worker program "improve")
  (WeightedFrontierDriver.phase_returns driverConfig program "improve") 3 [number 0] 0

theorem stored_open_edge_uses_reference :
    checkedPlan.execute (initial [.expression [.symbol "e", .var "stored-origin", number 1, number 3]]) =
      PureCallPortfolio.sourceMeaning program (FrontierIterationSource.callee driverNames [number 0] 0)
        (FrontierIterationRegion.entry "sssp" driverNames)
        (initial [.expression [.symbol "e", .var "stored-origin", number 1, number 3]]) :=
  FrontierIterationRegion.execute_exact "improvement" certificate (driverConfig.worker program "improve")
    (WeightedFrontierDriver.phase_returns driverConfig program "improve") 3 [number 0] 0 _

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierDriverControls
