import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierRefinement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationSource

/-!
# Repeated weighted source phases

Each authored driver activation binds only its frontier and round counter.
The phase introduces the distance-space capture locally and retains it through
the ordered queries. Name separation is checked independently of graph data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierDriver

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces KeyedImprovementSource EffectfulQuerySource
open Mettapedia.Machines.KeyedImprovement (denote)
open Mettapedia.Machines.WeightedRelaxation
open WeightedFrontierRefinement (Query)

structure Configuration where
  query : Query
  names : FrontierIterationSource.Names
  separated : ∀ slot ∈ [query.origin, query.names.vertex, query.weight, query.names.space, query.distance],
    slot ≠ names.frontier ∧ slot ≠ names.counter
  edgeData : query.edgeHead ∉ ["=", ":", ",", "cons"]

def Configuration.scope (config : Configuration) (caller : Subst) : Subst :=
  (config.query.names.space, Effects.handleValue config.query.target) :: caller

def Configuration.phase (config : Configuration) (function : String) : Atom :=
  .expression [.symbol "let", .var config.query.names.space,
    .expression [.symbol "quote", Effects.handleValue config.query.target],
    FrontierCollectionSource.source config.names.frontier config.query.origin
      (NestedQuerySource.source config.query.legs
        (WeightedImprovementSource.call function config.query.names config.query.distance config.query.weight))]

def natural : Atom → Bool
  | .grounded (.int (.ofNat _)) => true
  | _ => false

/-- Relevant stored open facts require the complete unifying route. Closed
frontier values alone do not justify treating those facts as absent. -/
def Configuration.readyInputs (config : Configuration) (caller : Subst) (state : Effects.State) : Bool :=
  match Subst.lookup (config.scope caller) config.names.frontier,
      state.read config.query.target, state.read config.query.graphSpace with
  | some (.expression values), some distances, some graph =>
      values.all natural &&
      ClosedQueryAdmission.capturesReady (config.scope caller)
        (WeightedQueryRows.distancePattern config.query.head config.query.origin config.query.distance) &&
      ClosedQueryAdmission.capturesReady (config.scope caller)
        (WeightedQueryRows.edgePattern config.query.edgeHead config.query.origin config.query.names.vertex config.query.weight) &&
      ClosedQueryAdmission.rowsReady (WeightedQueryRows.distancePattern config.query.head config.query.origin config.query.distance) distances &&
      ClosedQueryAdmission.rowsReady (WeightedQueryRows.edgePattern config.query.edgeHead config.query.origin config.query.names.vertex config.query.weight) graph
  | _, _, _ => false

def Configuration.worker (config : Configuration) (program : Program) (function : String) : Body :=
  fun caller state =>
    if Subst.lookup caller config.query.names.space = none ∧ config.readyInputs caller state = true then
      FrontierCollectionSource.run (config.query.worker program function) config.names.frontier config.query.origin
        (config.scope caller) state
    else none

theorem phase_returns (config : Configuration) (program : Program) (function : String)
    (caller : Subst) (before after : Effects.State) (next : List Atom)
    (completed : config.worker program function caller before = some (after, next)) :
    PureReturns program caller before (config.phase function) after (.expression next) := by
  unfold Configuration.worker at completed
  split at completed
  next fresh =>
    apply BridgeKit.fresh_let_returns program caller before before after config.query.names.space _
      (Effects.handleValue config.query.target) _ _ fresh.1
    · have quoted := quote_returns program caller before (Effects.handleValue config.query.target)
      have closed : Mettapedia.Languages.ProcessCalculi.MORK.applySubst caller (Effects.handleValue config.query.target) =
          Effects.handleValue config.query.target := by cases config.query.target <;> rfl
      simpa only [closed] using quoted
    · exact WeightedFrontierRefinement.source_phase_returns config.query program function _ config.names.frontier _ _ _ completed
  next => cases completed

private theorem callee_fresh (config : Configuration) (frontier : List Atom) (count : Nat) (slot : String)
    (member : slot ∈ [config.query.origin, config.query.names.vertex, config.query.weight, config.query.names.space, config.query.distance]) :
    Subst.lookup (FrontierIterationSource.callee config.names frontier count) slot = none := by
  have apart := config.separated slot member
  simp [FrontierIterationSource.callee, Subst.lookup, Ne.symm apart.1, Ne.symm apart.2]

theorem scope_ready (config : Configuration) (frontier : List Atom) (count : Nat) :
    config.query.Ready (config.scope (FrontierIterationSource.callee config.names frontier count)) := by
  have separated := config.query.separated
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at separated
  refine ⟨by simp [Configuration.scope, Subst.lookup], ?_, ?_, ?_, ?_⟩
  · simpa [Configuration.scope, Subst.lookup, Ne.symm separated.1.2.2.1] using
      callee_fresh config frontier count config.query.origin (by simp)
  · simpa [Configuration.scope, Subst.lookup, separated.2.2.2] using
      callee_fresh config frontier count config.query.distance (by simp)
  · simpa [Configuration.scope, Subst.lookup, Ne.symm separated.2.1.2.1] using
      callee_fresh config frontier count config.query.names.vertex (by simp)
  · simpa [Configuration.scope, Subst.lookup, Ne.symm separated.2.2.1.1] using
      callee_fresh config frontier count config.query.weight (by simp)

theorem scope_frontier (config : Configuration) (frontier : List Atom) (count : Nat) :
    Subst.lookup (config.scope (FrontierIterationSource.callee config.names frontier count)) config.names.frontier =
      some (.expression frontier) := by
  have outside := (config.separated config.query.names.space (by simp)).1
  have distinct := config.names.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
  simp [Configuration.scope, FrontierIterationSource.callee, Subst.lookup, outside, Ne.symm distinct.1.1]

theorem typed_inputs_ready (config : Configuration) (graph : List (Arc Nat)) (frontier : List Nat) (count : Nat)
    (before : Effects.State) (store : Nat → Option Nat)
    (represented : KeyedImprovementRows.Represents config.query.head before config.query.target store)
    (graphRead : before.read config.query.graphSpace = some (graph.map (WeightedQueryRows.encodeEdge config.query.edgeHead))) :
    config.readyInputs (FrontierIterationSource.callee config.names (frontier.map number) count) before = true := by
  obtain ⟨rows, snapshot, _⟩ := represented
  have ready := scope_ready config (frontier.map number) count
  have distanceReady := ClosedQueryAdmission.ground_rows_are_ready
    (WeightedQueryRows.distancePattern config.query.head config.query.origin config.query.distance)
    (KeyedImprovementRows.encodeRows config.query.head rows) (by
      intro atom member
      obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
      rfl)
  have graphReady := ClosedQueryAdmission.ground_rows_are_ready
    (WeightedQueryRows.edgePattern config.query.edgeHead config.query.origin config.query.names.vertex config.query.weight)
    (graph.map (WeightedQueryRows.encodeEdge config.query.edgeHead)) (by
      intro atom member
      obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
      rfl)
  have distanceCaptures : ClosedQueryAdmission.capturesReady
      (config.scope (FrontierIterationSource.callee config.names (frontier.map number) count))
      (WeightedQueryRows.distancePattern config.query.head config.query.origin config.query.distance) = true := by
    simp [ClosedQueryAdmission.capturesReady, WeightedQueryRows.distancePattern, row,
      Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars, Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
      ready.2.1, ready.2.2.1]
  have graphCaptures : ClosedQueryAdmission.capturesReady
      (config.scope (FrontierIterationSource.callee config.names (frontier.map number) count))
      (WeightedQueryRows.edgePattern config.query.edgeHead config.query.origin config.query.names.vertex config.query.weight) = true := by
    simp [ClosedQueryAdmission.capturesReady, WeightedQueryRows.edgePattern,
      Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars, Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList,
      ready.2.1, ready.2.2.2.1, ready.2.2.2.2]
  simp only [Configuration.readyInputs, scope_frontier, snapshot, graphRead, distanceReady, graphReady,
    distanceCaptures, graphCaptures, Bool.and_true]
  simp [List.all_map, Function.comp_def, natural, number]

theorem phase_refines (config : Configuration) (program : Program) (function : String)
    (certified : ∀ key candidate, KeyedImprovementEntry.Certificate program function config.query.names config.query.head config.query.target key candidate)
    (demanded : argumentIsRaw program function 2 = false)
    (graph : List (Arc Nat)) (frontier : List Nat) (count : Nat)
    (before : Effects.State) (store : Nat → Option Nat)
    (represented : KeyedImprovementRows.Represents config.query.head before config.query.target store)
    (graphRead : before.read config.query.graphSpace = some (graph.map (WeightedQueryRows.encodeEdge config.query.edgeHead)))
    (reached : ∀ vertex ∈ frontier, ∃ distance, store vertex = some distance) :
    ∃ after nextStore,
      config.worker program function (FrontierIterationSource.callee config.names (frontier.map number) count) before =
        some (after, (Rounds.pass graph (denote store) frontier).2.map number) ∧
      KeyedImprovementRows.Represents config.query.head after config.query.target nextStore ∧
      denote nextStore = (Rounds.pass graph (denote store) frontier).1 ∧
      (∀ other, other ≠ config.query.target → after.read other = before.read other) ∧ after.cells = before.cells := by
  obtain ⟨after, nextStore, completed, afterRep, labels, others, cells⟩ :=
    WeightedFrontierRefinement.pass_refines config.query program function certified demanded graph _
      (scope_ready config (frontier.map number) count) config.names.frontier frontier
      (scope_frontier config (frontier.map number) count) before store represented graphRead reached
  refine ⟨after, nextStore, ?_, afterRep, labels, others, cells⟩
  simpa only [Configuration.worker, callee_fresh config (frontier.map number) count config.query.names.space (by simp),
    typed_inputs_ready config graph frontier count before store represented graphRead, and_self, ↓reduceIte] using completed

theorem iterate_of_rounds (config : Configuration) (program : Program) (function : String)
    (certified : ∀ key candidate, KeyedImprovementEntry.Certificate program function config.query.names config.query.head config.query.target key candidate)
    (demanded : argumentIsRaw program function 2 = false)
    (graph : List (Arc Nat)) (fuel : Nat) (frontier : List Nat) (count : Nat)
    (before : Effects.State) (store : Nat → Option Nat)
    (represented : KeyedImprovementRows.Represents config.query.head before config.query.target store)
    (graphRead : before.read config.query.graphSpace = some (graph.map (WeightedQueryRows.encodeEdge config.query.edgeHead)))
    (reached : ∀ vertex ∈ frontier, ∃ distance, store vertex = some distance)
    (result : Labels Nat) (rounds : Nat)
    (completed : Rounds.run graph fuel (denote store) frontier count = some (result, rounds)) :
    ∃ after nextStore,
      FrontierIterationSource.iterate (config.worker program function) config.names fuel (frontier.map number) count before =
        some (after, rounds) ∧
      KeyedImprovementRows.Represents config.query.head after config.query.target nextStore ∧
      denote nextStore = result ∧
      (∀ other, other ≠ config.query.target → after.read other = before.read other) ∧ after.cells = before.cells := by
  induction fuel generalizing frontier count before store with
  | zero => cases completed
  | succ fuel ih =>
      obtain ⟨middle, middleStore, phaseRun, middleRep, middleLabels, otherReads, cells⟩ :=
        phase_refines config program function certified demanded graph frontier count before store represented graphRead reached
      simp only [Rounds.run] at completed
      split at completed
      next quiet =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
        refine ⟨middle, middleStore, ?_, middleRep, middleLabels, otherReads, cells⟩
        change (config.worker program function (FrontierIterationSource.callee config.names (frontier.map number) count) before).bind
          (fun receipt => if receipt.2 = [] then some (receipt.1, count)
            else FrontierIterationSource.iterate (config.worker program function) config.names fuel receipt.2 (count + 1) receipt.1) = _
        rw [phaseRun]
        simp [quiet]
      next productive =>
        have nextReached : ∀ vertex ∈ (Rounds.pass graph (denote store) frontier).2,
            ∃ distance, middleStore vertex = some distance := by
          intro vertex member
          have finite := Rounds.pass_frontier_finite graph (denote store) frontier vertex member
          rw [← middleLabels] at finite
          cases found : middleStore vertex with
          | none => simp [denote, found] at finite
          | some distance => exact ⟨distance, rfl⟩
        rw [← middleLabels] at completed
        obtain ⟨after, nextStore, continued, afterRep, labels, otherAfter, cellsAfter⟩ :=
          ih (Rounds.pass graph (denote store) frontier).2 (count + 1) middle middleStore middleRep
            ((otherReads config.query.graphSpace config.query.apart).trans graphRead) nextReached completed
        refine ⟨after, nextStore, ?_, afterRep, labels,
          fun other apart => (otherAfter other apart).trans (otherReads other apart), cellsAfter.trans cells⟩
        change (config.worker program function (FrontierIterationSource.callee config.names (frontier.map number) count) before).bind
          (fun receipt => if receipt.2 = [] then some (receipt.1, count)
            else FrontierIterationSource.iterate (config.worker program function) config.names fuel receipt.2 (count + 1) receipt.1) = _
        rw [phaseRun]
        simpa only [Option.bind_some, List.map_eq_nil_iff, if_neg productive] using continued

theorem source_call_of_rounds (config : Configuration) (program : Program) (function driver : String)
    (certified : ∀ key candidate, KeyedImprovementEntry.Certificate program function config.query.names config.query.head config.query.target key candidate)
    (demanded : argumentIsRaw program function 2 = false)
    (driverCertificate : FrontierIterationSource.Certificate program driver config.names (config.phase function))
    (graph : List (Arc Nat)) (fuel : Nat) (frontier : List Nat) (count : Nat)
    (before : Effects.State) (store : Nat → Option Nat)
    (represented : KeyedImprovementRows.Represents config.query.head before config.query.target store)
    (graphRead : before.read config.query.graphSpace = some (graph.map (WeightedQueryRows.encodeEdge config.query.edgeHead)))
    (reached : ∀ vertex ∈ frontier, ∃ distance, store vertex = some distance)
    (result : Labels Nat) (rounds : Nat)
    (completed : Rounds.run graph fuel (denote store) frontier count = some (result, rounds)) :
    ∃ after nextStore,
      PureReturns program (FrontierIterationSource.callee config.names (frontier.map number) count) before
        (.expression [.symbol driver, .var config.names.frontier, .var config.names.counter]) after (number rounds) ∧
      KeyedImprovementRows.Represents config.query.head after config.query.target nextStore ∧
      denote nextStore = result ∧
      (∀ other, other ≠ config.query.target → after.read other = before.read other) ∧ after.cells = before.cells := by
  obtain ⟨after, nextStore, ran, afterRep, labels, others, cells⟩ :=
    iterate_of_rounds config program function certified demanded graph fuel frontier count before store represented graphRead reached result rounds completed
  exact ⟨after, nextStore,
    FrontierIterationSource.call_returns driverCertificate (config.worker program function) (phase_returns config program function)
      fuel (frontier.map number) count before after rounds ran, afterRep, labels, others, cells⟩

/-- Finite edge lists suffice even over the unbounded natural vertex
namespace. The returned labels are the independent Mathlib-path distances;
the source counter is retained, not replaced by a schedule-invariant value. -/
theorem source_shortest_paths (config : Configuration) (program : Program) (function driver : String)
    (certified : ∀ key candidate, KeyedImprovementEntry.Certificate program function config.query.names config.query.head config.query.target key candidate)
    (demanded : argumentIsRaw program function 2 = false)
    (driverCertificate : FrontierIterationSource.Certificate program driver config.names (config.phase function))
    (graph : List (Arc Nat)) (root : Nat) (before : Effects.State) (store : Nat → Option Nat)
    (represented : KeyedImprovementRows.Represents config.query.head before config.query.target store)
    (graphRead : before.read config.query.graphSpace = some (graph.map (WeightedQueryRows.encodeEdge config.query.edgeHead)))
    (initialLabels : denote store = initial root) :
    ∃ after nextStore rounds,
      PureReturns program (FrontierIterationSource.callee config.names [number root] 0) before
        (.expression [.symbol driver, .var config.names.frontier, .var config.names.counter]) after (number rounds) ∧
      KeyedImprovementRows.Represents config.query.head after config.query.target nextStore ∧
      denote nextStore = distance graph root ∧
      (∀ other, other ≠ config.query.target → after.read other = before.read other) ∧ after.cells = before.cells := by
  obtain ⟨fuel, rounds, completed⟩ := Rounds.finite_shortest_paths graph root
  rw [← initialLabels] at completed
  have reached : ∀ vertex ∈ [root], ∃ value, store vertex = some value := by
    intro vertex member
    have same := List.mem_singleton.mp member
    subst vertex
    have value := congrFun initialLabels root
    cases found : store root with
    | none => simp [denote, found, initial] at value
    | some value => exact ⟨value, rfl⟩
  obtain ⟨after, nextStore, returned, afterRep, labels, others, cells⟩ :=
    source_call_of_rounds config program function driver certified demanded driverCertificate graph fuel [root] 0
      before store represented graphRead reached (distance graph root) rounds completed
  exact ⟨after, nextStore, rounds, returned, afterRep, labels, others, cells⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierDriver
