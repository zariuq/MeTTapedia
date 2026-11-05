import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedQueryExecution

/-!
# Mutable source frontier visits and the shortest-path scan

The graph and functional distance relation have distinct handles. Each vertex
visit reads its current distance, so improvements by earlier visits are visible.
The source matcher and ordered update traversal establish the correspondence;
the graph read is preserved by the proved other-space frame property.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierRefinement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces KeyedImprovementSource EffectfulQuerySource WeightedQueryRows
open Mettapedia.Machines.KeyedImprovement (denote)
open Mettapedia.Machines.WeightedRelaxation

structure Query where
  names : Names
  head : String
  edgeHead : String
  origin : String
  distance : String
  weight : String
  target : Handle
  graphSpace : Handle
  separated : [origin, names.vertex, weight, names.space, distance].Nodup
  ordinary : head ∉ ["=", ":", ",", "cons"]
  edgeOrdinary : edgeHead ≠ "cons"
  apart : graphSpace ≠ target

def Query.legs (query : Query) : List NestedQuerySource.Leg :=
  [(query.target, distancePattern query.head query.origin query.distance),
   (query.graphSpace, edgePattern query.edgeHead query.origin query.names.vertex query.weight)]

def Query.worker (query : Query) (program : Program) (function : String) : Body :=
  NestedQuerySource.run (WeightedImprovementSource.body program function query.names query.head query.distance query.weight query.target) query.legs

def Query.Ready (query : Query) (caller : Subst) : Prop :=
  Subst.lookup caller query.names.space = some (Effects.handleValue query.target) ∧
  Subst.lookup caller query.origin = none ∧ Subst.lookup caller query.distance = none ∧
  Subst.lookup caller query.names.vertex = none ∧ Subst.lookup caller query.weight = none

instance (query : Query) (caller : Subst) : Decidable (query.Ready caller) := by
  unfold Query.Ready
  infer_instance

theorem traverse_refines (query : Query) (program : Program) (function : String)
    (certified : ∀ key candidate, KeyedImprovementEntry.Certificate program function query.names query.head query.target key candidate)
    (demanded : argumentIsRaw program function 2 = false)
    (graph : List (Arc Nat)) (caller : Subst) (ready : query.Ready caller)
    (frontier : List Nat) (before : Effects.State) (store : Nat → Option Nat)
    (represented : KeyedImprovementRows.Represents query.head before query.target store)
    (graphRead : before.read query.graphSpace = some (graph.map (encodeEdge query.edgeHead)))
    (reached : ∀ vertex ∈ frontier, ∃ distance, store vertex = some distance) (changed : List Nat) :
    ∃ after nextStore,
      traverse (query.worker program function)
        (frontier.map (fun vertex => (query.origin, number vertex) :: caller)) (before, changed.map number) =
        some (after, (Rounds.scan (Rounds.duties graph frontier) (denote store) changed).2.map number) ∧
      KeyedImprovementRows.Represents query.head after query.target nextStore ∧
      denote nextStore = (Rounds.scan (Rounds.duties graph frontier) (denote store) changed).1 ∧
      (∀ other, other ≠ query.target → after.read other = before.read other) ∧ after.cells = before.cells := by
  induction frontier generalizing before store changed with
  | nil => exact ⟨before, store, rfl, represented, rfl, fun _ _ => rfl, rfl⟩
  | cons vertex rest ih =>
      obtain ⟨base, held⟩ := reached vertex List.mem_cons_self
      have separation := List.nodup_cons.mp query.separated
      have outside := separation.1
      simp only [List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, and_true] at outside
      let captured := (query.origin, number vertex) :: caller
      obtain ⟨middle, middleStore, called, middleRep, middleLabels, otherReads, cells⟩ :=
        WeightedQueryExecution.nested_reached_refines program function query.names query.head query.edgeHead
          query.origin query.distance query.weight query.target query.graphSpace captured vertex base graph separation.2
          (Ne.symm outside.2.2.2) query.ordinary query.edgeOrdinary certified demanded
          (by simpa [captured, Subst.lookup, outside.2.2.1] using ready.1)
          (by simp [captured, Subst.lookup])
          (by simpa [captured, Subst.lookup, outside.2.2.2] using ready.2.2.1)
          (by simpa [captured, Subst.lookup, outside.1] using ready.2.2.2.1)
          (by simpa [captured, Subst.lookup, outside.2.1] using ready.2.2.2.2)
          before store held represented graphRead
      have lower : denote middleStore ≤ denote store := by
        rw [middleLabels]
        exact (Rounds.scan_progress _ _ []).1
      have remaining : ∀ later ∈ rest, ∃ distance, middleStore later = some distance := by
        intro later member
        obtain ⟨distance, present⟩ := reached later (List.mem_cons_of_mem _ member)
        exact Mettapedia.Machines.KeyedImprovement.present_of_denote_le store middleStore lower later distance present
      obtain ⟨after, nextStore, traversed, afterRep, afterLabels, otherAfter, cellsAfter⟩ :=
        ih middle middleStore middleRep ((otherReads query.graphSpace query.apart).trans graphRead) remaining
          (changed ++ (Rounds.scan (Worklist.outgoing graph vertex) (denote store) []).2)
      rw [middleLabels] at traversed afterLabels
      have shifted := Rounds.scan_prefix (Worklist.outgoing graph vertex) (denote store) changed []
      simp only [List.append_nil] at shifted
      have combined : Rounds.scan (Rounds.duties graph (vertex :: rest)) (denote store) changed =
          Rounds.scan (Rounds.duties graph rest) (Rounds.scan (Worklist.outgoing graph vertex) (denote store) []).1
            (changed ++ (Rounds.scan (Worklist.outgoing graph vertex) (denote store) []).2) := by
        simp only [Rounds.duties, List.flatMap_cons, Rounds.scan_append]
        rw [shifted]
      rw [combined]
      refine ⟨after, nextStore, ?_, afterRep, afterLabels,
        fun other apart => (otherAfter other apart).trans (otherReads other apart), cellsAfter.trans cells⟩
      change query.worker program function captured before = _ at called
      dsimp only [captured] at called
      simp only [List.map_cons, EffectfulQuerySource.traverse, called, Option.bind_some]
      simpa only [List.map_append] using traversed

/-- The completed source phase matches the existing scheduler's entire pass,
including stable next-frontier deduplication, not just its final support. -/
theorem pass_refines (query : Query) (program : Program) (function : String)
    (certified : ∀ key candidate, KeyedImprovementEntry.Certificate program function query.names query.head query.target key candidate)
    (demanded : argumentIsRaw program function 2 = false)
    (graph : List (Arc Nat)) (caller : Subst) (ready : query.Ready caller)
    (frontierName : String) (frontier : List Nat)
    (captured : Subst.lookup caller frontierName = some (.expression (frontier.map number)))
    (before : Effects.State) (store : Nat → Option Nat)
    (represented : KeyedImprovementRows.Represents query.head before query.target store)
    (graphRead : before.read query.graphSpace = some (graph.map (encodeEdge query.edgeHead)))
    (reached : ∀ vertex ∈ frontier, ∃ distance, store vertex = some distance) :
    ∃ after nextStore,
      FrontierCollectionSource.run (query.worker program function) frontierName query.origin caller before =
        some (after, (Rounds.pass graph (denote store) frontier).2.map number) ∧
      KeyedImprovementRows.Represents query.head after query.target nextStore ∧
      denote nextStore = (Rounds.pass graph (denote store) frontier).1 ∧
      (∀ other, other ≠ query.target → after.read other = before.read other) ∧ after.cells = before.cells := by
  obtain ⟨after, nextStore, traversed, afterRep, labels, others, cells⟩ :=
    traverse_refines query program function certified demanded graph caller ready frontier before store represented graphRead reached []
  refine ⟨after, nextStore, ?_, afterRep, labels, others, cells⟩
  unfold FrontierCollectionSource.run
  rw [captured]
  simp only [ready.2.1, ↓reduceIte]
  have visits : FrontierCollectionSource.environments caller query.origin (frontier.map number) =
      frontier.map (fun vertex => (query.origin, number vertex) :: caller) := by
    simp [FrontierCollectionSource.environments, List.map_map, Function.comp_def]
  simp only [List.map_nil] at traversed
  rw [visits, traversed]
  change some (after, ((Rounds.scan (Rounds.duties graph frontier) (denote store) []).2.map number).eraseDups) = _
  rw [numbers_eraseDups]
  rfl

theorem source_phase_returns (query : Query) (program : Program) (function : String)
    (caller : Subst) (frontierName : String) (before after : Effects.State) (next : List Atom)
    (completed : FrontierCollectionSource.run (query.worker program function) frontierName query.origin caller before = some (after, next)) :
    PureReturns program caller before
      (FrontierCollectionSource.source frontierName query.origin
        (NestedQuerySource.source query.legs (WeightedImprovementSource.call function query.names query.distance query.weight)))
      after (.expression next) :=
  FrontierCollectionSource.source_returns program _ _
    (WeightedImprovementSource.nested_returns program function query.names query.head query.distance query.weight query.target query.legs)
    frontierName query.origin caller before after next completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedFrontierRefinement
