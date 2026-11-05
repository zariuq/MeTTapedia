import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedQueryRows
import Mettapedia.Machines.ShortestPathRounds

/-!
# Ordered source edge visits refine weighted relaxation

One captured source distance is used through its outgoing edge occurrences.
Nonnegative weights keep that distance current even across self-loops. Each
actual authored improvement call refines the existing keyed-store operation;
the entire ordered visit list refines the existing shortest-path scan, keeping
every changed event and leaving other spaces and state cells untouched.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedQueryExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces KeyedImprovementSource EffectfulQuerySource WeightedQueryRows
open Mettapedia.Machines.KeyedImprovement (denote improve)
open Mettapedia.Machines.WeightedRelaxation

theorem edge_body_eq_run (program : Program) (function : String) (names : Names)
    (head distance weight : String) (target : Handle) (caller : Subst) (base : Nat) (edge : Arc Nat)
    (separated : [names.vertex, weight, names.space, distance].Nodup)
    (certificate : KeyedImprovementEntry.Certificate program function names head target edge.target (base + edge.weight))
    (demanded : argumentIsRaw program function 2 = false)
    (location : Subst.lookup caller names.space = some (Effects.handleValue target))
    (readBase : Subst.lookup caller distance = some (number base)) (before : Effects.State) :
    WeightedImprovementSource.body program function names head distance weight target
      (edgeBindings caller names.vertex weight edge) before =
      KeyedImprovementSource.run names head target edge.target (base + edge.weight) before := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at separated
  obtain ⟨readKey, readWeight⟩ := edge_bindings_lookup caller names.vertex weight separated.1.1 edge
  exact WeightedImprovementSource.body_eq_run certificate demanded _ distance weight
    ((edge_bindings_other caller names.vertex weight names.space separated.1.2.1 separated.2.1.1 edge).trans location)
    readKey ((edge_bindings_other caller names.vertex weight distance separated.1.2.2 separated.2.1.2 edge).trans readBase)
    readWeight before

private theorem scan_step (edge : Arc Nat) (rest : List (Arc Nat)) (store : Nat → Option Nat)
    (base : Nat) (held : store edge.source = some base) (changed : List Nat) :
    Rounds.scan (edge :: rest) (denote store) changed =
      Rounds.scan rest (denote (improve store edge.target (base + edge.weight)).1)
        (changed ++ if (improve store edge.target (base + edge.weight)).2 then [edge.target] else []) := by
  have proposalValue : proposal (denote store) edge = ((base + edge.weight : Nat) : WithTop Nat) := by
    simp [proposal, denote, held, Nat.cast_add]
  have changedIff := Mettapedia.Machines.KeyedImprovement.changed_iff store edge.target (base + edge.weight)
  change (improve store edge.target (base + edge.weight)).2 = true ↔
    ((base + edge.weight : Nat) : WithTop Nat) < denote store edge.target at changedIff
  rw [← proposalValue] at changedIff
  rw [WeightedImprovementSource.improvement_denotes_relaxation store edge base held]
  by_cases better : proposal (denote store) edge < denote store edge.target
  · have flag := changedIff.mpr better
    simp [Rounds.scan, better, flag]
  · have flag : (improve store edge.target (base + edge.weight)).2 = false := by
      apply Bool.eq_false_iff.mpr
      exact fun yes => better (changedIff.mp yes)
    simp [Rounds.scan, better, flag, relax_of_not_better _ _ better]

theorem traverse_refines (program : Program) (function : String) (names : Names)
    (head distance weight : String) (target : Handle) (caller : Subst)
    (origin base : Nat) (edges : List (Arc Nat))
    (separated : [names.vertex, weight, names.space, distance].Nodup)
    (ordinary : head ∉ ["=", ":", ",", "cons"])
    (certified : ∀ key candidate, KeyedImprovementEntry.Certificate program function names head target key candidate)
    (demanded : argumentIsRaw program function 2 = false)
    (location : Subst.lookup caller names.space = some (Effects.handleValue target))
    (readBase : Subst.lookup caller distance = some (number base))
    (outgoing : ∀ edge ∈ edges, edge.source = origin)
    (before : Effects.State) (store : Nat → Option Nat) (held : store origin = some base)
    (represented : KeyedImprovementRows.Represents head before target store) (changed : List Nat) :
    ∃ after nextStore,
      traverse (WeightedImprovementSource.body program function names head distance weight target)
        (edges.map (edgeBindings caller names.vertex weight)) (before, changed.map number) =
        some (after, (Rounds.scan edges (denote store) changed).2.map number) ∧
      KeyedImprovementRows.Represents head after target nextStore ∧
      denote nextStore = (Rounds.scan edges (denote store) changed).1 ∧
      (∀ other, other ≠ target → after.read other = before.read other) ∧ after.cells = before.cells := by
  induction edges generalizing before store changed with
  | nil => exact ⟨before, store, rfl, represented, rfl, fun _ _ => rfl, rfl⟩
  | cons edge rest ih =>
      have source := outgoing edge List.mem_cons_self
      have atSource : store edge.source = some base := source ▸ held
      obtain ⟨middle, answers, ran, nextRepresentation, flags, otherReads, cells⟩ :=
        KeyedImprovementRows.run_total_refines names head ordinary target edge.target (base + edge.weight) before store represented
      have called := (edge_body_eq_run program function names head distance weight target caller base edge separated
        (certified edge.target (base + edge.weight)) demanded location readBase before).trans ran
      have current : (improve store edge.target (base + edge.weight)).1 origin = some base := by
        simpa only [source] using WeightedImprovementSource.improvement_preserves_source store edge base atSource
      obtain ⟨after, nextStore, traversed, representedAfter, labels, otherAfter, cellsAfter⟩ :=
        ih (fun later member => outgoing later (List.mem_cons_of_mem _ member)) middle
          (improve store edge.target (base + edge.weight)).1 current nextRepresentation
          (changed ++ if (improve store edge.target (base + edge.weight)).2 then [edge.target] else [])
      rw [scan_step edge rest store base atSource changed]
      refine ⟨after, nextStore, ?_, representedAfter, labels,
        fun other apart => (otherAfter other apart).trans (otherReads other apart), cellsAfter.trans cells⟩
      simp only [List.map_cons, EffectfulQuerySource.traverse, called, Option.bind_some]
      rw [flags]
      by_cases improved : (improve store edge.target (base + edge.weight)).2 = true <;>
        simpa [improved] using traversed

/-- Both actual query legs are decoded before connecting their ordered body
visits to the graph scan. The distance label is known to be reached. -/
theorem nested_reached_refines (program : Program) (function : String) (names : Names)
    (head edgeHead originName distance weight : String) (target graphSpace : Handle) (caller : Subst)
    (origin base : Nat) (graph : List (Arc Nat))
    (separated : [names.vertex, weight, names.space, distance].Nodup)
    (distanceOrigin : distance ≠ originName)
    (ordinary : head ∉ ["=", ":", ",", "cons"]) (edgeOrdinary : edgeHead ≠ "cons")
    (certified : ∀ key candidate, KeyedImprovementEntry.Certificate program function names head target key candidate)
    (demanded : argumentIsRaw program function 2 = false)
    (location : Subst.lookup caller names.space = some (Effects.handleValue target))
    (readOrigin : Subst.lookup caller originName = some (number origin))
    (freshDistance : Subst.lookup caller distance = none)
    (freshDestination : Subst.lookup caller names.vertex = none) (freshWeight : Subst.lookup caller weight = none)
    (before : Effects.State) (store : Nat → Option Nat) (held : store origin = some base)
    (represented : KeyedImprovementRows.Represents head before target store)
    (graphRead : before.read graphSpace = some (graph.map (encodeEdge edgeHead))) :
    ∃ after nextStore,
      NestedQuerySource.run (WeightedImprovementSource.body program function names head distance weight target)
        [(target, distancePattern head originName distance), (graphSpace, edgePattern edgeHead originName names.vertex weight)] caller before =
        some (after, (Rounds.scan (Worklist.outgoing graph origin) (denote store) []).2.map number) ∧
      KeyedImprovementRows.Represents head after target nextStore ∧
      denote nextStore = (Rounds.scan (Worklist.outgoing graph origin) (denote store) []).1 ∧
      (∀ other, other ≠ target → after.read other = before.read other) ∧ after.cells = before.cells := by
  have parts := separated
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at parts
  have notCons : head ≠ "cons" := by intro same; simp [same] at ordinary
  obtain ⟨rows, snapshot, fibres⟩ := represented
  have outerChoices : choices caller (distancePattern head originName distance) (KeyedImprovementRows.encodeRows head rows) =
      [(distance, number base) :: caller] := by
    rw [functional_distance_choices caller head originName distance notCons origin rows store fibres readOrigin freshDistance, held]
    rfl
  let withDistance := (distance, number base) :: caller
  have captured : Subst.lookup withDistance originName = some (number origin) := by
    simpa [withDistance, Subst.lookup, distanceOrigin] using readOrigin
  have freshVertex : Subst.lookup withDistance names.vertex = none := by
    simpa [withDistance, Subst.lookup, Ne.symm parts.1.2.2] using freshDestination
  have weightFresh : Subst.lookup withDistance weight = none := by
    simpa [withDistance, Subst.lookup, Ne.symm parts.2.1.2] using freshWeight
  have retainedLocation : Subst.lookup withDistance names.space = some (Effects.handleValue target) := by
    simpa [withDistance, Subst.lookup, Ne.symm parts.2.2] using location
  have innerChoices := edge_choices withDistance edgeHead originName names.vertex weight edgeOrdinary parts.1.1 origin graph
    captured freshVertex weightFresh
  obtain ⟨after, nextStore, traversed, representedAfter, labels, otherReads, cells⟩ :=
    traverse_refines program function names head distance weight target withDistance origin base (Worklist.outgoing graph origin)
      separated ordinary certified demanded retainedLocation (by simp [withDistance, Subst.lookup])
      (by intro edge member; exact (List.mem_filter.mp member).2 |> of_decide_eq_true)
      before store held ⟨rows, snapshot, fibres⟩ []
  refine ⟨after, nextStore, ?_, representedAfter, labels, otherReads, cells⟩
  have innerRun : NestedQuerySource.run (WeightedImprovementSource.body program function names head distance weight target)
      [(graphSpace, edgePattern edgeHead originName names.vertex weight)] withDistance before =
      some (after, (Rounds.scan (Worklist.outgoing graph origin) (denote store) []).2.map number) := by
    change (before.read graphSpace).bind (fun current =>
      traverse (WeightedImprovementSource.body program function names head distance weight target)
        (choices withDistance (edgePattern edgeHead originName names.vertex weight) current) (before, [])) = _
    rw [graphRead]
    simp only [Option.bind_some, innerChoices]
    exact traversed
  change (before.read target).bind (fun current =>
    traverse (NestedQuerySource.run (WeightedImprovementSource.body program function names head distance weight target)
      [(graphSpace, edgePattern edgeHead originName names.vertex weight)])
      (choices caller (distancePattern head originName distance) current) (before, [])) = _
  rw [snapshot]
  simp only [Option.bind_some, outerChoices, EffectfulQuerySource.traverse, List.nil_append]
  change (NestedQuerySource.run _ _ withDistance before).bind (fun next => some (next.1, next.2)) = _
  rw [innerRun]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedQueryExecution
