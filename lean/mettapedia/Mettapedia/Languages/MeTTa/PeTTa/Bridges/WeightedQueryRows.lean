import Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedImprovementSource

/-!
# Exact distance and outgoing-edge source queries

The actual PeTTa matcher reads a captured origin and introduces fresh result
slots. Distance fibres retain occurrence multiplicity; encoded edge lists
retain authored order and parallel occurrences. No matching oracle or set
quotient stands between source reads and the weighted graph.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedQueryRows

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics KeyedImprovementSource EffectfulQuerySource
open Mettapedia.Machines.KeyedImprovement
open Mettapedia.Machines.WeightedRelaxation (Arc)

def distancePattern (head origin distance : String) : Atom := row head (.var origin) (.var distance)

theorem distance_match (caller : Subst) (head origin distance : String) (ordinary : head ≠ "cons")
    (key : Nat) (entry : Nat × Nat)
    (captured : Subst.lookup caller origin = some (number key))
    (fresh : Subst.lookup caller distance = none) :
    matchValue caller (distancePattern head origin distance) (KeyedImprovementRows.encode head entry) =
      if entry.1 = key then some ((distance, number entry.2) :: caller) else none := by
  unfold distancePattern KeyedImprovementRows.encode row
  rw [matchValue_expression_of_not_cons _ _ _ (by
    intro first rest same
    exact ordinary (by simpa using (List.cons.inj same).1))]
  by_cases same : entry.1 = key <;>
    simp [matchValue.matchValues, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
      captured, fresh, number, same]

theorem distance_choices (caller : Subst) (head origin distance : String) (ordinary : head ≠ "cons")
    (key : Nat) (rows : List (Nat × Nat))
    (captured : Subst.lookup caller origin = some (number key))
    (fresh : Subst.lookup caller distance = none) :
    choices caller (distancePattern head origin distance) (KeyedImprovementRows.encodeRows head rows) =
      (OrderedRows.fibre rows key).map (fun value => (distance, number value) :: caller) := by
  simp only [choices, scan_bindings, KeyedImprovementRows.encodeRows, List.filterMap_map]
  induction rows with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.filterMap_cons, Function.comp_apply, distance_match caller head origin distance ordinary key entry captured fresh,
        OrderedRows.fibre_cons]
      by_cases same : entry.1 = key <;> simp [same]
      all_goals simpa only [Function.comp_def] using ih

theorem functional_distance_choices (caller : Subst) (head origin distance : String) (ordinary : head ≠ "cons")
    (key : Nat) (rows : List (Nat × Nat)) (store : Nat → Option Nat)
    (represented : OrderedRows.Represents rows store)
    (captured : Subst.lookup caller origin = some (number key))
    (fresh : Subst.lookup caller distance = none) :
    choices caller (distancePattern head origin distance) (KeyedImprovementRows.encodeRows head rows) =
      (store key).toList.map (fun value => (distance, number value) :: caller) := by
  rw [distance_choices caller head origin distance ordinary key rows captured fresh, represented key]

def encodeEdge (head : String) (edge : Arc Nat) : Atom :=
  .expression [.symbol head, number edge.source, number edge.target, number edge.weight]

def edgePattern (head origin destination weight : String) : Atom :=
  .expression [.symbol head, .var origin, .var destination, .var weight]

def edgeBindings (caller : Subst) (destination weight : String) (edge : Arc Nat) : Subst :=
  (weight, number edge.weight) :: (destination, number edge.target) :: caller

theorem edge_match (caller : Subst) (head origin destination weight : String)
    (ordinary : head ≠ "cons") (distinct : destination ≠ weight) (key : Nat) (edge : Arc Nat)
    (captured : Subst.lookup caller origin = some (number key))
    (freshDestination : Subst.lookup caller destination = none) (freshWeight : Subst.lookup caller weight = none) :
    matchValue caller (edgePattern head origin destination weight) (encodeEdge head edge) =
      if edge.source = key then some (edgeBindings caller destination weight edge) else none := by
  have weightFresh : Subst.lookup ((destination, number edge.target) :: caller) weight = none := by
    simpa [Subst.lookup, distinct] using freshWeight
  simp only [number] at weightFresh
  unfold edgePattern encodeEdge
  rw [matchValue_expression_of_not_cons _ _ _ (by
    intro first rest same
    exact ordinary (by simpa using (List.cons.inj same).1))]
  by_cases same : edge.source = key <;>
    simp [matchValue.matchValues, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
      captured, freshDestination, weightFresh, number, same, edgeBindings]

theorem edge_choices (caller : Subst) (head origin destination weight : String)
    (ordinary : head ≠ "cons") (distinct : destination ≠ weight) (key : Nat) (graph : List (Arc Nat))
    (captured : Subst.lookup caller origin = some (number key))
    (freshDestination : Subst.lookup caller destination = none) (freshWeight : Subst.lookup caller weight = none) :
    choices caller (edgePattern head origin destination weight) (graph.map (encodeEdge head)) =
      (graph.filter (fun edge => decide (edge.source = key))).map (edgeBindings caller destination weight) := by
  simp only [choices, scan_bindings, List.filterMap_map]
  induction graph with
  | nil => rfl
  | cons edge rest ih =>
      simp only [List.filterMap_cons, Function.comp_apply,
        edge_match caller head origin destination weight ordinary distinct key edge captured freshDestination freshWeight]
      by_cases same : edge.source = key <;> simp [same]
      all_goals simpa only [Function.comp_def] using ih

theorem edge_bindings_lookup (caller : Subst) (destination weight : String) (distinct : destination ≠ weight) (edge : Arc Nat) :
    Subst.lookup (edgeBindings caller destination weight edge) destination = some (number edge.target) ∧
    Subst.lookup (edgeBindings caller destination weight edge) weight = some (number edge.weight) := by
  simp [edgeBindings, Subst.lookup, Ne.symm distinct]

theorem edge_bindings_other (caller : Subst) (destination weight other : String)
    (notDestination : destination ≠ other) (notWeight : weight ≠ other) (edge : Arc Nat) :
    Subst.lookup (edgeBindings caller destination weight edge) other = Subst.lookup caller other := by
  simp [edgeBindings, Subst.lookup, notDestination, notWeight]

theorem numbers_eraseDups (values : List Nat) : (values.map number).eraseDups = values.eraseDups.map number := by
  cases values with
  | nil => rfl
  | cons value rest =>
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons, List.map_cons]
      congr 1
      have filtered : (rest.map number).filter (fun atom => !(atom == number value)) =
          (rest.filter (fun item => !(item == value))).map number := by
        rw [List.filter_map]
        congr 1
        apply List.filter_congr
        intro item _
        apply Bool.eq_iff_iff.mpr
        simp [number]
      rw [filtered]
      exact numbers_eraseDups _
termination_by values.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.WeightedQueryRows
