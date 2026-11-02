import Mettapedia.GSLT.Dynamics.IndexedJoinLeaves

/-!
# Prepared join selection, descent and terminal lookup allowances

Every terminal prefix is charged, including those rejected by feasibility.
The branch-tree identity derives their total from actual delivered keys.
Selection tests, binary comparisons and cursor-navigation allowances remain
separate from index preparation, annotation traversal and publication.

The terminal allowance reads all factor indexes. Short-circuit existence may
read fewer, so this is an upper allowance rather than an exact native trace.
Layout tests count finite-layout comparisons; scalar equality work within a
layout and machine/cache costs are not reclassified as unit operations here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.PreparedJoinLedger

open ConjunctiveRegionProvenance GenericJoinRegions IndexedJoinRegions PreparedJoinRegions
open Mettapedia.Machines.Cursor
open IndexedIntersection

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

def leafComparisons (stored : List (StoredFactor n Value Id)) (outside : Value)
    (environment : Environment n Value) : Nat :=
  (stored.map (fun factor =>
    (PrefixRunIndex.query (PreparedFactorIndex.columns factor.source).length factor.leaves.index outside
      (PreparedFactorIndex.targets factor.source (valuation outside environment))).2)).sum

def leafCoefficient (stored : List (StoredFactor n Value Id)) : Nat :=
  (stored.map (fun factor => factor.source.arity)).sum

theorem leafComparisons_bound (values : Finset Value) (stored : List (StoredFactor n Value Id))
    (outside : Value) (environment : Environment n Value) :
    leafComparisons stored outside environment ≤
      leafCoefficient stored * (seekBudget (maximumWidth values (sources stored)) + 1) := by
  have perFactor : ∀ factor ∈ stored,
      (PrefixRunIndex.query (PreparedFactorIndex.columns factor.source).length factor.leaves.index outside
        (PreparedFactorIndex.targets factor.source (valuation outside environment))).2 ≤
      factor.source.arity * (seekBudget (maximumWidth values (sources stored)) + 1) := by
    intro factor member
    have own := factor.leaves.query_bound (valuation outside environment) outside
    have rowBound : factor.source.rows.length ≤ maximumWidth values (sources stored) := by
      have inFactors : factor.source ∈ sources stored := List.mem_map.mpr ⟨factor, member, rfl⟩
      exact (List.le_sum_of_mem (List.mem_map.mpr ⟨factor.source, inFactors, rfl⟩ :
        factor.source.rows.length ∈ (sources stored).map (fun f => f.rows.length))).trans
        (Nat.le_add_left _ _)
    have logarithm := Nat.log_mono_right (b := 2) rowBound
    have budget : seekBudget factor.source.rows.length + 1 ≤ seekBudget (maximumWidth values (sources stored)) + 1 := by
      unfold seekBudget
      omega
    exact own.trans (Nat.mul_le_mul_left _ budget)
  have summed := List.sum_le_sum (l := stored) perFactor
  simpa only [leafComparisons, leafCoefficient, List.sum_map_mul_right] using summed

def nodes {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) : List (Fin n) → Environment n Value → Nat
  | [], _ => 1
  | coordinate :: rest, environment =>
      1 + (((CyclicJoinRegions.execute (stage domain stored outside environment coordinate)).sort (· ≤ ·)).map
        (fun value => nodes domain stored outside rest (Function.update environment coordinate (some value)))).sum

theorem nodes_eq_delivered_add_one {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value) (order : List (Fin n))
    (environment : Environment n Value) :
    nodes domain stored outside order environment =
      1 + IndexedMultiwayProjection.delivered
        (CyclicJoinRegions.cyclicStages values (sources stored) (stage domain stored outside) order environment) := by
  induction order generalizing environment with
  | nil => rfl
  | cons coordinate rest ih =>
      have childCount := (stage domain stored outside environment coordinate).output_length
      simp only [nodes, CyclicJoinRegions.cyclicStages, ih,
        IndexedMultiwayProjection.delivered, List.map_cons, List.sum_cons,
        List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
        List.sum_map_add, List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
        CyclicJoinRegions.execute_exact]
      rw [childCount]

def boundaryAllowance {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value) :
    List (Fin n) → Environment n Value → Nat
  | [], environment => stored.length + leafComparisons stored outside environment
  | coordinate :: rest, environment =>
      selectionTests stored environment coordinate + descentComparisons domain stored outside environment coordinate +
      (((CyclicJoinRegions.execute (stage domain stored outside environment coordinate)).sort (· ≤ ·)).map
        (fun value => boundaryAllowance domain stored outside rest (Function.update environment coordinate (some value)))).sum

def nodeBudget (values : Finset Value) (stored : List (StoredFactor n Value Id)) : Nat :=
  stored.length + selectionCoefficient stored +
    (descentCoefficient stored + leafCoefficient stored) * (seekBudget (maximumWidth values (sources stored)) + 1)

theorem boundaryAllowance_le_nodes {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value) (order : List (Fin n))
    (environment : Environment n Value) :
    boundaryAllowance domain stored outside order environment ≤
      nodes domain stored outside order environment * nodeBudget values stored := by
  induction order generalizing environment with
  | nil =>
      have terminal := leafComparisons_bound values stored outside environment
      simp only [boundaryAllowance, nodes, one_mul, nodeBudget]
      nlinarith
  | cons coordinate rest ih =>
      have selection := selectionTests_bound stored environment coordinate
      have descent := descentComparisons_bound domain stored outside environment coordinate
      have children := List.sum_le_sum
        (l := (CyclicJoinRegions.execute (stage domain stored outside environment coordinate)).sort (· ≤ ·))
        (f := fun value => boundaryAllowance domain stored outside rest (Function.update environment coordinate (some value)))
        (g := fun value => nodes domain stored outside rest (Function.update environment coordinate (some value)) * nodeBudget values stored)
        (fun value _ => ih _)
      rw [List.sum_map_mul_right] at children
      simp only [boundaryAllowance, nodes]
      have localBound : selectionTests stored environment coordinate +
          descentComparisons domain stored outside environment coordinate ≤ nodeBudget values stored := by
        unfold nodeBudget
        nlinarith
      nlinarith

/-- Preparation, annotation traversal and final delivery are not hidden in
this fixed-query sum-min/logarithmic navigation-and-boundary allowance. -/
theorem combined_sum_min_bound {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value) (order : List (Fin n))
    (environment : Environment n Value) :
    let width := maximumArity (sources stored)
    let maximum := maximumWidth values (sources stored)
    let visited := CyclicJoinRegions.cyclicStages values (sources stored) (stage domain stored outside) order environment
    CyclicJoinRegions.navigationWork values (sources stored) (stage domain stored outside) order environment +
      boundaryAllowance domain stored outside order environment ≤
        (4 * width + 2 * width ^ 2 + nodeBudget values stored) +
        IndexedMultiwayProjection.sumMin visited *
          (4 * width + 2 * width ^ 2 + 2 * width * (3 * width + 4 + seekBudget maximum) + 1 + nodeBudget values stored) := by
  have navigation := navigation_bound domain stored outside order environment
  have boundaries := boundaryAllowance_le_nodes domain stored outside order environment
  rw [nodes_eq_delivered_add_one] at boundaries
  have delivered := IndexedMultiwayProjection.delivered_le_sumMin
    (CyclicJoinRegions.cyclicStages values (sources stored) (stage domain stored outside) order environment)
  have scaled := Nat.mul_le_mul_right (nodeBudget values stored) delivered
  dsimp only at navigation ⊢
  nlinarith

namespace Controls

open IndexedJoinRegions.Controls

theorem empty_schedule_still_pays_one_terminal :
    nodes (prepareDomain 0 {0, 1}) (prepareFactors ([] : List (Factor (Fin 1) Nat Nat))) 0 []
      (fun _ => none) = 1 := rfl

abbrev crossed : Factor (Fin 1) Nat Nat :=
  ⟨2, fun _ => .variable 0,
    [(40, fun column => if column = 0 then 1 else 2),
     (41, fun column => if column = 0 then 2 else 1)]⟩

theorem rejected_leaf_is_still_charged :
    nodes (prepareDomain 0 {1, 2}) (prepareFactors [crossed]) 0 [0]
      (fun _ => none) = 3 := by
  have projections : domains {1, 2} [crossed] (fun _ => none) 0 = [{1, 2}, {1, 2}, {1, 2}] := by decide +kernel
  have candidateKeys : candidates {1, 2} [crossed] (fun _ => none) 0 = {1, 2} := by
    ext value
    rw [mem_candidates_iff, projections]
    simp
  simp only [nodes, CyclicJoinRegions.execute_exact, Stage.execute_exact, sources_prepare]
  rw [candidateKeys]
  simp

theorem those_leaves_really_fail :
    IndexedJoinLeaves.run (prepareDomain 0 {1, 2}) (prepareFactors [crossed]) 0 [0] (fun _ => none) = ∅ := by
  rw [IndexedJoinLeaves.run_exact, execute_exact, sources_prepare]
  decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.PreparedJoinLedger
