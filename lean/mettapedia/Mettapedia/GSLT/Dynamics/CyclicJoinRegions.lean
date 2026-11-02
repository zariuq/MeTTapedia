import Mettapedia.GSLT.Dynamics.IndexedJoinRegions
import Mettapedia.Machines.Cursor.IndexedCyclicEntry

/-!
# Arbitrary finite joins through rotating indexed cursors

The concrete cyclic worker is a second qualified realization of the same
conditioned projection interface. Its own advance trace, binary comparisons
and initial head-ordering ledger supply the sum-min navigation bound. This
does not identify its work with the minimum-projection probing worker.

The independent authored occurrence semantics still supplies multiplicity
and provenance. Ground-key navigation does not establish an open-term
unification cost bound. Index construction, leaf provenance evaluation and
physical result publication remain separate accounts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CyclicJoinRegions

open ConjunctiveRegionProvenance GenericJoinRegions IndexedJoinRegions
open Mettapedia.Machines.Cursor
open IndexedIntersection

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

def attempt {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) : Option (Finset Value) :=
  (IndexedCyclicEntry.intersect stage.ranges).map (fun result => result.navigation.keys.toFinset)

theorem attempt_exact {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) :
    attempt stage = some (candidates domain factors environment coordinate) := by
  let maximum := (stage.ranges.map Range.width).sum
  have bounded : ∀ range ∈ stage.ranges, range.width ≤ maximum := by
    intro range member
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨range, member, rfl⟩)
  obtain ⟨result, completed, members, _⟩ := IndexedCyclicEntry.intersect_spec stage.ranges
    stage.nonempty stage.sorted maximum bounded
  have exactKeys : result.navigation.keys.toFinset =
      candidates domain factors environment coordinate := by
    ext key
    rw [List.mem_toFinset, members, mem_candidates_iff, ← stage.supports]
    simp only [List.forall_mem_map, List.mem_toFinset]
  simp only [attempt, completed, Option.map_some, exactKeys]

/-- A refusal goes to the source projection, not the empty set. -/
def execute {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) : Finset Value :=
  (attempt stage).getD (candidates domain factors environment coordinate)

theorem execute_exact {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) :
    execute stage = stage.execute := by
  rw [execute, attempt_exact, Stage.execute_exact]
  rfl

def cyclicJoin (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) :
    List (Fin n) → Environment n Value → Finset (Environment n Value)
  | [], environment => if feasible environment factors then {environment} else ∅
  | coordinate :: rest, environment =>
      (execute (index environment coordinate)).biUnion fun value =>
        cyclicJoin domain factors index rest (Function.update environment coordinate (some value))

theorem cyclicJoin_eq_indexed (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (order : List (Fin n)) (environment : Environment n Value) :
    cyclicJoin domain factors index order environment =
      indexedJoin domain factors index order environment := by
  induction order generalizing environment with
  | nil => rfl
  | cons coordinate rest ih => simp only [cyclicJoin, indexedJoin, execute_exact, ih]

theorem cyclicJoin_exact (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (order : List (Fin n)) (environment : Environment n Value) :
    cyclicJoin domain factors index order environment = reference domain factors order environment := by
  rw [cyclicJoin_eq_indexed, indexedJoin_exact]

theorem weighted_cyclicJoin_exact {K : Type} [CommSemiring K]
    (tag : Id → K) (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (before : Environment n Value) (outside : Value) :
    (∑ environment ∈ cyclicJoin domain factors index (List.finRange n) before,
      factorized tag (valuation outside environment) factors) =
    ∑ environment ∈ reference domain factors (List.finRange n) before,
      interpretation tag (witnesses (valuation outside environment) factors) := by
  rw [cyclicJoin_eq_indexed]
  exact weighted_indexedJoin_exact tag domain factors index before outside

def cyclicStages (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) : List (Fin n) → Environment n Value → List (List (Range Value))
  | [], _ => []
  | coordinate :: rest, environment =>
      let stage := index environment coordinate
      stage.ranges :: ((execute stage).sort (· ≤ ·)).flatMap fun value =>
        cyclicStages domain factors index rest (Function.update environment coordinate (some value))

theorem cyclicStages_exact (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (order : List (Fin n)) (environment : Environment n Value) :
    cyclicStages domain factors index order environment =
      visitedStages domain factors index order environment := by
  induction order generalizing environment with
  | nil => rfl
  | cons coordinate rest ih => simp only [cyclicStages, visitedStages, execute_exact, ih]

def navigationWork (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) : List (Fin n) → Environment n Value → Nat
  | [], _ => 0
  | coordinate :: rest, environment =>
      let stage := index environment coordinate
      IndexedCyclicEntry.workBound stage.ranges + (((execute stage).sort (· ≤ ·)).map fun value =>
        navigationWork domain factors index rest (Function.update environment coordinate (some value))).sum

theorem navigationWork_eq_ledger (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (index : Index domain factors)
    (order : List (Fin n)) (environment : Environment n Value) :
    navigationWork domain factors index order environment =
      ((cyclicStages domain factors index order environment).map IndexedCyclicEntry.workBound).sum := by
  induction order generalizing environment with
  | nil => rfl
  | cons coordinate rest ih =>
      simp [navigationWork, cyclicStages, ih,
        List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def]

/-- The family-width factors remain explicit. Fixed query width gives the
sum-min/logarithmic navigation account; it is not a combined-complexity AGM
statement or a claim about constructing the conditioned indexes. -/
theorem navigation_closed_sum_min_bound (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (index : Index domain factors)
    (order : List (Fin n)) (environment : Environment n Value) (maximum width : Nat)
    (bounded : ∀ env coordinate, ∀ range ∈ (index env coordinate).ranges, range.width ≤ maximum)
    (arity : ∀ env coordinate, (index env coordinate).ranges.length ≤ width) :
    let stages := cyclicStages domain factors index order environment
    navigationWork domain factors index order environment ≤ (4 * width + 2 * width ^ 2) +
      IndexedMultiwayProjection.sumMin stages *
        (4 * width + 2 * width ^ 2 + 2 * width * (3 * width + 4 + seekBudget maximum) + 1) := by
  rw [navigationWork_eq_ledger, cyclicStages_exact]
  have raw := IndexedCyclicEntry.sum_min_work_bound
    (visitedStages domain factors index order environment) maximum width
    (visited_bounded domain factors index order environment _ (fun env coordinate => (index env coordinate).nonempty))
    (visited_bounded domain factors index order environment _ (fun env coordinate => (index env coordinate).sorted))
    (visited_bounded domain factors index order environment _ bounded)
    (visited_bounded domain factors index order environment _ arity)
  have nodes := visited_count_le_delivered domain factors index order environment
  have delivered := IndexedMultiwayProjection.delivered_le_sumMin
    (visitedStages domain factors index order environment)
  have scaled := Nat.mul_le_mul_right (4 * width + 2 * width ^ 2) nodes
  have scaledDelivered := Nat.mul_le_mul_right (4 * width + 2 * width ^ 2) delivered
  nlinarith

/-- Source-derived range construction supplies the size premises. Its own
row filtering and sorting are not charged to navigation. -/
theorem prepared_navigation_bound (outside : Value) (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (order : List (Fin n))
    (environment : Environment n Value) :
    let width := maximumArity factors
    let maximum := maximumWidth domain factors
    let index := prepare outside domain factors
    let stages := cyclicStages domain factors index order environment
    navigationWork domain factors index order environment ≤ (4 * width + 2 * width ^ 2) +
      IndexedMultiwayProjection.sumMin stages *
        (4 * width + 2 * width ^ 2 + 2 * width * (3 * width + 4 + seekBudget maximum) + 1) :=
  navigation_closed_sum_min_bound domain factors (prepare outside domain factors) order environment
    (maximumWidth domain factors) (maximumArity factors)
    (prepared_width_bounded outside domain factors) (prepared_arity_bounded outside domain factors)

namespace Portfolio

open ObservationQualified

def region (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (order : List (Fin n)) :
    CertifiedRegion (GenericJoinRegions.Portfolio.boundary domain factors order) Nat where
  regime := 2
  Artifact := Finset (Environment n Value)
  attempt environment := .committed (cyclicJoin domain factors index order environment)
  decode := id
  restores _ _ impossible := by cases impossible
  exact environment _ committed := by
    cases committed
    exact cyclicJoin_exact domain factors index order environment

end Portfolio

namespace Controls

open IndexedJoinRegions.Controls

theorem path_preserves_two_keys_four_derivations :
    (cyclicJoin {0, 1, 2} path (prepare 0 {0, 1, 2} path) [0, 1, 2] (fun _ => none)).card = 2 ∧
    (∑ environment ∈ cyclicJoin {0, 1, 2} path (prepare 0 {0, 1, 2} path)
        [0, 1, 2] (fun _ => none), factorized (fun _ => (1 : Nat)) (valuation 0 environment) path) = 4 := by
  simp only [cyclicJoin_eq_indexed]
  exact IndexedJoinRegions.Controls.path_preserves_two_keys_four_derivations

theorem triangle_three_way_source :
    cyclicJoin {0, 1, 2} GenericJoinRegions.Controls.triangle
      (prepare 0 {0, 1, 2} GenericJoinRegions.Controls.triangle) [0, 1, 2] (fun _ => none) =
      {fun coordinate => some coordinate.val} := by
  rw [cyclicJoin_eq_indexed]
  exact cyclic_triangle_reuses_source_proof

theorem clique_four_source :
    cyclicJoin {0, 1, 2, 3} clique (prepare 0 {0, 1, 2, 3} clique) [0, 1, 2, 3]
      (fun _ => none) = {fun coordinate => some coordinate.val} := by
  rw [cyclicJoin_eq_indexed]
  exact clique_enumeration

theorem captured_variables_still_fixed :
    cyclicJoin {0, 1, 2, 3} clique (prepare 0 {0, 1, 2, 3} clique) [0, 1, 2, 3]
      (fun _ => some 0) = ∅ := by
  rw [cyclicJoin_eq_indexed]
  exact captures_are_not_rebound

theorem repeated_variables_still_correlated :
    cyclicJoin {1, 2} [GenericJoinRegions.Controls.repeatedCoordinate]
      (prepare 0 {1, 2} [GenericJoinRegions.Controls.repeatedCoordinate]) [0] (fun _ => none) = ∅ := by
  rw [cyclicJoin_eq_indexed]
  exact correlated_holes_not_independent

end Controls

end Mettapedia.GSLT.Dynamics.CyclicJoinRegions
