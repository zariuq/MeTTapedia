import Mettapedia.GSLT.Dynamics.GenericJoinRegions
import Mettapedia.Machines.Cursor.IndexedMultiwayProjection

/-!
# Indexed projection routes for arbitrary finite conjunctive queries

Prepared stages carry sorted random-access ranges and an exact relationship
to the source query's conditioned projections. The supplied builder really
constructs these arrays from the source rows. Its preparation scans are not
part of the indexed-navigation bound and must be accounted for separately.

The worker binds variables using minimum-projection probing. Its support is
proved equal to the existing leapfrog route, hence to exhaustive source
enumeration. The independent occurrence-polynomial interpretation survives
this change of route. A recursive stage ledger records the prefixes actually
visited, rather than assuming that every Cartesian prefix is visited.

The finite sum-min bound is for this indexed-probing route. It does not prove
the native rotating cursor's arbitrary-width trace correspondence, constant
physical lookup cost, cheap index construction, or an AGM bound.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.IndexedJoinRegions

open ConjunctiveRegionProvenance GenericJoinRegions
open Mettapedia.Machines.Cursor
open IndexedIntersection

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

structure Stage (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (environment : Environment n Value) (coordinate : Fin n) where
  ranges : List (Range Value)
  sorted : ∀ r ∈ ranges, r.Sorted
  supports : ranges.map (fun r => r.view.toFinset) =
    domains domain factors environment coordinate

theorem Stage.nonempty {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) : stage.ranges ≠ [] := by
  intro empty
  have impossible := stage.supports
  simp [empty, domains] at impossible

/-- Concrete preparation is separate from the subsequently reusable range
reader. Sorting and source-row filtering occur here, not inside a seek. -/
def prepare (outside : Value) (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (environment : Environment n Value)
    (coordinate : Fin n) : Stage domain factors environment coordinate where
  ranges := (domains domain factors environment coordinate).map fun support =>
    Range.ofArray (support.sort (· ≤ ·)).toArray outside
  sorted r member := by
    obtain ⟨support, _, rfl⟩ := List.mem_map.mp member
    apply ofArray_sorted
    simpa using support.sortedLT_sort.pairwise
  supports := by simp [List.map_map, Function.comp_def, ofArray_view]

def maximumWidth (domain : Finset Value) (factors : List (Factor (Fin n) Value Id)) : Nat :=
  domain.card + (factors.map fun factor => factor.rows.length).sum

def maximumArity (factors : List (Factor (Fin n) Value Id)) : Nat :=
  1 + (factors.map Factor.arity).sum

theorem projection_card_le_rows (environment : Environment n Value)
    (factor : Factor (Fin n) Value Id) (column : Fin factor.arity) :
    (projection environment factor column).card ≤ factor.rows.length := by
  unfold projection
  exact (List.toFinset_card_le _).trans
    ((List.length_map ..).le.trans (List.length_filter_le _ _))

theorem domain_card_bounded (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (environment : Environment n Value) (coordinate : Fin n)
    (support : Finset Value) (member : support ∈ domains domain factors environment coordinate) :
    support.card ≤ maximumWidth domain factors := by
  simp only [domains, List.mem_cons, List.mem_flatMap, List.mem_map] at member
  rcases member with rfl | ⟨factor, present, column, _, rfl⟩
  · exact (Finset.card_filter_le _ _).trans (Nat.le_add_right _ _)
  · have rowBound := List.le_sum_of_mem
      (List.mem_map.mpr ⟨factor, present, rfl⟩ : factor.rows.length ∈
        factors.map fun f => f.rows.length)
    exact (projection_card_le_rows environment factor column).trans
      (rowBound.trans (Nat.le_add_left _ _))

theorem domains_length_bounded (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (environment : Environment n Value)
    (coordinate : Fin n) :
    (domains domain factors environment coordinate).length ≤ maximumArity factors := by
  unfold domains maximumArity
  simp only [List.length_cons, List.length_flatMap, List.length_map]
  have summed := List.sum_le_sum (l := factors)
    (f := fun factor => ((List.finRange factor.arity).filter
      (fun column => factor.pattern column = .variable coordinate)).length)
    (g := Factor.arity) (fun factor _ =>
      (List.length_filter_le _ _).trans_eq List.length_finRange)
  omega

theorem prepared_width_bounded (outside : Value) (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (environment : Environment n Value)
    (coordinate : Fin n) (r : Range Value)
    (member : r ∈ (prepare outside domain factors environment coordinate).ranges) :
    r.width ≤ maximumWidth domain factors := by
  obtain ⟨support, present, rfl⟩ := List.mem_map.mp member
  simpa [Range.ofArray, Range.width] using
    domain_card_bounded domain factors environment coordinate support present

theorem prepared_arity_bounded (outside : Value) (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (environment : Environment n Value)
    (coordinate : Fin n) :
    (prepare outside domain factors environment coordinate).ranges.length ≤ maximumArity factors := by
  simpa [prepare] using domains_length_bounded domain factors environment coordinate

theorem Stage.selected {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) :
    ∃ seed, IndexedMultiwayProjection.selected stage.ranges = some seed := by
  cases chosen : IndexedMultiwayProjection.selected stage.ranges with
  | some seed => exact ⟨seed, rfl⟩
  | none => exact False.elim (stage.nonempty (List.argmin_eq_none.mp chosen))

def Stage.attempt {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) : Option (Finset Value) :=
  (IndexedMultiwayProjection.intersect stage.ranges).map (fun result => result.keys.toFinset)

theorem Stage.attempt_exact {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) :
    stage.attempt = some (candidates domain factors environment coordinate) := by
  obtain ⟨seed, chosen⟩ := stage.selected
  have scanned := IndexedMultiwayProjection.scan_keys seed.read stage.ranges seed.width seed.lo
  have sourceMember := IndexedMultiwayProjection.selected_member chosen
  have same : (IndexedMultiwayProjection.scan seed.read stage.ranges seed.width seed.lo).keys.toFinset =
      candidates domain factors environment coordinate := by
    ext value
    rw [List.mem_toFinset, scanned, List.mem_filter,
      IndexedMultiwayProjection.probeAll_exact stage.ranges value stage.sorted, mem_candidates_iff,
      ← stage.supports]
    simp only [List.forall_mem_map, List.mem_toFinset]
    exact and_iff_right_of_imp (fun all => all seed sourceMember)
  simp [Stage.attempt, IndexedMultiwayProjection.intersect, chosen, same]

/-- The generic fallback is retained even though this certified stage proves
that its own worker completes. A refusal never means an empty projection. -/
def Stage.execute {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) : Finset Value :=
  stage.attempt.getD (candidates domain factors environment coordinate)

theorem Stage.execute_exact {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) :
    stage.execute = candidates domain factors environment coordinate := by
  rw [Stage.execute, stage.attempt_exact]
  rfl

theorem Stage.output_length {domain : Finset Value} {factors : List (Factor (Fin n) Value Id)}
    {environment : Environment n Value} {coordinate : Fin n}
    (stage : Stage domain factors environment coordinate) :
    (stage.execute.sort (· ≤ ·)).length = (IndexedMultiwayProjection.keys stage.ranges).length := by
  obtain ⟨seed, chosen⟩ := stage.selected
  have same : stage.execute = (IndexedMultiwayProjection.keys stage.ranges).toFinset := by
    simp [Stage.execute, Stage.attempt, IndexedMultiwayProjection.keys,
      IndexedMultiwayProjection.intersect, chosen]
  rw [same, Finset.length_sort]
  exact List.toFinset_card_of_nodup
    (IndexedMultiwayProjection.keys_sorted stage.ranges stage.sorted).nodup

abbrev Index (domain : Finset Value) (factors : List (Factor (Fin n) Value Id)) :=
  (environment : Environment n Value) → (coordinate : Fin n) →
    Stage domain factors environment coordinate

def indexedJoin (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) :
    List (Fin n) → Environment n Value → Finset (Environment n Value)
  | [], environment => if feasible environment factors then {environment} else ∅
  | coordinate :: rest, environment =>
      (index environment coordinate).execute.biUnion fun value =>
        indexedJoin domain factors index rest (Function.update environment coordinate (some value))

theorem indexedJoin_eq_generic (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (order : List (Fin n)) (environment : Environment n Value) :
    indexedJoin domain factors index order environment = genericJoin domain factors order environment := by
  induction order generalizing environment with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [indexedJoin, genericJoin, Stage.execute_exact, ih]

theorem indexedJoin_exact (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (order : List (Fin n)) (environment : Environment n Value) :
    indexedJoin domain factors index order environment = reference domain factors order environment := by
  rw [indexedJoin_eq_generic, genericJoin_exact]

theorem weighted_indexedJoin_exact {K : Type} [CommSemiring K]
    (tag : Id → K) (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (before : Environment n Value) (outside : Value) :
    (∑ environment ∈ indexedJoin domain factors index (List.finRange n) before,
      factorized tag (valuation outside environment) factors) =
    ∑ environment ∈ reference domain factors (List.finRange n) before,
      interpretation tag (witnesses (valuation outside environment) factors) := by
  rw [indexedJoin_eq_generic]
  exact weighted_genericJoin_exact tag domain factors before outside

/-- This log follows the worker's branches. It is an audit object, not an
obligation to retain a materialized execution history at runtime. -/
def visitedStages (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) : List (Fin n) → Environment n Value → List (List (Range Value))
  | [], _ => []
  | coordinate :: rest, environment =>
      let stage := index environment coordinate
      stage.ranges :: (stage.execute.sort (· ≤ ·)).flatMap fun value =>
        visitedStages domain factors index rest (Function.update environment coordinate (some value))

def navigationWork (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) : List (Fin n) → Environment n Value → Nat
  | [], _ => 0
  | coordinate :: rest, environment =>
      let stage := index environment coordinate
      IndexedMultiwayProjection.workBound stage.ranges + ((stage.execute.sort (· ≤ ·)).map fun value =>
        navigationWork domain factors index rest (Function.update environment coordinate (some value))).sum

theorem navigationWork_eq_ledger (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (index : Index domain factors)
    (order : List (Fin n)) (environment : Environment n Value) :
    navigationWork domain factors index order environment =
      ((visitedStages domain factors index order environment).map IndexedMultiwayProjection.workBound).sum := by
  induction order generalizing environment with
  | nil => rfl
  | cons coordinate rest ih =>
      simp [navigationWork, visitedStages, ih,
        List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def]

theorem visited_bounded (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (order : List (Fin n)) (environment : Environment n Value)
    (P : List (Range Value) → Prop) (holds : ∀ env coordinate, P (index env coordinate).ranges) :
    ∀ stage ∈ visitedStages domain factors index order environment, P stage := by
  induction order generalizing environment with
  | nil => simp [visitedStages]
  | cons coordinate rest ih =>
      intro stage member
      simp only [visitedStages, List.mem_cons, List.mem_flatMap] at member
      rcases member with rfl | ⟨value, _, later⟩
      · exact holds environment coordinate
      · exact ih _ stage later

/-- An explicit sum-min/log bound for the indexed worker's visited prefixes.
Preparation, leaf feasibility/provenance, result assembly and publication are
separate ledgers. No hidden unit-cost row scan is admitted by this theorem. -/
theorem navigation_sum_min_bound (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (index : Index domain factors)
    (order : List (Fin n)) (environment : Environment n Value) (maximum width : Nat)
    (bounded : ∀ env coordinate, ∀ r ∈ (index env coordinate).ranges, r.width ≤ maximum)
    (arity : ∀ env coordinate, (index env coordinate).ranges.length ≤ width) :
    let stages := visitedStages domain factors index order environment
    navigationWork domain factors index order environment ≤ stages.length * width +
      IndexedMultiwayProjection.sumMin stages * (1 + width * (2 + seekBudget maximum)) + IndexedMultiwayProjection.delivered stages := by
  rw [navigationWork_eq_ledger]
  exact IndexedMultiwayProjection.sum_min_work_bound _ maximum width
    (visited_bounded domain factors index order environment _ bounded)
    (visited_bounded domain factors index order environment _ arity)

/-- Each non-root stage is reached through a key actually delivered by its
parent. Even unsuccessful prefixes are accounted for by that delivery. -/
theorem visited_count_le_delivered (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (index : Index domain factors)
    (order : List (Fin n)) (environment : Environment n Value) :
    (visitedStages domain factors index order environment).length ≤
      1 + IndexedMultiwayProjection.delivered
        (visitedStages domain factors index order environment) := by
  induction order generalizing environment with
  | nil => simp [visitedStages, IndexedMultiwayProjection.delivered]
  | cons coordinate rest ih =>
      let stage := index environment coordinate
      let children := stage.execute.sort (· ≤ ·)
      have childrenBound := List.sum_le_sum (l := children)
        (f := fun value =>
          (visitedStages domain factors index rest (Function.update environment coordinate (some value))).length)
        (g := fun value => 1 + IndexedMultiwayProjection.delivered
          (visitedStages domain factors index rest (Function.update environment coordinate (some value))))
        (fun value _ => ih _)
      have count := stage.output_length
      simp only [visitedStages, List.length_cons, List.length_flatMap]
      change _ ≤ 1 + IndexedMultiwayProjection.delivered
        (stage.ranges :: children.flatMap _)
      simp only [IndexedMultiwayProjection.delivered, List.map_cons, List.sum_cons,
        List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
      simp only [IndexedMultiwayProjection.delivered, List.sum_map_add, List.map_const',
        List.sum_replicate, smul_eq_mul, mul_one] at childrenBound
      change children.length = _ at count
      dsimp [children, stage] at childrenBound count ⊢
      omega

/-- Setup and intermediate delivery can be absorbed into the sum-min
account because the prefix graph is a tree of actual deliveries. For fixed
query width this is the explicit O((1 + Σ Cᵢ) (1 + log Nmax)) navigation bound.
Final result materialization and index preparation remain separate. -/
theorem navigation_closed_sum_min_bound (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (index : Index domain factors)
    (order : List (Fin n)) (environment : Environment n Value) (maximum width : Nat)
    (bounded : ∀ env coordinate, ∀ r ∈ (index env coordinate).ranges, r.width ≤ maximum)
    (arity : ∀ env coordinate, (index env coordinate).ranges.length ≤ width) :
    let stages := visitedStages domain factors index order environment
    navigationWork domain factors index order environment ≤ width +
      IndexedMultiwayProjection.sumMin stages * (2 + width * (3 + seekBudget maximum)) := by
  have raw := navigation_sum_min_bound domain factors index order environment maximum width bounded arity
  have nodes := visited_count_le_delivered domain factors index order environment
  have delivered := IndexedMultiwayProjection.delivered_le_sumMin
    (visitedStages domain factors index order environment)
  dsimp only at raw ⊢
  have scaled := Nat.mul_le_mul_right width nodes
  have scaledDelivered := Nat.mul_le_mul_right width delivered
  nlinarith

/-- The concrete source-derived array builder discharges the range-size and
query-width premises. Its row scans and sorting remain preparation work. -/
theorem prepared_navigation_bound (outside : Value) (domain : Finset Value)
    (factors : List (Factor (Fin n) Value Id)) (order : List (Fin n))
    (environment : Environment n Value) :
    let index := prepare outside domain factors
    let stages := visitedStages domain factors index order environment
    navigationWork domain factors index order environment ≤ maximumArity factors +
      IndexedMultiwayProjection.sumMin stages *
        (2 + maximumArity factors * (3 + seekBudget (maximumWidth domain factors))) :=
  navigation_closed_sum_min_bound domain factors (prepare outside domain factors) order environment
    (maximumWidth domain factors) (maximumArity factors)
    (prepared_width_bounded outside domain factors) (prepared_arity_bounded outside domain factors)

namespace Portfolio

open ObservationQualified

def region (domain : Finset Value) (factors : List (Factor (Fin n) Value Id))
    (index : Index domain factors) (order : List (Fin n)) :
    CertifiedRegion (GenericJoinRegions.Portfolio.boundary domain factors order) Nat where
  regime := 1
  Artifact := Finset (Environment n Value)
  attempt environment := .committed (indexedJoin domain factors index order environment)
  decode := id
  restores _ _ impossible := by cases impossible
  exact environment _ committed := by
    cases committed
    exact indexedJoin_exact domain factors index order environment

end Portfolio

namespace Controls

def edge {m : Nat} (a b : Fin m) (rows : List (Nat × (Nat × Nat))) : Factor (Fin m) Nat Nat :=
  ⟨2, (fun column => .variable (if column = 0 then a else b)),
    rows.map fun row => (row.1, fun column => if column = 0 then row.2.1 else row.2.2)⟩

def path : List (Factor (Fin 3) Nat Nat) :=
  [edge 0 1 [(10, (0, 1)), (11, (0, 1))], edge 1 2 [(20, (1, 2)), (21, (1, 0))]]

theorem path_preserves_two_keys_four_derivations :
    (indexedJoin {0, 1, 2} path (prepare 0 {0, 1, 2} path) [0, 1, 2] (fun _ => none)).card = 2 ∧
    (∑ environment ∈ indexedJoin {0, 1, 2} path (prepare 0 {0, 1, 2} path)
        [0, 1, 2] (fun _ => none), factorized (fun _ => (1 : Nat)) (valuation 0 environment) path) = 4 := by
  simp only [indexedJoin_exact]
  decide

theorem cyclic_triangle_reuses_source_proof :
    indexedJoin {0, 1, 2} GenericJoinRegions.Controls.triangle
      (prepare 0 {0, 1, 2} GenericJoinRegions.Controls.triangle) [0, 1, 2] (fun _ => none) =
      {fun coordinate => some coordinate.val} := by
  rw [indexedJoin_eq_generic]
  exact GenericJoinRegions.Controls.cyclic_triangle_enumeration

def clique : List (Factor (Fin 4) Nat Nat) :=
  [edge 0 1 [(1, (0, 1)), (2, (0, 1))], edge 0 2 [(3, (0, 2))],
   edge 0 3 [(4, (0, 3))], edge 1 2 [(5, (1, 2))],
   edge 1 3 [(6, (1, 3))], edge 2 3 [(7, (2, 3))]]

theorem clique_enumeration :
    indexedJoin {0, 1, 2, 3} clique (prepare 0 {0, 1, 2, 3} clique) [0, 1, 2, 3]
      (fun _ => none) = {fun coordinate => some coordinate.val} := by
  rw [indexedJoin_exact]
  decide

theorem clique_weight_preserves_duplicate_edge :
    factorized (fun _ => (1 : Nat)) (fun coordinate : Fin 4 => coordinate.val) clique = 2 := by decide

theorem captures_are_not_rebound :
    indexedJoin {0, 1, 2, 3} clique (prepare 0 {0, 1, 2, 3} clique) [0, 1, 2, 3]
      (fun _ => some 0) = ∅ := by
  rw [indexedJoin_exact]
  decide

theorem correlated_holes_not_independent :
    indexedJoin {1, 2} [GenericJoinRegions.Controls.repeatedCoordinate]
      (prepare 0 {1, 2} [GenericJoinRegions.Controls.repeatedCoordinate]) [0] (fun _ => none) = ∅ := by
  rw [indexedJoin_eq_generic]
  exact GenericJoinRegions.Controls.repeated_coordinate_is_not_two_wildcards

theorem changed_relation_cannot_keep_old_projection :
    ¬∃ stage : Stage {0, 1} ([edge (0 : Fin 2) 1 []] : List (Factor (Fin 2) Nat Nat))
      (fun _ => none) 0, stage.ranges.map (fun r => r.view.toFinset) = [{0, 1}, {0}] := by
  rintro ⟨stage, stale⟩
  have impossible := stage.supports
  rw [stale] at impossible
  have distinct : domains ({0, 1} : Finset Nat) [edge (0 : Fin 2) 1 []]
      (fun _ => none) 0 ≠ [{0, 1}, {0}] := by decide
  exact distinct impossible.symm

end Controls

end Mettapedia.GSLT.Dynamics.IndexedJoinRegions
