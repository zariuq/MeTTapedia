import Mettapedia.GSLT.Dynamics.FactorProjectionLayout
import Mettapedia.GSLT.Dynamics.CyclicJoinRegions
import Mettapedia.GSLT.Dynamics.PreparedFactorIndex

/-!
# Generic joins over retained prepared projection indexes

Preparation materializes a finite catalogue once per factor and an ascending
domain range once per query. Conditioned stages select stored layouts and
descend their key arrays. No source-row filtering or sorting occurs in these
projection reads. The catalogue's exponential dependence on factor arity is
explicit; this is a complete finite catalogue, not a globally optimal one.

The existing leaf feasibility test remains a separate source-row operation.
The navigation and projection-descent ledgers do not hide that leaf work,
catalogue selection, index construction or result publication.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.PreparedJoinRegions

open ConjunctiveRegionProvenance GenericJoinRegions IndexedJoinRegions
open Mettapedia.Machines.Cursor
open IndexedIntersection

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

structure Domain (values : Finset Value) where
  range : Range Value
  sorted : range.Sorted
  exact : range.view.toFinset = values

def prepareDomain (outside : Value) (values : Finset Value) : Domain values where
  range := Range.ofArray (values.sort (· ≤ ·)).toArray outside
  sorted := ofArray_sorted _ _ (by simpa using values.sortedLT_sort.pairwise)
  exact := by simp [ofArray_view]

def Domain.read {values : Finset Value} (domain : Domain values) (outside : Value)
    (bound : Option Value) : Range Value × Nat :=
  match bound with
  | none => (domain.range, 0)
  | some value =>
      let found := IndexedKeyLookup.lookup domain.range value
      (if found.1.isSome then Range.ofArray #[value] outside else Range.ofArray #[] outside, found.2)

theorem Domain.read_spec {values : Finset Value} (domain : Domain values) (outside : Value)
    (environment : Environment n Value) (coordinate : Fin n) :
    let result := domain.read outside (environment coordinate)
    result.1.Sorted ∧ result.1.view.toFinset = allowed values environment coordinate := by
  cases bound : environment coordinate with
  | none =>
      simp only [Domain.read]
      exact ⟨domain.sorted, by simp [allowed, bound, domain.exact]⟩
  | some value =>
      have present : (IndexedKeyLookup.lookup domain.range value).1.isSome = true ↔ value ∈ values := by
        rw [Option.isSome_iff_ne_none, ne_eq, IndexedKeyLookup.lookup_none_iff _ domain.sorted,
          not_not]
        simp only [← domain.exact, List.mem_toFinset]
      simp only [Domain.read]
      split
      next found =>
        refine ⟨ofArray_sorted _ _ (by simp), ?_⟩
        ext candidate
        have member := present.mp found
        simp only [ofArray_view, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_insert, Finset.notMem_empty, or_false, allowed, Finset.mem_filter, bound,
          Option.some_ne_none, Option.some.injEq, false_or]
        constructor
        · intro same
          subst candidate
          exact ⟨member, rfl⟩
        · rintro ⟨_, same⟩
          exact same.symm
      next absent =>
        refine ⟨ofArray_sorted _ _ (by simp), ?_⟩
        have missing : value ∉ values := fun member => absent (present.mpr member)
        ext candidate
        simp only [ofArray_view, List.toFinset_nil, Finset.notMem_empty, allowed,
          Finset.mem_filter, bound, Option.some_ne_none, Option.some.injEq, false_or, false_iff]
        rintro ⟨member, same⟩
        exact missing (by simpa [same] using member)

theorem Domain.width {values : Finset Value} (domain : Domain values) : domain.range.width = values.card := by
  have count := List.toFinset_card_of_nodup (view_sorted domain.range domain.sorted).nodup
  rw [domain.exact, view_length] at count
  exact count.symm

theorem Domain.read_comparisons {values : Finset Value} (domain : Domain values) (outside : Value)
    (bound : Option Value) (maximum : Nat) (bounded : values.card ≤ maximum) :
    (domain.read outside bound).2 ≤ seekBudget maximum + 1 := by
  cases bound with
  | none => exact Nat.zero_le _
  | some value =>
      exact IndexedKeyLookup.lookup_comparisons domain.range value maximum
        (by rw [domain.width]; exact bounded)

structure StoredFactor (n : Nat) (Value Id : Type) [LinearOrder Value] where
  source : Factor (Fin n) Value Id
  projections : FactorProjectionLayout.Store source
  leaves : PreparedFactorIndex.Prepared source

def prepareFactors (factors : List (Factor (Fin n) Value Id)) : List (StoredFactor n Value Id) :=
  factors.map (fun source => ⟨source, FactorProjectionLayout.prepareStore source, PreparedFactorIndex.prepare source⟩)

def sources (stored : List (StoredFactor n Value Id)) : List (Factor (Fin n) Value Id) :=
  stored.map StoredFactor.source

theorem sources_prepare (factors : List (Factor (Fin n) Value Id)) : sources (prepareFactors factors) = factors := by
  simp [sources, prepareFactors, List.map_map, Function.comp_def]

def factorRanges (factor : StoredFactor n Value Id) (outside : Value)
    (environment : Environment n Value) (coordinate : Fin n) : List (Range Value) :=
  ((List.finRange factor.source.arity).filter
    (fun column => factor.source.pattern column = .variable coordinate)).map
    (fun column => (factor.projections.projection environment outside column).1)

theorem factorRanges_exact (factor : StoredFactor n Value Id) (outside : Value)
    (environment : Environment n Value) (coordinate : Fin n) :
    (factorRanges factor outside environment coordinate).map (fun range => range.view.toFinset) =
      ((List.finRange factor.source.arity).filter
        (fun column => factor.source.pattern column = .variable coordinate)).map
        (projection environment factor.source) := by
  simp only [factorRanges, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro column member
  exact (factor.projections.projection_spec environment outside column).1

def stage {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (environment : Environment n Value) (coordinate : Fin n) :
    Stage values (sources stored) environment coordinate where
  ranges := (domain.read outside (environment coordinate)).1 :: stored.flatMap
    (fun factor => factorRanges factor outside environment coordinate)
  sorted range member := by
    rcases List.mem_cons.mp member with same | member
    · subst range
      exact (domain.read_spec outside environment coordinate).1
    · obtain ⟨factor, _, inRanges⟩ := List.mem_flatMap.mp member
      obtain ⟨column, _, rfl⟩ := List.mem_map.mp inRanges
      exact (factor.projections.projection_spec environment outside column).2.1
  supports := by
    simp only [List.map_cons, List.map_flatMap, (domain.read_spec outside environment coordinate).2,
      factorRanges_exact, domains, sources, List.flatMap_map]

theorem stage_width_bound {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value)
    (environment : Environment n Value) (coordinate : Fin n)
    (range : Range Value) (member : range ∈ (stage domain stored outside environment coordinate).ranges) :
    range.width ≤ maximumWidth values (sources stored) := by
  let prepared := stage domain stored outside environment coordinate
  have inDomains : range.view.toFinset ∈ domains values (sources stored) environment coordinate := by
    rw [← prepared.supports]
    exact List.mem_map.mpr ⟨range, member, rfl⟩
  have cardinal := domain_card_bounded values (sources stored) environment coordinate range.view.toFinset inDomains
  have count := List.toFinset_card_of_nodup (view_sorted range (prepared.sorted range member)).nodup
  rw [count, view_length] at cardinal
  exact cardinal

theorem stage_arity_bound {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value)
    (environment : Environment n Value) (coordinate : Fin n) :
    (stage domain stored outside environment coordinate).ranges.length ≤ maximumArity (sources stored) := by
  have same := congrArg List.length (stage domain stored outside environment coordinate).supports
  simp only [List.length_map] at same
  rw [same]
  exact domains_length_bounded values (sources stored) environment coordinate

def execute {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (environment : Environment n Value) : Finset (Environment n Value) :=
  CyclicJoinRegions.cyclicJoin values (sources stored) (stage domain stored outside) order environment

theorem execute_exact {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (environment : Environment n Value) :
    execute domain stored outside order environment = GenericJoinRegions.reference values (sources stored) order environment :=
  CyclicJoinRegions.cyclicJoin_exact values (sources stored) (stage domain stored outside) order environment

theorem weighted_execute_exact {K : Type} [CommSemiring K]
    {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (tag : Id → K) (environment : Environment n Value) :
    (∑ result ∈ execute domain stored outside (List.finRange n) environment,
      factorized tag (valuation outside result) (sources stored)) =
      ∑ result ∈ GenericJoinRegions.reference values (sources stored) (List.finRange n) environment,
        interpretation tag (witnesses (valuation outside result) (sources stored)) :=
  CyclicJoinRegions.weighted_cyclicJoin_exact tag values (sources stored) (stage domain stored outside) environment outside

theorem navigation_bound {values : Finset Value} (domain : Domain values) (stored : List (StoredFactor n Value Id))
    (outside : Value) (order : List (Fin n)) (environment : Environment n Value) :
    let width := maximumArity (sources stored)
    let maximum := maximumWidth values (sources stored)
    let index := stage domain stored outside
    let visited := CyclicJoinRegions.cyclicStages values (sources stored) index order environment
    CyclicJoinRegions.navigationWork values (sources stored) index order environment ≤
      (4 * width + 2 * width ^ 2) + IndexedMultiwayProjection.sumMin visited *
        (4 * width + 2 * width ^ 2 + 2 * width * (3 * width + 4 + seekBudget maximum) + 1) :=
  CyclicJoinRegions.navigation_closed_sum_min_bound values (sources stored) (stage domain stored outside)
    order environment (maximumWidth values (sources stored)) (maximumArity (sources stored))
    (stage_width_bound domain stored outside) (stage_arity_bound domain stored outside)

def descentComparisons {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value)
    (environment : Environment n Value) (coordinate : Fin n) : Nat :=
  (domain.read outside (environment coordinate)).2 + (stored.map (fun factor =>
    (((List.finRange factor.source.arity).filter
      (fun column => factor.source.pattern column = .variable coordinate)).map
      (fun column => (factor.projections.projection environment outside column).2)).sum)).sum

def descentCoefficient (stored : List (StoredFactor n Value Id)) : Nat :=
  1 + (stored.map (fun factor => factor.source.arity ^ 2)).sum

theorem descentComparisons_bound {values : Finset Value} (domain : Domain values)
    (stored : List (StoredFactor n Value Id)) (outside : Value)
    (environment : Environment n Value) (coordinate : Fin n) :
    descentComparisons domain stored outside environment coordinate ≤
      descentCoefficient stored * (seekBudget (maximumWidth values (sources stored)) + 1) := by
  let maximum := maximumWidth values (sources stored)
  have domainBound : values.card ≤ maximum := Nat.le_add_right _ _
  have domainCharge := domain.read_comparisons outside (environment coordinate) maximum domainBound
  have factorBound : ∀ factor ∈ stored,
      (((List.finRange factor.source.arity).filter
        (fun column => factor.source.pattern column = .variable coordinate)).map
        (fun column => (factor.projections.projection environment outside column).2)).sum ≤
      factor.source.arity ^ 2 * (seekBudget maximum + 1) := by
    intro factor member
    have rowBound : factor.source.rows.length ≤ maximum := by
      have inFactors : factor.source ∈ sources stored := List.mem_map.mpr ⟨factor, member, rfl⟩
      have summed := List.le_sum_of_mem (List.mem_map.mpr ⟨factor.source, inFactors, rfl⟩ :
        factor.source.rows.length ∈ (sources stored).map (fun f => f.rows.length))
      exact summed.trans (Nat.le_add_left _ _)
    have logarithm := Nat.log_mono_right (b := 2) rowBound
    have perColumn : ∀ column ∈ (List.finRange factor.source.arity).filter
        (fun column => factor.source.pattern column = .variable coordinate),
        (factor.projections.projection environment outside column).2 ≤
          factor.source.arity * (seekBudget maximum + 1) := by
      intro column inColumns
      have bound := (factor.projections.projection_spec environment outside column).2.2.2
      have depth : seekBudget factor.source.rows.length + 1 ≤ seekBudget maximum + 1 := by
        unfold seekBudget
        omega
      exact bound.trans (Nat.mul_le_mul_left _ depth)
    have summed := List.sum_le_sum (l := (List.finRange factor.source.arity).filter
      (fun column => factor.source.pattern column = .variable coordinate)) perColumn
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at summed
    have count := List.length_filter_le (fun column => factor.source.pattern column = .variable coordinate)
      (List.finRange factor.source.arity)
    rw [List.length_finRange] at count
    have scaled := Nat.mul_le_mul_right (factor.source.arity * (seekBudget maximum + 1)) count
    nlinarith
  have summed := List.sum_le_sum (l := stored) factorBound
  rw [List.sum_map_mul_right] at summed
  unfold descentComparisons descentCoefficient
  change _ ≤ (1 + _) * (seekBudget maximum + 1)
  nlinarith

/-- Selection is a query-shape cost, separate from data-key comparisons. -/
def selectionTests (stored : List (StoredFactor n Value Id))
    (environment : Environment n Value) (coordinate : Fin n) : Nat :=
  (stored.map (fun factor => (((List.finRange factor.source.arity).filter
    (fun column => factor.source.pattern column = .variable coordinate)).map
    (fun column => FactorProjectionLayout.selectionTests factor.projections.entries
      (FactorProjectionLayout.sourceLayout factor.source environment column))).sum)).sum

def selectionCoefficient (stored : List (StoredFactor n Value Id)) : Nat :=
  (stored.map (fun factor => factor.source.arity * factor.projections.entries.length)).sum

theorem selectionTests_bound (stored : List (StoredFactor n Value Id))
    (environment : Environment n Value) (coordinate : Fin n) :
    selectionTests stored environment coordinate ≤ selectionCoefficient stored := by
  apply List.sum_le_sum
  intro factor member
  have perColumn : ∀ column ∈ (List.finRange factor.source.arity).filter
      (fun column => factor.source.pattern column = .variable coordinate),
      FactorProjectionLayout.selectionTests factor.projections.entries
        (FactorProjectionLayout.sourceLayout factor.source environment column) ≤ factor.projections.entries.length :=
    fun column _ => FactorProjectionLayout.selectionTests_bound _ _
  have summed := List.sum_le_sum (l := (List.finRange factor.source.arity).filter
    (fun column => factor.source.pattern column = .variable coordinate)) perColumn
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at summed
  have count := List.length_filter_le (fun column => factor.source.pattern column = .variable coordinate)
    (List.finRange factor.source.arity)
  rw [List.length_finRange] at count
  exact summed.trans (Nat.mul_le_mul_right _ count)

namespace Controls

open IndexedJoinRegions.Controls

theorem path_occurrences_preserved :
    (execute (prepareDomain 0 {0, 1, 2}) (prepareFactors path) 0 [0, 1, 2] (fun _ => none)).card = 2 ∧
    (∑ environment ∈ execute (prepareDomain 0 {0, 1, 2}) (prepareFactors path) 0
        [0, 1, 2] (fun _ => none), factorized (fun _ => (1 : Nat)) (valuation 0 environment) path) = 4 := by
  simp only [execute_exact, sources_prepare]
  decide +kernel

theorem repeated_variables_not_independent :
    execute (prepareDomain 0 {1, 2}) (prepareFactors [GenericJoinRegions.Controls.repeatedCoordinate]) 0
      [0] (fun _ => none) = ∅ := by
  rw [execute_exact, sources_prepare]
  decide +kernel

theorem captured_value_outside_domain_has_no_answer :
    execute (prepareDomain 0 {0, 1, 2, 3}) (prepareFactors clique) 0 [0, 1, 2, 3]
      (fun _ => some 9) = ∅ := by
  rw [execute_exact, sources_prepare]
  decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.PreparedJoinRegions
