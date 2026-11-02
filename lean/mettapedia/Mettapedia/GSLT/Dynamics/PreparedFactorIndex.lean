import Mettapedia.GSLT.Dynamics.ConjunctiveRegionProvenance
import Mettapedia.Machines.Cursor.PrefixRunIndex

/-!
# Prepared factor indexes and occurrence provenance

Each source factor is indexed once by its physical columns. Full valuations
provide lookup keys through the actual constant/variable pattern. Repeated
variables therefore request the same value in every repeated position.
Leaf payloads retain occurrence identities and duplicates. Summing their
annotations refines the independent authored factor interpretation.

This is a reusable leaf/provenance route. Feeding partial-prefix projections
to generic join navigation is an additional adapter, not implicit here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.PreparedFactorIndex

open ConjunctiveRegionProvenance
open Mettapedia.Machines.Cursor

variable {Var Value Id : Type} [LinearOrder Value]

abbrev Row (factor : Factor Var Value Id) := Id × (Fin factor.arity → Value)

def columns (factor : Factor Var Value Id) : List (Row factor → Value) :=
  List.ofFn (fun column : Fin factor.arity => fun row => row.2 column)

omit [LinearOrder Value] in
theorem columns_length (factor : Factor Var Value Id) : (columns factor).length = factor.arity := by
  simp [columns]

def targets (factor : Factor Var Value Id) (environment : Var → Value)
    (i : Fin (columns factor).length) : Value :=
  (factor.pattern (Fin.cast (columns_length factor) i)).eval environment

omit [LinearOrder Value] in
theorem columns_get (factor : Factor Var Value Id) (i : Fin (columns factor).length) (row : Row factor) :
    (columns factor)[i] row = row.2 (Fin.cast (columns_length factor) i) := by
  change (List.ofFn (fun column : Fin factor.arity => fun value : Row factor => value.2 column))[i.val] row = _
  rw [List.getElem_ofFn]
  rfl

theorem filter_exact (factor : Factor Var Value Id) (environment : Var → Value) :
    PrefixRunIndex.reference (columns factor) (targets factor environment) factor.rows =
      factor.rows.filter (factor.acceptsRow environment) := by
  rw [PrefixRunIndex.reference_eq_filter]
  congr 1
  funext row
  apply Bool.eq_iff_iff.mpr
  simp only [Factor.acceptsRow, decide_eq_true_eq]
  constructor
  · intro matched column
    let i : Fin (columns factor).length := Fin.cast (columns_length factor).symm column
    have atColumn := matched i
    rw [columns_get] at atColumn
    exact atColumn
  · intro matched i
    have atColumn := matched (Fin.cast (columns_length factor) i)
    rw [columns_get]
    exact atColumn

structure Prepared (factor : Factor Var Value Id) where
  index : PrefixRunIndex.Index (Row factor) Value (columns factor).length
  preparationComparisons : Nat
  exact : ∀ environment outside,
    (PrefixRunIndex.query (columns factor).length index outside (targets factor environment)).1.Perm
      (factor.rows.filter (factor.acceptsRow environment))
  query_bound : ∀ environment outside,
    (PrefixRunIndex.query (columns factor).length index outside (targets factor environment)).2 ≤
      factor.arity * (IndexedIntersection.seekBudget factor.rows.length + 1)
  preparation_bound : preparationComparisons ≤ factor.arity * factor.rows.length *
    (Mettapedia.Algorithms.CountedKeySort.depth factor.rows.length + 1)
  occurrence_count : PrefixRunIndex.leafOccurrences (columns factor).length index = factor.rows.length
  key_bound : PrefixRunIndex.keySlots (columns factor).length index ≤ factor.arity * factor.rows.length

def prepare (factor : Factor Var Value Id) : Prepared factor :=
  let built := PrefixRunIndex.build (columns factor) factor.rows
  { index := built.index
    preparationComparisons := built.comparisons
    exact environment outside := by
      have result := PrefixRunIndex.query_exact (columns factor) factor.rows outside (targets factor environment)
      rw [filter_exact] at result
      exact result
    query_bound environment outside := by
      simpa only [columns_length] using
        PrefixRunIndex.query_comparisons (columns factor) factor.rows outside (targets factor environment)
          factor.rows.length le_rfl
    preparation_bound := by
      simpa only [columns_length] using PrefixRunIndex.build_comparisons (columns factor) factor.rows
    occurrence_count := (PrefixRunIndex.build_storage (columns factor) factor.rows).1
    key_bound := by
      simpa only [columns_length] using (PrefixRunIndex.build_storage (columns factor) factor.rows).2 }

def occurrences {factor : Factor Var Value Id} (prepared : Prepared factor)
    (environment : Var → Value) (outside : Value) : List Id :=
  (PrefixRunIndex.query (columns factor).length prepared.index outside (targets factor environment)).1.map Prod.fst

theorem occurrences_exact {factor : Factor Var Value Id} (prepared : Prepared factor)
    (environment : Var → Value) (outside : Value) :
    (occurrences prepared environment outside).Perm (factor.occurrences environment) :=
  (prepared.exact environment outside).map Prod.fst

/-- Existence reads only the retained leaf's empty/nonempty tag. It does not
map every occurrence to an identifier merely to answer a Boolean question. -/
def present {factor : Factor Var Value Id} (prepared : Prepared factor)
    (environment : Var → Value) (outside : Value) : Bool :=
  !(PrefixRunIndex.query (columns factor).length prepared.index outside (targets factor environment)).1.isEmpty

theorem present_exact {factor : Factor Var Value Id} (prepared : Prepared factor)
    (environment : Var → Value) (outside : Value) :
    present prepared environment outside = true ↔
      ∃ row ∈ factor.rows, factor.acceptsRow environment row = true := by
  have permutation := prepared.exact environment outside
  simp only [present, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem]
  constructor
  · rintro ⟨row, member⟩
    exact ⟨row, (List.mem_filter.mp (permutation.mem_iff.mp member)).1,
      (List.mem_filter.mp (permutation.mem_iff.mp member)).2⟩
  · rintro ⟨row, member, matched⟩
    exact ⟨row, permutation.mem_iff.mpr (List.mem_filter.mpr ⟨member, matched⟩)⟩

def weight {K : Type} [CommSemiring K] {factor : Factor Var Value Id}
    (prepared : Prepared factor) (tag : Id → K) (environment : Var → Value) (outside : Value) : K :=
  ((occurrences prepared environment outside).map tag).sum

theorem weight_exact {K : Type} [CommSemiring K] {factor : Factor Var Value Id}
    (prepared : Prepared factor) (tag : Id → K) (environment : Var → Value) (outside : Value) :
    weight prepared tag environment outside = ((factor.occurrences environment).map tag).sum :=
  ((occurrences_exact prepared environment outside).map tag).sum_eq

structure StoredFactor (Var Value Id : Type) [LinearOrder Value] where
  source : Factor Var Value Id
  prepared : Prepared source

def prepareFactors (factors : List (Factor Var Value Id)) : List (StoredFactor Var Value Id) :=
  factors.map (fun factor => ⟨factor, prepare factor⟩)

def evaluate {K : Type} [CommSemiring K] (stored : List (StoredFactor Var Value Id))
    (tag : Id → K) (environment : Var → Value) (outside : Value) : K :=
  (stored.map (fun factor => weight factor.prepared tag environment outside)).prod

/-- Prepared leaf retrieval composes with the independent authored witness
interpretation for arbitrary finite conjunctions and commutative weights. -/
theorem evaluate_exact {K : Type} [CommSemiring K] (stored : List (StoredFactor Var Value Id))
    (tag : Id → K) (environment : Var → Value) (outside : Value) :
    evaluate stored tag environment outside =
      interpretation tag (witnesses environment (stored.map StoredFactor.source)) := by
  rw [← factorized_exact]
  simp only [evaluate, factorized, List.map_map, Function.comp_def, weight_exact]

theorem preparedFactors_exact {K : Type} [CommSemiring K]
    (factors : List (Factor Var Value Id)) (tag : Id → K) (environment : Var → Value) (outside : Value) :
    evaluate (prepareFactors factors) tag environment outside = interpretation tag (witnesses environment factors) := by
  rw [evaluate_exact]
  simp [prepareFactors, List.map_map, Function.comp_def]

def retrievalComparisons (stored : List (StoredFactor Var Value Id))
    (environment : Var → Value) (outside : Value) : Nat :=
  (stored.map (fun factor =>
    (PrefixRunIndex.query (columns factor.source).length factor.prepared.index outside
      (targets factor.source environment)).2)).sum

theorem retrieval_comparisons_bound (stored : List (StoredFactor Var Value Id))
    (environment : Var → Value) (outside : Value) :
    retrievalComparisons stored environment outside ≤
      (stored.map (fun factor => factor.source.arity *
        (IndexedIntersection.seekBudget factor.source.rows.length + 1))).sum := by
  apply List.sum_le_sum
  intro factor member
  exact factor.prepared.query_bound environment outside

namespace Controls

def repeated : Factor (Fin 1) Nat Nat :=
  ⟨2, fun _ => .variable 0,
    [(10, fun i => if i = 0 then 1 else 2),
     (11, fun _ => 1), (12, fun _ => 1)]⟩

theorem repeated_variable_rejects_inconsistent_row :
    occurrences (prepare repeated) (fun _ => 1) 0 = [11, 12] := by decide +kernel

theorem duplicate_votes_count_twice : weight (prepare repeated) (fun _ => (1 : Nat)) (fun _ => 1) 0 = 2 := by
  rw [weight_exact]
  decide +kernel

def constantFactor : Factor (Fin 1) Nat Nat :=
  ⟨2, fun i => if i = 0 then .constant 9 else .variable 0,
    [(30, fun i => if i = 0 then 8 else 2), (31, fun i => if i = 0 then 9 else 2)]⟩

theorem constants_are_lookup_coordinates :
    occurrences (prepare constantFactor) (fun _ => 2) 0 = [31] := by decide +kernel

theorem zero_arity_retains_all_occurrences :
    occurrences (prepare (⟨0, Fin.elim0, [(40, Fin.elim0), (41, Fin.elim0)]⟩ : Factor (Fin 0) Nat Nat))
      Fin.elim0 0 = [40, 41] := by decide +kernel

theorem stale_index_is_not_current_absence :
    occurrences (prepare repeated) (fun _ => 1) 0 ≠
      ({ repeated with rows := [] }).occurrences (fun _ => 1) := by decide +kernel

theorem joined_occurrence_weights :
    evaluate (prepareFactors [repeated, constantFactor]) (fun _ => (1 : Nat)) (fun _ => 1) 0 = 0 ∧
    evaluate (prepareFactors [repeated, repeated]) (fun _ => (1 : Nat)) (fun _ => 1) 0 = 4 := by
  simp only [preparedFactors_exact]
  decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.PreparedFactorIndex
