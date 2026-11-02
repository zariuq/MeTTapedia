import Mettapedia.Algorithms.CountedKeySort
import Mettapedia.Machines.Cursor.ContiguousKeyRuns
import Mettapedia.Machines.Cursor.IndexedKeyTable

/-!
# Prepared occurrence-preserving prefix indexes

Each level groups the current rows by the next authored key projection.
Distinct keys and child indexes are stored in aligned immutable arrays;
leaves retain all occurrence payloads. Queries perform one binary lookup per
level and return a leaf without re-sorting or scanning source rows.

Construction uses counted balanced merge sorting and linear grouping. Its
comparison bound is separate from the subsequently reusable query ledger.
Answers are bag-exact: sorting is not permission to reorder an ordered source
consumer, and the result is not a set of occurrence payloads.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.PrefixRunIndex

open ContiguousKeyRuns
open Mettapedia.Algorithms

variable {Row Key : Type} [LinearOrder Key]

def Index (Row Key : Type) [LinearOrder Key] : Nat → Type
  | 0 => List Row
  | depth + 1 => IndexedKeyTable.Table (Prod.fst : Key × Index Row Key depth → Key)

structure Built (Row Key : Type) [LinearOrder Key] (depth : Nat) where
  index : Index Row Key depth
  comparisons : Nat

def build : (columns : List (Row → Key)) → List Row → Built Row Key columns.length
  | [], source => ⟨source, 0⟩
  | key :: rest, source =>
      let ordered := CountedKeySort.run key source
      let grouped := group key ordered.rows
      let children := grouped.buckets.map (fun bucket => (key bucket.first, build rest bucket.rows))
      let entries := children.map (fun child => (child.1, child.2.index))
      let table := IndexedKeyTable.ofList Prod.fst entries (by
        simpa only [entries, children, grouped, List.pairwise_map] using
          group_keys_sorted key ordered.rows (CountedKeySort.run_spec key source).2.1)
      ⟨table, ordered.comparisons + grouped.comparisons +
        (children.map (fun child => child.2.comparisons)).sum⟩

def query : (depth : Nat) → Index Row Key depth → Key → (Fin depth → Key) → List Row × Nat
  | 0, index, _, _ => (index, 0)
  | depth + 1, index, outside, targets =>
      let found := IndexedKeyTable.lookup index outside (targets 0)
      match found.1 with
      | none => ([], found.2)
      | some child =>
          let remaining := query depth child.2 outside (fun i => targets i.succ)
          (remaining.1, found.2 + remaining.2)

def reference : (columns : List (Row → Key)) → (Fin columns.length → Key) → List Row → List Row
  | [], _, source => source
  | key :: rest, targets, source =>
      reference rest (fun i => targets i.succ) (source.filter (fun row => decide (key row = targets 0)))

theorem reference_empty (columns : List (Row → Key)) (targets : Fin columns.length → Key) :
    reference columns targets [] = [] := by
  induction columns with
  | nil => rfl
  | cons key rest ih => exact ih _

theorem reference_perm (columns : List (Row → Key)) (targets : Fin columns.length → Key)
    (first second : List Row) (permutation : first.Perm second) :
    (reference columns targets first).Perm (reference columns targets second) := by
  induction columns generalizing first second with
  | nil => exact permutation
  | cons key rest ih => exact ih _ _ _ (permutation.filter _)

theorem reference_eq_filter (columns : List (Row → Key))
    (targets : Fin columns.length → Key) (source : List Row) :
    reference columns targets source = source.filter
      (fun row => decide (∀ i : Fin columns.length, columns[i] row = targets i)) := by
  induction columns generalizing source with
  | nil => simp [reference]
  | cons key rest ih =>
      rw [reference, ih, List.filter_filter]
      congr 1
      funext row
      apply Bool.eq_iff_iff.mpr
      simp only [List.length_cons, Fin.forall_fin_succ,
        Bool.and_eq_true, decide_eq_true_eq]
      exact and_comm

theorem build_lookup (key : Row → Key) (rest : List (Row → Key)) (source : List Row)
    (outside target : Key) :
    (IndexedKeyTable.lookup (build (key :: rest) source).index outside target).1 =
      (((group key (CountedKeySort.run key source).rows).buckets.find?
        (fun bucket => decide (key bucket.first = target))).map
        (fun bucket => (key bucket.first, (build rest bucket.rows).index))) := by
  dsimp only [build]
  rw [IndexedKeyTable.ofList_lookup]
  simp only [List.find?_map, List.map_map, Function.comp_def]

/-- Every leaf query retains the complete bag of original occurrences whose
key projections match. This compares to direct source filtering. -/
theorem query_exact (columns : List (Row → Key)) (source : List Row)
    (outside : Key) (targets : Fin columns.length → Key) :
    (query columns.length (build columns source).index outside targets).1.Perm
      (reference columns targets source) := by
  induction columns generalizing source with
  | nil => exact List.Perm.refl _
  | cons key rest ih =>
      let ordered := CountedKeySort.run key source
      let buckets := (group key ordered.rows).buckets
      let selected := (buckets.find? (fun bucket => decide (key bucket.first = targets 0)))
      have selectedExact := find_group_exact key (targets 0) ordered.rows
        (CountedKeySort.run_spec key source).2.1
      have preparation := reference_perm (key :: rest) targets ordered.rows source
        (CountedKeySort.run_spec key source).1
      have localResult : (query (rest.length + 1) (build (key :: rest) source).index outside targets).1.Perm
          (reference rest (fun i => targets i.succ) ((selected.map Bucket.rows).getD [])) := by
        rw [query, build_lookup]
        dsimp only [selected, buckets, ordered]
        cases found : (group key (CountedKeySort.run key source).rows).buckets.find?
            (fun bucket => decide (key bucket.first = targets 0)) with
        | none => simp only [Option.map_none, Option.getD_none, reference_empty]; exact List.Perm.refl _
        | some bucket => exact ih bucket.rows _
      change (selected.map Bucket.rows).getD [] = _ at selectedExact
      rw [selectedExact] at localResult
      exact localResult.trans preparation

theorem bucket_size_le (key : Row → Key) (source : List Row) (bucket : Bucket Row)
    (member : bucket ∈ (group key source).buckets) : bucket.rows.length ≤ source.length := by
  rw [← group_rows_count key source]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨bucket, member, rfl⟩)

theorem build_comparisons (columns : List (Row → Key)) (source : List Row) :
    (build columns source).comparisons ≤
      columns.length * source.length * (CountedKeySort.depth source.length + 1) := by
  induction columns generalizing source with
  | nil => simp [build]
  | cons key rest ih =>
      let ordered := CountedKeySort.run key source
      let buckets := (group key ordered.rows).buckets
      have sorting := (CountedKeySort.run_spec key source).2.2
      have length : ordered.rows.length = source.length := (CountedKeySort.run_spec key source).1.length_eq
      have grouping : (group key ordered.rows).comparisons ≤ source.length := by
        rw [group_comparisons, length]
        omega
      have childBound : ∀ bucket ∈ buckets, (build rest bucket.rows).comparisons ≤
          bucket.rows.length * (rest.length * (CountedKeySort.depth source.length + 1)) := by
        intro bucket member
        have localBound := ih bucket.rows
        have size : bucket.rows.length ≤ source.length := by
          rw [← length]
          exact bucket_size_le key ordered.rows bucket member
        have logarithm := Nat.log_mono_right (b := 2) size
        have depth : CountedKeySort.depth bucket.rows.length + 1 ≤ CountedKeySort.depth source.length + 1 := by
          unfold CountedKeySort.depth
          omega
        have scaled := Nat.mul_le_mul_left (rest.length * bucket.rows.length) depth
        nlinarith
      have children := List.sum_le_sum (l := buckets) childBound
      rw [List.sum_map_mul_right] at children
      have sizes : (buckets.map (fun bucket => bucket.rows.length)).sum = source.length := by
        rw [group_rows_count, length]
      rw [sizes] at children
      change ordered.comparisons + (group key ordered.rows).comparisons +
        ((buckets.map fun bucket => (key bucket.first, build rest bucket.rows)).map
          (fun child => child.2.comparisons)).sum ≤ _
      simp only [List.map_map, Function.comp_def, List.length_cons]
      change ordered.comparisons ≤ source.length * CountedKeySort.depth source.length at sorting
      nlinarith

theorem root_keys_bounded (key : Row → Key) (rest : List (Row → Key)) (source : List Row) :
    (build (key :: rest) source).index.keys.size ≤ source.length := by
  have bound := group_bucket_count key (CountedKeySort.run key source).rows
  have length := (CountedKeySort.run_spec key source).1.length_eq
  simpa [build, IndexedKeyTable.ofList, length] using bound

theorem query_comparisons (columns : List (Row → Key)) (source : List Row)
    (outside : Key) (targets : Fin columns.length → Key) (maximum : Nat)
    (bounded : source.length ≤ maximum) :
    (query columns.length (build columns source).index outside targets).2 ≤
      columns.length * (IndexedIntersection.seekBudget maximum + 1) := by
  induction columns generalizing source with
  | nil => simp [query]
  | cons key rest ih =>
      have keysBound := (root_keys_bounded key rest source).trans bounded
      have logarithm := Nat.log_mono_right (b := 2) keysBound
      have rootCharge := IndexedKeyTable.lookup_comparisons (build (key :: rest) source).index
        outside (targets 0)
      have charged : (IndexedKeyTable.lookup (build (key :: rest) source).index outside (targets 0)).2 ≤
          IndexedIntersection.seekBudget maximum + 1 := by
        unfold IndexedIntersection.seekBudget at *
        omega
      simp only [List.length_cons]
      rw [query, build_lookup]
      cases found : (group key (CountedKeySort.run key source).rows).buckets.find?
          (fun bucket => decide (key bucket.first = targets 0)) with
      | none =>
          simp only [Option.map_none]
          nlinarith
      | some bucket =>
          have member := List.mem_of_find?_eq_some found
          have size := bucket_size_le key (CountedKeySort.run key source).rows bucket member
          rw [(CountedKeySort.run_spec key source).1.length_eq] at size
          have childCharge := ih bucket.rows (fun i => targets i.succ) (size.trans bounded)
          simp only [Option.map_some]
          nlinarith

def keySlots : (depth : Nat) → Index Row Key depth → Nat
  | 0, _ => 0
  | depth + 1, index => index.keys.size +
      (index.values.toList.map (fun child => keySlots depth child.2)).sum

def leafOccurrences : (depth : Nat) → Index Row Key depth → Nat
  | 0, index => index.length
  | depth + 1, index =>
      (index.values.toList.map (fun child => leafOccurrences depth child.2)).sum

/-- Rows are retained at leaves, not copied into every completed index
level. Distinct-key/child slots are bounded by depth times source size. -/
theorem build_storage (columns : List (Row → Key)) (source : List Row) :
    leafOccurrences columns.length (build columns source).index = source.length ∧
      keySlots columns.length (build columns source).index ≤ columns.length * source.length := by
  induction columns generalizing source with
  | nil => simp [build, leafOccurrences, keySlots]
  | cons key rest ih =>
      let ordered := CountedKeySort.run key source
      let buckets := (group key ordered.rows).buckets
      have length : ordered.rows.length = source.length := (CountedKeySort.run_spec key source).1.length_eq
      have rowCount : (buckets.map (fun bucket => bucket.rows.length)).sum = source.length := by
        rw [group_rows_count, length]
      have bucketCount : buckets.length ≤ source.length := by
        exact (group_bucket_count key ordered.rows).trans_eq length
      constructor
      · simp only [List.length_cons, leafOccurrences]
        dsimp only [build, IndexedKeyTable.ofList]
        simp only [List.map_map, Function.comp_def]
        change (buckets.map (fun bucket => leafOccurrences rest.length (build rest bucket.rows).index)).sum = _
        have equal : buckets.map (fun bucket => leafOccurrences rest.length (build rest bucket.rows).index) =
            buckets.map (fun bucket => bucket.rows.length) := by
          apply List.map_congr_left
          intro bucket member
          exact (ih bucket.rows).1
        rw [equal, rowCount]
      · simp only [List.length_cons, keySlots]
        dsimp only [build, IndexedKeyTable.ofList]
        simp only [List.size_toArray, List.length_map, List.map_map, Function.comp_def]
        change buckets.length + (buckets.map (fun bucket => keySlots rest.length (build rest bucket.rows).index)).sum ≤ _
        have children := List.sum_le_sum (l := buckets)
          (f := fun bucket => keySlots rest.length (build rest bucket.rows).index)
          (g := fun bucket => rest.length * bucket.rows.length)
          (fun bucket _ => (ih bucket.rows).2)
        rw [List.sum_map_mul_left, rowCount] at children
        nlinarith

namespace Controls

def source : List (Nat × Nat × Nat) := [(2, 1, 20), (1, 3, 10), (2, 1, 21), (1, 4, 11)]
def columns : List ((Nat × Nat × Nat) → Nat) := [Prod.fst, fun row => row.2.1]
def targets : Fin 2 → Nat := fun i => if i = 0 then 2 else 1

theorem repeated_leaf_retains_both_ids :
    (query 2 (build columns source).index 0 targets).1 = [(2, 1, 20), (2, 1, 21)] := by decide +kernel

theorem missing_second_key_is_empty :
    (query 2 (build columns source).index 0 (fun _ => 2)).1 = [] := by decide +kernel

theorem missing_first_key_is_empty :
    (query 2 (build columns source).index 0 (fun _ => 9)).1 = [] := by decide +kernel

theorem empty_relation_stays_empty :
    (query 2 (build columns []).index 0 targets).1 = [] := by decide +kernel

theorem source_filter_is_independent : reference columns targets source = [(2, 1, 20), (2, 1, 21)] := by decide +kernel

theorem leaf_payloads_not_replicated_per_level :
    leafOccurrences 2 (build columns source).index = 4 ∧
      keySlots 2 (build columns source).index = 5 := by decide +kernel

end Controls

end Mettapedia.Machines.Cursor.PrefixRunIndex
