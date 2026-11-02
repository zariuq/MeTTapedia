import Mettapedia.Machines.Cursor.PrefixRunIndex

/-!
# Conditioned projection ranges from prepared prefix indexes

A prepared index stores the conditioning columns before the requested output
column. Descent performs binary lookups only; the final range is the stored
distinct-key array, not a newly filtered or sorted source projection. A
missing prefix has a complete empty range. This is distinct from refusal of
an unqualified layout or stale index.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.PrefixProjectionIndex

open ContiguousKeyRuns PrefixRunIndex IndexedIntersection
open Mettapedia.Algorithms

variable {Row Key : Type} [LinearOrder Key]

theorem group_key_support (key : Row → Key) (source : List Row) :
    ((group key source).buckets.map (fun bucket => key bucket.first)).toFinset =
      (source.map key).toFinset := by
  ext value
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨bucket, member, same⟩
    refine ⟨bucket.first, ?_, same⟩
    rw [← flatten_group key source]
    exact bucket_first_mem member
  · rintro ⟨row, member, same⟩
    rw [← flatten_group key source] at member
    obtain ⟨bucket, member, inBucket⟩ := List.mem_flatMap.mp member
    exact ⟨bucket, member, ((group_homogeneous key source bucket member row inBucket).symm.trans same)⟩

theorem root_projection (key : Row → Key) (suffix : List (Row → Key)) (source : List Row)
    (outside : Key) :
    ((build (key :: suffix) source).index.range outside).view.toFinset = (source.map key).toFinset := by
  change (Range.ofArray (build (key :: suffix) source).index.keys outside).view.toFinset = _
  rw [ofArray_view]
  dsimp only [build, IndexedKeyTable.ofList]
  simp only [List.map_map, Function.comp_def]
  rw [group_key_support]
  ext value
  simpa only [List.mem_toFinset] using ((CountedKeySort.run_spec key source).1.map key).mem_iff

def descend : (prefixKeys : List (Row → Key)) → (projection : Row → Key) →
    Index Row Key (prefixKeys ++ [projection]).length → Key → (Fin prefixKeys.length → Key) →
    Range Key × Nat
  | [], _, index, outside, _ => (index.range outside, 0)
  | _ :: rest, projection, index, outside, targets =>
      let found := IndexedKeyTable.lookup index outside (targets 0)
      match found.1 with
      | none => (Range.ofArray #[] outside, found.2)
      | some child =>
          let later := descend rest projection child.2 outside (fun i => targets i.succ)
          (later.1, found.2 + later.2)

def reference (prefixKeys : List (Row → Key)) (targets : Fin prefixKeys.length → Key)
    (projection : Row → Key) (source : List Row) : Finset Key :=
  ((PrefixRunIndex.reference prefixKeys targets source).map projection).toFinset

theorem reference_perm (prefixKeys : List (Row → Key)) (targets : Fin prefixKeys.length → Key)
    (projection : Row → Key) (first second : List Row) (permutation : first.Perm second) :
    reference prefixKeys targets projection first = reference prefixKeys targets projection second := by
  ext value
  simpa only [reference, List.mem_toFinset] using
    ((PrefixRunIndex.reference_perm prefixKeys targets first second permutation).map projection).mem_iff

theorem descend_spec (prefixKeys : List (Row → Key)) (projection : Row → Key) (source : List Row)
    (outside : Key) (targets : Fin prefixKeys.length → Key) (maximum : Nat)
    (bounded : source.length ≤ maximum) :
    let result := descend prefixKeys projection (build (prefixKeys ++ [projection]) source).index outside targets
    result.1.view.toFinset = reference prefixKeys targets projection source ∧
      result.1.Sorted ∧ result.1.width ≤ source.length ∧
      result.2 ≤ prefixKeys.length * (seekBudget maximum + 1) := by
  induction prefixKeys generalizing source with
  | nil =>
      refine ⟨root_projection projection [] source outside,
        IndexedKeyTable.range_sorted _ _, ?_, Nat.zero_le _⟩
      simpa [descend, IndexedKeyTable.Table.range, Range.ofArray, Range.width] using root_keys_bounded projection [] source
  | cons key rest ih =>
      let ordered := CountedKeySort.run key source
      let buckets := (group key ordered.rows).buckets
      have sortedRows := (CountedKeySort.run_spec key source).2.1
      have length : ordered.rows.length = source.length := (CountedKeySort.run_spec key source).1.length_eq
      have filtered := find_group_exact key (targets 0) ordered.rows sortedRows
      have preparation := reference_perm (key :: rest) targets projection ordered.rows source
        (CountedKeySort.run_spec key source).1
      have rootCharge := IndexedKeyTable.lookup_comparisons
        (build (key :: (rest ++ [projection])) source).index outside (targets 0)
      have keyBound := (root_keys_bounded key (rest ++ [projection]) source).trans bounded
      have logarithm := Nat.log_mono_right (b := 2) keyBound
      have charged : (IndexedKeyTable.lookup (build (key :: (rest ++ [projection])) source).index
          outside (targets 0)).2 ≤ seekBudget maximum + 1 := by
        unfold seekBudget at *
        omega
      dsimp only
      rw [descend]
      simp only [List.cons_append]
      rw [build_lookup key (rest ++ [projection]) source outside (targets 0)]
      cases found : buckets.find? (fun bucket => decide (key bucket.first = targets 0)) with
      | none =>
          have emptyRows : ordered.rows.filter (fun row => decide (key row = targets 0)) = [] := by
            change ((buckets.find? _).map Bucket.rows).getD [] = _ at filtered
            simpa only [found, Option.map_none, Option.getD_none] using filtered.symm
          have emptySupport : reference (key :: rest) targets projection source = ∅ := by
            rw [← preparation]
            simp only [reference, PrefixRunIndex.reference, emptyRows, PrefixRunIndex.reference_empty,
              List.map_nil, List.toFinset_nil]
          change _ = _ ∧ _ ∧ _ ∧ _
          simp only [Option.map_none]
          refine ⟨by simp [ofArray_view, emptySupport], ofArray_sorted _ _ (by simp), ?_, ?_⟩
          · simp [Range.ofArray, Range.width]
          · simp only [List.length_cons]
            nlinarith
      | some bucket =>
          have member := List.mem_of_find?_eq_some found
          have size : bucket.rows.length ≤ source.length :=
            (bucket_size_le key ordered.rows bucket member).trans_eq length
          have next := ih bucket.rows (fun i => targets i.succ) (size.trans bounded)
          have bucketRows : bucket.rows = ordered.rows.filter (fun row => decide (key row = targets 0)) := by
            change ((buckets.find? _).map Bucket.rows).getD [] = _ at filtered
            simpa only [found, Option.map_some, Option.getD_some] using filtered
          simp only [Option.map_some]
          refine ⟨?_, next.2.1, next.2.2.1.trans size, ?_⟩
          · rw [next.1, bucketRows]
            exact preparation
          · have bound := next.2.2.2
            simp only [List.length_cons]
            nlinarith

namespace Controls

def source : List (Nat × Nat × Nat) := PrefixRunIndex.Controls.source
def first : List ((Nat × Nat × Nat) → Nat) := [Prod.fst]
def second (row : Nat × Nat × Nat) : Nat := row.2.1

theorem existing_prefix_uses_stored_keys :
    (descend first second (build (first ++ [second]) source).index 0 (fun _ => 1)).1.view = [3, 4] := by decide +kernel

theorem missing_prefix_has_complete_empty_range :
    (descend first second (build (first ++ [second]) source).index 0 (fun _ => 9)).1.view = [] := by decide +kernel

theorem duplicate_occurrences_do_not_duplicate_navigation_keys :
    (descend first second (build (first ++ [second]) source).index 0 (fun _ => 2)).1.view = [1] := by decide +kernel

end Controls

end Mettapedia.Machines.Cursor.PrefixProjectionIndex
