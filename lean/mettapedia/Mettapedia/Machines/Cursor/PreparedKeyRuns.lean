import Mettapedia.Machines.Cursor.ContiguousKeyRuns
import Mettapedia.Machines.Cursor.IndexedKeyLookup

/-!
# Reusable distinct-key arrays with complete occurrence payloads

Preparation groups a sorted input once and stores aligned key/payload arrays.
Lookup navigates the key array by binary search and retrieves the selected
payload by position. It does not regroup, sort or filter the source rows.
The reference filter occurs only in the correctness statement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.PreparedKeyRuns

open IndexedIntersection ContiguousKeyRuns

variable {Row Key : Type*} [LinearOrder Key]

structure Prepared (key : Row → Key) where
  buckets : Array (Bucket Row)
  keys : Array Key
  aligned : keys.toList = buckets.toList.map (fun bucket => key bucket.first)
  sorted : keys.toList.Pairwise (· < ·)

def prepare (key : Row → Key) (rows : List Row)
    (sorted : rows.Pairwise (fun left right => key left ≤ key right)) : Prepared key :=
  let result := group key rows
  { buckets := result.buckets.toArray
    keys := (result.buckets.map (fun bucket => key bucket.first)).toArray
    aligned := by simp
    sorted := by
      simpa only [List.toList_toArray, List.pairwise_map] using group_keys_sorted key rows sorted }

def Prepared.range {key : Row → Key} (prepared : Prepared key) (outside : Key) : Range Key :=
  Range.ofArray prepared.keys outside

theorem range_sorted {key : Row → Key} (prepared : Prepared key) (outside : Key) :
    (prepared.range outside).Sorted := ofArray_sorted _ _ prepared.sorted

theorem aligned_size {key : Row → Key} (prepared : Prepared key) :
    prepared.keys.size = prepared.buckets.size := by
  have same := congrArg List.length prepared.aligned
  simpa using same

theorem range_read {key : Row → Key} (prepared : Prepared key) (outside : Key)
    (i : Nat) (inside : i < prepared.buckets.size) :
    (prepared.range outside).read i = key prepared.buckets[i].first := by
  have keyInside : i < prepared.keys.size := by rw [aligned_size]; exact inside
  have atIndex := congrArg (fun entries : List Key => entries[i]?) prepared.aligned
  have equal := congrArg (fun entry => entry.getD outside) atIndex
  simpa [Prepared.range, Range.ofArray, List.getElem?_map,
    Array.getElem?_eq_getElem keyInside, Array.getElem?_eq_getElem inside] using equal

def lookup {key : Row → Key} (prepared : Prepared key) (outside target : Key) : Option (Bucket Row) × Nat :=
  let found := IndexedKeyLookup.lookup (prepared.range outside) target
  (found.1.bind (fun i => prepared.buckets[i]?), found.2)

theorem lookup_exact {key : Row → Key} (prepared : Prepared key) (outside target : Key) :
    (lookup prepared outside target).1 =
      prepared.buckets.toList.find? (fun bucket => decide (key bucket.first = target)) := by
  cases found : prepared.buckets.toList.find? (fun bucket => decide (key bucket.first = target)) with
  | none =>
      have missing := List.find?_eq_none.mp found
      have absent : target ∉ (prepared.range outside).view := by
        rw [Prepared.range, ofArray_view, prepared.aligned]
        intro member
        obtain ⟨bucket, member, same⟩ := List.mem_map.mp member
        exact missing bucket member (decide_eq_true same)
      have noPosition := (IndexedKeyLookup.lookup_none_iff (prepared.range outside)
        (range_sorted prepared outside) target).mpr absent
      simp only [lookup, noPosition, Option.bind_none]
  | some bucket =>
      have member := List.mem_of_find?_eq_some found
      have same : key bucket.first = target := by simpa only [decide_eq_true_eq] using List.find?_some found
      obtain ⟨i, inside, atBucket⟩ := List.mem_iff_getElem.mp member
      have bucketInside : i < prepared.buckets.size := inside
      have keyInside : i < prepared.keys.size := by rw [aligned_size]; exact bucketInside
      have atKey : (prepared.range outside).read i = target := by
        rw [range_read prepared outside i bucketInside]
        change key prepared.buckets.toList[i].first = target
        rw [atBucket]
        exact same
      have position := (IndexedKeyLookup.lookup_some_iff (prepared.range outside)
        (range_sorted prepared outside) target i).mpr ⟨Nat.zero_le _, keyInside, atKey⟩
      simp only [lookup, position, Option.bind_some, Array.getElem?_eq_getElem bucketInside]
      exact congrArg some atBucket

def rows {key : Row → Key} (prepared : Prepared key) (outside target : Key) : List Row :=
  ((lookup prepared outside target).1.map Bucket.rows).getD []

theorem prepared_rows_exact (key : Row → Key) (source : List Row)
    (sorted : source.Pairwise (fun left right => key left ≤ key right)) (outside target : Key) :
    rows (prepare key source sorted) outside target = source.filter (fun row => decide (key row = target)) := by
  rw [rows, lookup_exact]
  change (((group key source).buckets.toArray.toList.find? _).map Bucket.rows).getD [] = _
  rw [List.toList_toArray]
  exact find_group_exact key target source sorted

theorem lookup_comparisons {key : Row → Key} (prepared : Prepared key) (outside target : Key) :
    (lookup prepared outside target).2 ≤ seekBudget prepared.keys.size + 1 :=
  IndexedKeyLookup.lookup_comparisons _ _ _ (by simp [Prepared.range, Range.ofArray, Range.width])

theorem prepared_key_count (key : Row → Key) (source : List Row)
    (sorted : source.Pairwise (fun left right => key left ≤ key right)) :
    (prepare key source sorted).keys.size ≤ source.length := by
  simpa [prepare] using group_bucket_count key source

theorem prepared_occurrence_count (key : Row → Key) (source : List Row)
    (sorted : source.Pairwise (fun left right => key left ≤ key right)) :
    (((prepare key source sorted).buckets.toList).map (fun bucket => bucket.rows.length)).sum = source.length := by
  simpa [prepare] using group_rows_count key source

namespace Controls

def source : List (Nat × Nat) := ContiguousKeyRuns.Controls.occurrences
def prepared : Prepared (Prod.fst : Nat × Nat → Nat) := prepare Prod.fst source (by decide)

theorem lookup_all_duplicate_occurrences : rows prepared 0 1 = [(1, 10), (1, 11)] := by decide +kernel
theorem lookup_middle_gap : rows prepared 0 3 = [] := by decide +kernel
theorem lookup_final_run : rows prepared 0 4 = [(4, 13), (4, 14)] := by decide +kernel
theorem keys_are_not_occurrences : prepared.keys.size = 3 ∧ source.length = 5 := by decide +kernel
theorem dropping_duplicate_is_wrong : rows prepared 0 1 ≠ [(1, 10)] := by decide +kernel

end Controls

end Mettapedia.Machines.Cursor.PreparedKeyRuns
