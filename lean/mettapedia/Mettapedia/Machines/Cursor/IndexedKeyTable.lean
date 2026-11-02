import Mettapedia.Machines.Cursor.IndexedKeyLookup

/-!
# Immutable aligned key and payload arrays

A table is constructed once. Binary lookup reads only its key array and then
one payload position. Key/payload alignment and strict ordering are part of
the representation invariant, not facts inferred from a successful lookup.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.IndexedKeyTable

open IndexedIntersection

variable {Value Key : Type*} [LinearOrder Key]

structure Table (key : Value → Key) where
  values : Array Value
  keys : Array Key
  aligned : keys.toList = values.toList.map key
  sorted : keys.toList.Pairwise (· < ·)

def ofList (key : Value → Key) (values : List Value)
    (sorted : values.Pairwise (fun a b => key a < key b)) : Table key where
  values := values.toArray
  keys := (values.map key).toArray
  aligned := by simp
  sorted := by simpa only [List.toList_toArray, List.pairwise_map] using sorted

def Table.range {key : Value → Key} (table : Table key) (outside : Key) : Range Key :=
  Range.ofArray table.keys outside

theorem range_sorted {key : Value → Key} (table : Table key) (outside : Key) :
    (table.range outside).Sorted := ofArray_sorted _ _ table.sorted

theorem aligned_size {key : Value → Key} (table : Table key) : table.keys.size = table.values.size := by
  have same := congrArg List.length table.aligned
  simpa using same

theorem range_read {key : Value → Key} (table : Table key) (outside : Key)
    (i : Nat) (inside : i < table.values.size) :
    (table.range outside).read i = key table.values[i] := by
  have keyInside : i < table.keys.size := by rw [aligned_size]; exact inside
  have atIndex := congrArg (fun entries : List Key => entries[i]?) table.aligned
  have equal := congrArg (fun entry => entry.getD outside) atIndex
  simpa [Table.range, Range.ofArray, List.getElem?_map,
    Array.getElem?_eq_getElem keyInside, Array.getElem?_eq_getElem inside] using equal

def lookup {key : Value → Key} (table : Table key) (outside target : Key) : Option Value × Nat :=
  let found := IndexedKeyLookup.lookup (table.range outside) target
  (found.1.bind (fun i => table.values[i]?), found.2)

theorem lookup_exact {key : Value → Key} (table : Table key) (outside target : Key) :
    (lookup table outside target).1 = table.values.toList.find? (fun value => decide (key value = target)) := by
  cases found : table.values.toList.find? (fun value => decide (key value = target)) with
  | none =>
      have missing := List.find?_eq_none.mp found
      have absent : target ∉ (table.range outside).view := by
        rw [Table.range, ofArray_view, table.aligned]
        intro member
        obtain ⟨value, member, same⟩ := List.mem_map.mp member
        exact missing value member (decide_eq_true same)
      have noPosition := (IndexedKeyLookup.lookup_none_iff (table.range outside)
        (range_sorted table outside) target).mpr absent
      simp only [lookup, noPosition, Option.bind_none]
  | some value =>
      have member := List.mem_of_find?_eq_some found
      have same : key value = target := by simpa only [decide_eq_true_eq] using List.find?_some found
      obtain ⟨i, inside, atValue⟩ := List.mem_iff_getElem.mp member
      have valueInside : i < table.values.size := inside
      have keyInside : i < table.keys.size := by rw [aligned_size]; exact valueInside
      have atKey : (table.range outside).read i = target := by
        rw [range_read table outside i valueInside]
        change key table.values.toList[i] = target
        rw [atValue]
        exact same
      have position := (IndexedKeyLookup.lookup_some_iff (table.range outside)
        (range_sorted table outside) target i).mpr ⟨Nat.zero_le _, keyInside, atKey⟩
      simp only [lookup, position, Option.bind_some, Array.getElem?_eq_getElem valueInside]
      exact congrArg some atValue

theorem lookup_comparisons {key : Value → Key} (table : Table key) (outside target : Key) :
    (lookup table outside target).2 ≤ seekBudget table.keys.size + 1 :=
  IndexedKeyLookup.lookup_comparisons _ _ _ (by simp [Table.range, Range.ofArray, Range.width])

theorem ofList_lookup (key : Value → Key) (values : List Value)
    (sorted : values.Pairwise (fun a b => key a < key b)) (outside target : Key) :
    (lookup (ofList key values sorted) outside target).1 =
      values.find? (fun value => decide (key value = target)) := by
  rw [lookup_exact]
  simp [ofList]

namespace Controls

def table : Table (Prod.fst : Nat × String → Nat) :=
  ofList Prod.fst [(1, "first"), (4, "fourth")] (by decide)

theorem payload_is_position_aligned : (lookup table 0 4).1 = some (4, "fourth") := by decide +kernel
theorem gap_does_not_return_nearest_payload : (lookup table 0 2).1 = none := by decide +kernel

end Controls

end Mettapedia.Machines.Cursor.IndexedKeyTable
