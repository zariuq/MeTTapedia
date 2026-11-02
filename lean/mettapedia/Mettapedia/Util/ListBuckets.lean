import Mathlib.Data.List.Basic

/-! Stable array buckets built in one traversal of a list. Each bucket is
exactly the original list filtered by its key; order and duplicates remain. -/

set_option autoImplicit false

namespace Mettapedia.Util.ListBuckets

def prepend {α : Type} (key : α → Nat) (values : List α) (buckets : Array (List α)) : Array (List α) :=
  values.foldr (fun value buckets => buckets.modify (key value) (value :: ·)) buckets

theorem getElem?_prepend {α : Type} (key : α → Nat) (values : List α)
    (buckets : Array (List α)) (position : Nat) :
    (prepend key values buckets)[position]? =
      (buckets[position]?).map ((values.filter fun value => key value == position) ++ ·) := by
  induction values with
  | nil => simp [prepend]
  | cons value rest ih =>
    simp only [prepend, List.foldr_cons, Array.getElem?_modify] at *
    rw [ih]
    by_cases same : key value = position
    · simp [same, Option.map_map, Function.comp_def]
    · simp [same]

def build {α : Type} (key : α → Nat) (size : Nat) (values : List α) : Array (List α) :=
  prepend key values (Array.replicate size [])

theorem build_eq {α : Type} (key : α → Nat) (size : Nat) (values : List α) :
    build key size values = Array.ofFn (fun position : Fin size =>
      values.filter fun value => key value == position.val) := by
  apply Array.ext_getElem?
  intro position
  rw [build, getElem?_prepend]
  by_cases inside : position < size
  · simp [inside]
  · simp [inside]

end Mettapedia.Util.ListBuckets
