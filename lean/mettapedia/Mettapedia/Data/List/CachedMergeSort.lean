import Init.Data.List.Sort.Lemmas

set_option autoImplicit false

namespace List

universe u v
variable {α : Type u} {κ : Type v}

/-- Compute each ordering key once while retaining the complete input record. -/
def mergeSortWithCachedKeys (key : α → κ) (before : κ → κ → Bool) (items : List α) :
    List α :=
  ((items.map fun item => (key item, item)).mergeSort
    (fun x y => before x.1 y.1)).map Prod.snd

/-- Caching keys preserves the full ordered result, including ties. -/
theorem mergeSortWithCachedKeys_eq (key : α → κ) (before : κ → κ → Bool) (items : List α) :
    mergeSortWithCachedKeys key before items =
      items.mergeSort (fun x y => before (key x) (key y)) := by
  unfold mergeSortWithCachedKeys
  rw [List.map_mergeSort (s := fun x y => before (key x) (key y))]
  · rw [List.map_map]
    change (items.map id).mergeSort _ = _
    rw [List.map_id]
  · intro a ha b hb
    obtain ⟨left, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨right, _, rfl⟩ := List.mem_map.mp hb
    rfl

private def keysOrderedFrom (key : α → κ) (before : κ → κ → Bool) :
    κ → List α → Bool
  | _, [] => true
  | previous, item :: rest =>
      let next := key item
      if before previous next then keysOrderedFrom key before next rest else false

private theorem keysOrderedFrom_sound (key : α → κ) (before : κ → κ → Bool)
    (transitive : ∀ a b c, before a b = true → before b c = true → before a c = true) :
    ∀ (items : List α) (previous : κ), keysOrderedFrom key before previous items = true →
      (∀ item ∈ items, before previous (key item) = true) ∧
      items.Pairwise (fun x y => before (key x) (key y) = true) := by
  intro items
  induction items with
  | nil => simp
  | cons item rest ih =>
      intro previous ordered
      simp only [keysOrderedFrom] at ordered
      split at ordered
      next earlier =>
        obtain ⟨compares, pairwise⟩ := ih (key item) ordered
        refine ⟨?_, List.pairwise_cons.mpr ⟨compares, pairwise⟩⟩
        intro current member
        rcases List.mem_cons.mp member with rfl | later
        · exact earlier
        · exact transitive _ _ _ earlier (compares current later)
      next _ => cases ordered

/-- A linear check leaves already ordered inputs as they are. -/
def mergeSortWithOrderedCheck (key : α → κ) (before : κ → κ → Bool)
    (items : List α) : List α :=
  match items with
  | [] | [_] => items
  | first :: second :: rest =>
      if keysOrderedFrom key before (key first) (second :: rest) then items
      else mergeSortWithCachedKeys key before items

/-- For a transitive comparator the ordered check preserves stable sort exactly. -/
theorem mergeSortWithOrderedCheck_eq (key : α → κ) (before : κ → κ → Bool)
    (transitive : ∀ a b c, before a b = true → before b c = true → before a c = true)
    (items : List α) : mergeSortWithOrderedCheck key before items =
      items.mergeSort (fun x y => before (key x) (key y)) := by
  cases items with
  | nil => simp [mergeSortWithOrderedCheck]
  | cons first tail =>
      cases tail with
      | nil => simp [mergeSortWithOrderedCheck]
      | cons second rest =>
          simp only [mergeSortWithOrderedCheck]
          split
          next ready =>
            exact (List.mergeSort_of_pairwise (List.pairwise_cons.mpr
              (keysOrderedFrom_sound key before transitive (second :: rest) (key first) ready))).symm
          next _ => exact mergeSortWithCachedKeys_eq key before _

example :
    mergeSortWithOrderedCheck Prod.fst (fun a b : Nat => a ≤ b)
      [(2, "first"), (1, "middle"), (2, "last")] =
      [(1, "middle"), (2, "first"), (2, "last")] := by cbv

end List
