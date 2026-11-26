import Mathlib.Data.List.Chain

/-! A Boolean scan for a relational chain, with the relational proof kept out
of the computed result. -/

set_option autoImplicit false

namespace Mettapedia.Data.List

variable {α : Type*}

/-- Test each consecutive pair, from left to right. -/
def checkAdjacent (test : α → α → Bool) : List α → Bool
  | [] | [_] => true
  | first :: second :: rest => test first second && checkAdjacent test (second :: rest)

theorem checkAdjacent_eq_true_iff {test : α → α → Bool} {relation : α → α → Prop}
    (law : ∀ a b, (test a b = true) ↔ relation a b) :
    ∀ items, checkAdjacent test items = true ↔ List.IsChain relation items
  | [] => by simp [checkAdjacent]
  | [_] => by simp [checkAdjacent]
  | first :: second :: rest => by
      rw [checkAdjacent, Bool.and_eq_true, List.isChain_cons_cons, law,
        checkAdjacent_eq_true_iff law (second :: rest)]

theorem isChain_of_checkAdjacent {relation : α → α → Prop} [DecidableRel relation]
    {items : List α} (checked : checkAdjacent (fun a b => decide (relation a b)) items = true) :
    List.IsChain relation items :=
  (checkAdjacent_eq_true_iff (fun _ _ => decide_eq_true_iff) items).mp checked

/-- A checked nonempty segment with explicit boundary labels. -/
structure ChainSegment (relation : α → α → Prop) (items : List α) (first last : α) : Prop where
  head : items.head? = some first
  tail : items.getLast? = some last
  ordered : List.IsChain relation items

namespace ChainSegment

theorem append {relation : α → α → Prop} {left right : List α}
    {first before after last : α}
    (leftBlock : ChainSegment relation left first before) (rightBlock : ChainSegment relation right after last)
    (seam : relation before after) : ChainSegment relation (left ++ right) first last where
  head := by rw [List.head?_append, leftBlock.head]; rfl
  tail := by rw [List.getLast?_append, rightBlock.tail]; rfl
  ordered := leftBlock.ordered.append rightBlock.ordered (by simpa [leftBlock.tail, rightBlock.head] using seam)

end ChainSegment

/-- A sorted flattening with the chunk boundaries retained in its type. -/
structure OrderedChunks (relation : α → α → Prop) (chunks : List (List α))
    (first last : α) : Prop where
  segment : ChainSegment relation chunks.flatten first last

namespace OrderedChunks

theorem single {relation : α → α → Prop} [DecidableRel relation] (items : List α)
    (nonempty : items ≠ []) (checked : checkAdjacent (fun a b => decide (relation a b)) items = true) :
    OrderedChunks relation [items] (items.head nonempty) (items.getLast nonempty) where
  segment := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
      (show ChainSegment relation items (items.head nonempty) (items.getLast nonempty) from
        ⟨List.head?_eq_some_head nonempty, List.getLast?_eq_some_getLast nonempty,
          isChain_of_checkAdjacent checked⟩)

theorem append {relation : α → α → Prop} {left right : List (List α)}
    {first before after last : α}
    (leftBlock : OrderedChunks relation left first before) (rightBlock : OrderedChunks relation right after last)
    (seam : relation before after) : OrderedChunks relation (left ++ right) first last where
  segment := by
    rw [List.flatten_append]
    exact leftBlock.segment.append rightBlock.segment seam

end OrderedChunks

section Controls

example : checkAdjacent (fun a b : String => decide (a < b)) ["aa", "ab", "ba"] = true := rfl

example : checkAdjacent (fun a b : String => decide (a < b)) ["aa", "aa", "ba"] = false := rfl

example : checkAdjacent (fun a b : String => decide (a < b)) ["ab", "aa", "ba"] = false := rfl


end Controls
end Mettapedia.Data.List
