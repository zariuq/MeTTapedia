import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic

/-!
# List-Set Bridge Lemmas

This module provides lemmas bridging List.foldl operations with Set operations.

## Main Results

- `List.foldl_union_pair`: Two-element foldl with union equals union of images
- `List.mem_of_mem_cons_cons`: Membership symmetry for two-element lists
- `List.foldl_union_set`: General foldl with union equals indexed union
- `Set.mem_foldl_union`: Membership characterization in folded union

## References

- mm-lean4 ArrayListExt.lean: fold invariant patterns (lines 88-178)
- NoncrossingPartitions.lean: Finset union examples

-/

namespace Mettapedia.Lists.SetFold

/-! ## Basic Lemmas -/

/-- Membership in a two-element list is symmetric.

    This lemma shows that the order of elements in a two-element list
    doesn't affect membership.
-/
theorem List.mem_of_mem_cons_cons {α : Type*} (a b x : α) :
    x ∈ [a, b] ↔ x ∈ [b, a] := by
  simp only [List.mem_cons]
  tauto

/-- Folding union over a two-element list.

    This directly computes the result of folding set union over [a, b],
    showing it equals f a ∪ f b.
-/
theorem List.foldl_union_pair {α : Type*} (f : α → Set β) (a b : α) :
    [a, b].foldl (fun acc x => acc ∪ f x) ∅ = f a ∪ f b := by
  simp only [List.foldl_cons, List.foldl_nil]
  rw [Set.empty_union, Set.union_comm]

/-! ## General Lemmas -/

/-- Folding union with initial value s equals s ∪ (folding with empty initial).

    This is the key property that union distributes over fold initialization.
-/
theorem List.foldl_union_comm {α : Type*} (f : α → Set β) (s : Set β) (xs : List α) :
    xs.foldl (fun acc x => acc ∪ f x) s =
    s ∪ xs.foldl (fun acc x => acc ∪ f x) ∅ := by
  induction xs generalizing s with
  | nil =>
      simp [List.foldl]
  | cons x xs ih =>
      simp only [List.foldl]
      rw [ih (s ∪ f x), ih (∅ ∪ f x), Set.empty_union]
      rw [Set.union_assoc]

/-- Folding union over a cons equals union of head with fold of tail.

    This is a key structural lemma for inductive proofs about foldl with union.
-/
theorem List.foldl_union_cons {α : Type*} (f : α → Set β) (a : α) (xs : List α) :
    (a :: xs).foldl (fun acc x => acc ∪ f x) ∅ =
    f a ∪ xs.foldl (fun acc x => acc ∪ f x) ∅ := by
  simp only [List.foldl]
  rw [foldl_union_comm, Set.empty_union]

/-- Membership in folded union iff exists element with membership in image.

    This characterizes when an element belongs to a folded union,
    which is crucial for the canInteract_implies_freeNames proof.
-/
theorem Set.mem_foldl_union {α : Type*} (f : α → Set β) (xs : List α) (y : β) :
    y ∈ xs.foldl (fun acc x => acc ∪ f x) ∅ ↔ ∃ x ∈ xs, y ∈ f x := by
  induction xs with
  | nil =>
      simp [List.foldl]
  | cons x xs ih =>
      rw [List.foldl_union_cons, Set.mem_union]
      constructor
      · intro h
        cases h with
        | inl hx =>
            exact ⟨x, by simp, hx⟩
        | inr hxs =>
            obtain ⟨z, hz_mem, hz⟩ := ih.mp hxs
            exact ⟨z, by simp [hz_mem], hz⟩
      · intro ⟨z, hz_mem, hz⟩
        simp only [List.mem_cons] at hz_mem
        cases hz_mem with
        | inl heq =>
            left
            rw [← heq]
            exact hz
        | inr hmem =>
            right
            exact ih.mpr ⟨z, hmem, hz⟩

/-- Folding union over a list equals the indexed union over list elements.

    This is the main theorem connecting list foldl to set-theoretic union.
    It generalizes foldl_union_pair to arbitrary lists.
-/
theorem List.foldl_union_set {α : Type*} (f : α → Set β) (xs : List α) :
    xs.foldl (fun acc x => acc ∪ f x) ∅ = ⋃ (x : α) (_ : x ∈ xs), f x := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_foldl_union]
  constructor
  · intro ⟨x, hx, hy⟩
    exact ⟨x, ⟨hx, hy⟩⟩
  · intro ⟨i, hi, hy⟩
    exact ⟨i, hi, hy⟩

/-! ## Examples and Tests -/

-- Test foldl_union_pair
example : [1, 2].foldl (fun acc x => acc ∪ {x}) ∅ = ({1} ∪ {2} : Set ℕ) := by
  rw [List.foldl_union_pair]

-- Test mem_of_mem_cons_cons
example (a b : Nat) : a ∈ [a, b] ∧ b ∈ [a, b] ∧ a ∈ [b, a] ∧ b ∈ [b, a] := by
  constructor <;> try constructor <;> simp

end Mettapedia.Lists.SetFold
