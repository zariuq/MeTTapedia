import Mettapedia.OSLF.PathMap.Trie.Morphisms
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie

/-!
# Morphism Correctness — Connecting Theorems

Proves `FTrie.cata countAlgebra t = t.recCount` via mutual induction,
where `recCount` is an independently defined recursive value counter.

This is the substantive connecting theorem: the catamorphism framework
produces the same answer as direct structural recursion.

## Pattern

Follows `TrieRefinement.lean:120-223` — mutual theorems in a separate
file from the mutual definitions.
-/

namespace Mettapedia.OSLF.PathMap.Trie

universe u

variable {V : Type u}

/-! ## §1: Independent recursive value count -/

mutual
  /-- Count values by direct structural recursion (independent of cata).
      Mirrors `cata`'s mutual structure but with hardcoded counting logic. -/
  def FTrie.recCount : FTrie V → Nat
    | .empty => 0
    | .node val children =>
      (match val with | some _ => 1 | none => 0) +
      FTrie.recCountChildren children

  /-- Count values across a child list. -/
  def FTrie.recCountChildren : List (UInt8 × FTrie V) → Nat
    | [] => 0
    | (_, child) :: cs =>
      FTrie.recCount child + FTrie.recCountChildren cs
end

/-! ## §2: foldl (+) telescope -/

/-- `foldl (+) a xs = a + foldl (+) 0 xs` for Nat. -/
private theorem foldl_add_init (a : Nat) (xs : List Nat) :
    xs.foldl (· + ·) a = a + xs.foldl (· + ·) 0 := by
  induction xs generalizing a with
  | nil => simp [List.foldl]
  | cons x rest ih =>
    simp only [List.foldl]
    rw [ih (a + x)]
    simp [Nat.zero_add]
    rw [ih x]
    omega

/-! ## §3: General cata_count_correct via mutual induction -/

mutual
  /-- **Connecting theorem (general case):**
      `cata countAlgebra t` equals the recursively computed `recCount t`.

      Proved by mutual structural induction on `FTrie V`. -/
  theorem FTrie.cata_recCount (t : FTrie V) :
      FTrie.cata countAlgebra t = FTrie.recCount t := by
    match t with
    | .empty => rfl
    | .node val children =>
      simp only [FTrie.cata, countAlgebra, FTrie.recCount]
      congr 1
      exact FTrie.cataChildren_recCount children

  /-- Mutual helper: `foldl (+) 0` over cata results equals `recCountChildren`. -/
  theorem FTrie.cataChildren_recCount
      (cs : List (UInt8 × FTrie V)) :
      (FTrie.cataChildren countAlgebra cs).foldl (· + ·) 0 =
      FTrie.recCountChildren cs := by
    match cs with
    | [] => rfl
    | (_, child) :: rest =>
      simp only [FTrie.cataChildren, FTrie.recCountChildren, List.foldl]
      rw [foldl_add_init, FTrie.cata_recCount child, FTrie.cataChildren_recCount rest]
      omega
end

/-! ## §4: zip_map_fst helper -/

/-- Zipping keys with values reconstructs the original pair list. -/
private theorem zip_map_fst_snd {α β : Type u} (cs : List (α × β)) :
    (cs.map Prod.fst).zip (cs.map Prod.snd) = cs := by
  induction cs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp [List.map, List.zip, ih]

/-! ## §5: Identity catamorphism — lookup-level correctness -/

/-- The faithful rebuild algebra. -/
def rebuildAlgebra : CataAlgebra V (FTrie V) :=
  fun keys children val => .node val (keys.zip children)

mutual
  /-- **Identity catamorphism correctness (lookup-level):**
      `(cata rebuildAlgebra t).lookup p = t.lookup p` for all paths.

      Note: `cata rebuildAlgebra .empty = .node none []` (not `.empty`),
      so structural equality `cata rebuildAlgebra t = t` fails for empty.
      But LOOKUP equality holds because `.node none []` and `.empty` have
      the same lookup behavior. -/
  theorem FTrie.cata_rebuild_lookup (t : FTrie V) (p : List UInt8) :
      (FTrie.cata rebuildAlgebra t).lookup p = t.lookup p := by
    match t with
    | .empty =>
      -- cata rebuildAlgebra .empty = .node none []
      -- .node none [] has same lookup as .empty for all paths
      cases p with
      | nil => rfl
      | cons b rest =>
        show FTrie.lookupChild b rest (List.nil.zip List.nil) = none
        rfl
    | .node val children =>
      cases p with
      | nil =>
        simp only [FTrie.cata, rebuildAlgebra, FTrie.lookup]
      | cons b rest =>
        show (FTrie.node val ((children.map Prod.fst).zip
          (FTrie.cataChildren rebuildAlgebra children))).lookup (b :: rest) =
          (FTrie.node val children).lookup (b :: rest)
        simp only [FTrie.lookup]
        exact FTrie.cataChildren_rebuild_lookupChild children b rest

  /-- Mutual helper: lookupChild through zip of keys and cataChildren results
      equals lookupChild through the original children. -/
  theorem FTrie.cataChildren_rebuild_lookupChild
      (cs : List (UInt8 × FTrie V)) (b : UInt8) (rest : List UInt8) :
      FTrie.lookupChild b rest
        ((cs.map Prod.fst).zip (FTrie.cataChildren rebuildAlgebra cs)) =
      FTrie.lookupChild b rest cs := by
    induction cs with
    | nil => rfl
    | cons hd tl ih =>
      obtain ⟨k, child⟩ := hd
      simp only [List.map, FTrie.cataChildren, List.zip, List.zipWith,
                  FTrie.lookupChild]
      by_cases hkb : (k == b) = true
      · simp only [hkb, ↓reduceIte]
        exact FTrie.cata_rebuild_lookup child rest
      · simp only [hkb, Bool.false_eq_true, ↓reduceIte]
        exact ih
end

/-! ## §6: Summary

**0 sorries. 0 axioms.**

- `FTrie.recCount` / `FTrie.recCountChildren` — independent recursive count
- `FTrie.cata_recCount` — **general connecting theorem** via mutual induction:
  `cata countAlgebra t = recCount t`
- `FTrie.cataChildren_recCount` — mutual helper for child lists
- `foldl_add_init` — telescope lemma used in the induction step

The mutual induction follows the `join_lookup` / `joinChildren_lookup` pattern
from `TrieRefinement.lean`.
-/

end Mettapedia.OSLF.PathMap.Trie
