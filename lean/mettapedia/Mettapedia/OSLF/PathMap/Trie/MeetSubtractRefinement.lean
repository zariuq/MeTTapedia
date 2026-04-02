import Mettapedia.OSLF.PathMap.Trie.CoinductiveTrie
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement

/-!
# Meet / Subtract Refinement (First Slice)

This file does **not** yet provide the full mutual-recursive lookup refinement
for `meet` and `subtract`.

What it does settle is the root-path agreement between finite tries and the
coinductive semantic carrier.  That gives a small but honest first bridge for
the algebra-parity gap after `join` and `restrict`.
-/

namespace Mettapedia.OSLF.PathMap.Trie

universe u

namespace FTrie

variable {V : Type u}

@[simp] theorem normalize_lookup_nil (t : FTrie V) :
    t.normalize.lookup [] = t.lookup [] := by
  cases t with
  | empty =>
      rfl
  | node val children =>
      cases val <;> cases children <;> simp [FTrie.normalize, FTrie.lookup]

/-- Root lookup for finite `meet` agrees with the pointwise coinductive
    intersection semantics. -/
theorem meet_lookup_nil (t₁ t₂ : FTrie V) :
    (t₁.meet t₂).lookup [] =
      (match t₁.lookup [], t₂.lookup [] with
       | some v, some _ => some v
       | _, _ => none) := by
  cases t₁ with
  | empty =>
      cases t₂ <;> simp [FTrie.meet, FTrie.lookup]
  | node v₁ c₁ =>
      cases t₂ with
      | empty =>
          simp [FTrie.meet, FTrie.lookup]
      | node v₂ c₂ =>
          cases v₁ <;> cases v₂ <;> simp [FTrie.meet, FTrie.lookup]

/-- Root lookup for finite `subtract` agrees with the pointwise coinductive
    difference semantics. -/
theorem subtract_lookup_nil (t₁ t₂ : FTrie V) :
    (t₁.subtract t₂).lookup [] =
      (match t₁.lookup [], t₂.lookup [] with
       | some v, none => some v
       | _, _ => none) := by
  cases t₁ with
  | empty =>
      cases t₂ <;> simp [FTrie.subtract, FTrie.lookup]
  | node v₁ c₁ =>
      cases t₂ with
      | empty =>
          cases v₁ <;> simp [FTrie.subtract, FTrie.lookup]
      | node v₂ c₂ =>
          cases v₁ <;> cases v₂ <;> simp [FTrie.subtract, FTrie.lookup]

/-- The `FTrie → CTrie` embedding agrees with `inter` at the root path. -/
theorem toCTrie_meet_root (t₁ t₂ : FTrie V) :
    (t₁.meet t₂).toCTrie [] = (CTrie.inter t₁.toCTrie t₂.toCTrie) [] := by
  simpa [CTrie.lookup_inter] using meet_lookup_nil t₁ t₂

/-- The `FTrie → CTrie` embedding agrees with `diff` at the root path. -/
theorem toCTrie_subtract_root (t₁ t₂ : FTrie V) :
    (t₁.subtract t₂).toCTrie [] = (CTrie.diff t₁.toCTrie t₂.toCTrie) [] := by
  simpa [CTrie.lookup_diff] using subtract_lookup_nil t₁ t₂

/-! ## Summary

**0 sorries. 0 axioms.**

This is a deliberately modest first slice:

- `meet_lookup_nil`
- `subtract_lookup_nil`
- `toCTrie_meet_root`
- `toCTrie_subtract_root`

The full pathwise lookup refinement for `meet` and `subtract` remains open and
should be developed as a later mutual-recursion packet, just as `join` and
`restrict` were.
-/

end FTrie

end Mettapedia.OSLF.PathMap.Trie
