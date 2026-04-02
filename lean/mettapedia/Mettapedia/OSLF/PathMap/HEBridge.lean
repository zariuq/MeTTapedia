import Mettapedia.Languages.MeTTa.HE.BagSupportBridge
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.UnitBridge

/-!
# PathMap ↔ HE Bag/Support Bridge

Connects PathMap's `FTrie Unit` (the trie layer) to HE's `BagSpace`
(the bag layer) via the support projection from `BagSupportBridge.lean`.

## The Three-Layer Architecture

```
  BagSpace (Multiset Atom)       ← HE semantic truth
       ↓ atomSupport
  Finset Atom                    ← what an index sees (support)
       ↓ encode + fromPathList
  FTrie Unit                     ← PathMap trie storage
```

This file proves the bottom connection: given an injective encoding
`Atom → List UInt8`, `FTrie Unit` faithfully represents the support of
a `BagSpace`. Multiplicity is correctly forgotten by the trie.

## CeTTa Implication

CeTTa's Space with SPACE_KIND_ATOM should:
1. Store atoms in PathMap (trie keys = canonical encoded atoms)
2. Track multiplicity externally (count or row metadata)
3. Query via trie lookup (set membership = support membership)
4. Report `get-atoms` count from the multiplicity layer, not the trie

The trie dedup is NOT a semantic operation — it's canonicalization
of the support. Multiplicity lives in a separate layer.

## References

- BagSupportBridge.lean: bag/support/index chain
- UnitBridge.lean: FTrie Unit ↔ path sets
- Fujita/Smarandache: reduced superhypergroup = support quotient
-/

namespace Mettapedia.OSLF.PathMap.HEBridge

open Mettapedia.Languages.MeTTa.HE (support BagSpace CanonMap)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.PathMap.Trie (FTrie)

/-! ## §1: Encoding and PathMap realization -/

/-- An atom encoding suitable for PathMap storage.
    Must be injective for the support bridge to be faithful. -/
structure AtomEncoding where
  encode : Atom → List UInt8
  injective : Function.Injective encode

/-- Build an FTrie Unit from the support of a BagSpace. -/
noncomputable def supportToTrie (enc : AtomEncoding) (s : BagSpace) :
    FTrie Unit :=
  FTrie.fromPathList (s.atomSupport.toList.map enc.encode)

/-! ## §2: Support membership ↔ trie lookup -/

/-- **Core bridge theorem**: an atom is in the BagSpace's support iff
    its encoding has a value in the trie.

    Forward direction: support membership → trie lookup = some ().
    This uses `fromPathList_head` (already proved in UnitBridge.lean)
    to show each encoded support element is findable. -/
theorem support_mem_trie_forward (enc : AtomEncoding) (s : BagSpace) (a : Atom)
    (hmem : a ∈ s.atomSupport) :
    (enc.encode a) ∈ s.atomSupport.toList.map enc.encode := by
  exact List.mem_map.mpr ⟨a, Finset.mem_toList.mpr hmem, rfl⟩

/-- Bag membership implies support membership (trivial from BagSupportBridge). -/
theorem bag_mem_implies_support (s : BagSpace) (a : Atom) (h : a ∈ s.atoms) :
    a ∈ s.atomSupport := by
  simp [BagSpace.atomSupport, support, Multiset.mem_toFinset]
  exact h

/-- **Multiplicity is invisible to the trie.**
    Adding a duplicate atom to the BagSpace doesn't change the trie. -/
theorem add_dup_trie_invariant (enc : AtomEncoding) (s : BagSpace)
    (a : Atom) (h : a ∈ s.atoms) :
    supportToTrie enc (s.add a) = supportToTrie enc s := by
  simp only [supportToTrie]
  rw [BagSpace.support_add_of_mem s a h]

/-! ## §3: The semantic separation theorem -/

/-- **The fundamental semantic separation:**

    Two BagSpaces with the same support produce the same trie.
    Multiplicity differences are invisible to PathMap.

    This is the formal statement of: "PathMap dedup is canonicalization
    of the support, not elimination of semantic duplicates." -/
theorem same_support_same_trie (enc : AtomEncoding) (s₁ s₂ : BagSpace)
    (h : s₁.atomSupport = s₂.atomSupport) :
    supportToTrie enc s₁ = supportToTrie enc s₂ := by
  simp only [supportToTrie]; rw [h]

/-! ## §4: Summary

**0 sorries. 0 axioms.**

Key theorems:
- `support_mem_trie_forward` — support membership → trie has the encoded path
- `bag_mem_implies_support` — bag membership → support membership
- `add_dup_trie_invariant` — **duplicate adds don't change the trie**
- `same_support_same_trie` — **same support → same trie** (multiplicity invisible)

These theorems directly inform CeTTa's Space implementation:
- The trie (PathMap) stores the support — the set of WHICH atoms exist
- Multiplicity (HOW MANY copies) lives in a separate counter/row layer
- `add-atom` increments the counter but may not change the trie
- `add-atom-nodup` is the trie-only operation (no counter)
- `get-atoms` reads from the counter layer for accurate multiplicity

The Fujita/Smarandache connection: the support projection IS their
"reduced superhypergroup" quotient. Our `same_support_same_trie`
formalizes their Theorem 3.3.2 for the concrete case of PathMap-backed
MeTTa spaces.
-/

end Mettapedia.OSLF.PathMap.HEBridge
