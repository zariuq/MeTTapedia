import Mettapedia.OSLF.PathMap.Zipper
import Mettapedia.OSLF.PathMap.Core
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.TriePathMapInstance

/-!
# ZipperWriting Mutation Laws

Semantic specifications and concrete operations for PathMap mutations.
Closes the Rust `write_zipper.rs` formalization gap.

## Architecture

1. `InPlaceMeetSubtractRestrict` — 3 in-place operations (class)
2. `FTrie.graft` — subtrie replacement
3. Concrete `FTrie` instance with identity-correctness theorems
4. `ZipperWritingSpec` / `InPlaceStatusSpec` — specification records

## References

- PathMap crate: `write_zipper.rs`
- Zipper.lean: `PathMapLatticeInPlace`, `AlgebraicStatus`
-/

namespace Mettapedia.OSLF.PathMap

open Mettapedia.PathMap
open Mettapedia.OSLF.PathMap.Trie

/-! ## §1: Specification Records -/

/-- Specification of lens-like laws for value mutation at a cursor focus. -/
structure ZipperWritingSpec (Z V : Type*) (valueAt : Z → Option V)
    (setValue : Z → V → Z) (clearValue pruneSubtrie : Z → Z) : Prop where
  setValue_valueAt : ∀ z v, valueAt (setValue z v) = some v
  clearValue_valueAt : ∀ z, valueAt (clearValue z) = none
  pruneSubtrie_clears : ∀ z, valueAt (pruneSubtrie z) = none

/-- Status correctness: `.identity` means the first operand is unchanged. -/
structure InPlaceStatusSpec {α : Type*} (op : α → α → α × AlgebraicStatus)
    [BEq α] : Prop where
  identity_means_unchanged : ∀ a b,
      (op a b).2 = .identity → ((op a b).1 == a) = true

/-! ## §2: In-Place Operations -/

/-- In-place meet, subtract, and restrict extending PathMap's `joinInto`. -/
class InPlaceMeetSubtractRestrict (α : Type*) where
  meetInto : α → α → α × AlgebraicStatus
  subtractInto : α → α → α × AlgebraicStatus
  restrictInto : α → α → α × AlgebraicStatus

/-! ## §3: FTrie.graft — Subtrie Replacement -/

-- upsertChild, graftAtPath, and graftAtPath_root are now in Trie/FiniteTrie.lean

/-! ## §4: Concrete FTrie In-Place Instance -/

private def ftrieInPlaceOp {V : Type*} [BEq V] (op : FTrie V → FTrie V → FTrie V)
    (a b : FTrie V) : FTrie V × AlgebraicStatus :=
  let result := op a b
  if result == a then (result, .identity)
  else if result == .empty then (result, .none)
  else (result, .modified)

instance {V : Type*} [BEq V] [LawfulBEq V] :
    InPlaceMeetSubtractRestrict (FTrie V) where
  meetInto := ftrieInPlaceOp FTrie.meet
  subtractInto := ftrieInPlaceOp FTrie.subtract
  restrictInto := ftrieInPlaceOp FTrie.restrict

/-! ## §5: Identity-Correctness Theorems -/

private theorem ftrieInPlaceOp_identity {V : Type*} [BEq V] [LawfulBEq V]
    (op : FTrie V → FTrie V → FTrie V) (a b : FTrie V)
    (h : (ftrieInPlaceOp op a b).2 = .identity) :
    ((ftrieInPlaceOp op a b).1 == a) = true := by
  delta ftrieInPlaceOp at h ⊢
  simp only at h ⊢
  split_ifs at h ⊢ with h1 h2 <;> first | exact h1 | exact absurd h (by decide)

theorem FTrie.meetInto_status {V : Type*} [BEq V] [LawfulBEq V] :
    InPlaceStatusSpec (α := FTrie V) (ftrieInPlaceOp FTrie.meet) where
  identity_means_unchanged a b h := ftrieInPlaceOp_identity FTrie.meet a b h

theorem FTrie.subtractInto_status {V : Type*} [BEq V] [LawfulBEq V] :
    InPlaceStatusSpec (α := FTrie V) (ftrieInPlaceOp FTrie.subtract) where
  identity_means_unchanged a b h := ftrieInPlaceOp_identity FTrie.subtract a b h

theorem FTrie.restrictInto_status {V : Type*} [BEq V] [LawfulBEq V] :
    InPlaceStatusSpec (α := FTrie V) (ftrieInPlaceOp FTrie.restrict) where
  identity_means_unchanged a b h := ftrieInPlaceOp_identity FTrie.restrict a b h

/-! ## §6: None-Status Correctness -/

private theorem ftrieInPlaceOp_none {V : Type*} [BEq V] [LawfulBEq V]
    (op : FTrie V → FTrie V → FTrie V) (a b : FTrie V)
    (h : (ftrieInPlaceOp op a b).2 = .none) :
    ((ftrieInPlaceOp op a b).1 == FTrie.empty) = true := by
  delta ftrieInPlaceOp at h ⊢
  simp only at h ⊢
  split_ifs at h ⊢ with h1 h2 <;> first | exact h2 | exact absurd h (by decide)

/-! ## §7: Summary

**0 sorries. 0 axioms.**

Contributions:
- `ZipperWritingSpec` — 3-law specification record for value mutations
- `InPlaceStatusSpec` — identity-status correctness specification
- `InPlaceMeetSubtractRestrict` — 3 in-place operation class
- `FTrie.graft` with `graft_root` / `graft_root_lookup`
- `FTrie` instance of `InPlaceMeetSubtractRestrict`
- 3 identity-correctness theorems + 1 none-correctness theorem
- Generic `ftrieInPlaceOp_identity` / `ftrieInPlaceOp_none` lemmas
-/

end Mettapedia.OSLF.PathMap
