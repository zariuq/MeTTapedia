import Mettapedia.OSLF.PathMap.Trie.GraftCorrectness
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie

/-!
# Subtrie vs Snapshot Semantics

This file makes explicit the distinction between two different nouns that had
previously been easy to conflate:

- a **structural subtrie export**, which keeps the descendants below the focus
  but clears any value at the focus itself
- a **rooted focus snapshot**, which keeps the descendants and also re-exposes
  the focus value at the empty path `[]`

This matches the Rust split between `try_make_map` / `make_map` and the newer
`try_make_snapshot_map` / `make_snapshot_map`.
-/

namespace Mettapedia.OSLF.PathMap.Trie

open FTrie

universe u

variable {V : Type u}

/-- The rooted focus snapshot at `pfx`: descend to the focus and keep its root value. -/
def FTrie.snapshotAt (t : FTrie V) (pfx : List UInt8) : FTrie V :=
  t.subtreeAt pfx

/-- The structural subtrie export at `pfx`: descend to the focus and clear its root value. -/
def FTrie.structuralSubtrieAt (t : FTrie V) (pfx : List UInt8) : FTrie V :=
  (t.subtreeAt pfx).clearValueAtRoot

/-- Restore a value at the root of a trie while preserving its descendants. -/
def FTrie.withRootValue : FTrie V → V → FTrie V
  | .empty, v => FTrie.singleton [] v
  | .node _ children, v => FTrie.node (some v) children

/-! ## §1: Root vs descendant lookup behavior -/

/-- A rooted focus snapshot preserves the focus value at the empty path. -/
theorem FTrie.snapshotAt_lookup_nil (t : FTrie V) (pfx : List UInt8) :
    (t.snapshotAt pfx).lookup [] = t.lookup pfx := by
  simpa [FTrie.snapshotAt] using FTrie.subtreeAt_lookup t pfx []

/-- `clearValueAtRoot` clears only the root value; descendant lookups are preserved. -/
theorem FTrie.clearValueAtRoot_lookup_cons (t : FTrie V) (b : UInt8) (suffix : List UInt8) :
    (t.clearValueAtRoot).lookup (b :: suffix) = t.lookup (b :: suffix) := by
  cases t with
  | empty =>
      rfl
  | node val children =>
      cases children with
      | nil =>
          rfl
      | cons head tail =>
          rfl

/-- A structural subtrie export never reintroduces a value at the empty path. -/
theorem FTrie.structuralSubtrieAt_lookup_nil (t : FTrie V) (pfx : List UInt8) :
    (t.structuralSubtrieAt pfx).lookup [] = none := by
  simp [FTrie.structuralSubtrieAt, FTrie.clearValueAtRoot_lookup]

/-- A structural subtrie export preserves all strict descendants below the focus. -/
theorem FTrie.structuralSubtrieAt_lookup_cons
    (t : FTrie V) (pfx : List UInt8) (b : UInt8) (suffix : List UInt8) :
    (t.structuralSubtrieAt pfx).lookup (b :: suffix) = t.lookup (pfx ++ b :: suffix) := by
  rw [FTrie.structuralSubtrieAt, FTrie.clearValueAtRoot_lookup_cons]
  simpa using FTrie.subtreeAt_lookup t pfx (b :: suffix)

/-- The rooted focus snapshot and the structural subtrie export differ only at the root. -/
theorem FTrie.snapshotAt_lookup_cases (t : FTrie V) (pfx q : List UInt8) :
    (t.snapshotAt pfx).lookup q =
      match q with
      | [] => t.lookup pfx
      | b :: suffix => (t.structuralSubtrieAt pfx).lookup (b :: suffix) := by
  cases q with
  | nil =>
      simp [FTrie.snapshotAt_lookup_nil]
  | cons b suffix =>
      simp
      rw [FTrie.structuralSubtrieAt_lookup_cons]
      simpa [FTrie.snapshotAt] using FTrie.subtreeAt_lookup t pfx (b :: suffix)

/-! ## §2: Reconstructing the snapshot from the structural export -/

/-- If the focus has no value, the structural export and rooted snapshot have the same lookup
    behavior at every path. -/
theorem FTrie.snapshotAt_lookup_eq_structuralSubtrieAt_of_lookup_none
    (t : FTrie V) (pfx q : List UInt8) (hnone : t.lookup pfx = none) :
    (t.snapshotAt pfx).lookup q = (t.structuralSubtrieAt pfx).lookup q := by
  cases q with
  | nil =>
      simp [FTrie.snapshotAt_lookup_nil, hnone, FTrie.structuralSubtrieAt_lookup_nil]
  | cons b suffix =>
      rw [FTrie.structuralSubtrieAt_lookup_cons]
      simpa [FTrie.snapshotAt] using FTrie.subtreeAt_lookup t pfx (b :: suffix)

/-- `withRootValue` restores the requested root value. -/
theorem FTrie.withRootValue_lookup_nil (t : FTrie V) (v : V) :
    (t.withRootValue v).lookup [] = some v := by
  cases t <;> rfl

/-- `withRootValue` preserves all descendants. -/
theorem FTrie.withRootValue_lookup_cons (t : FTrie V) (v : V) (b : UInt8) (suffix : List UInt8) :
    (t.withRootValue v).lookup (b :: suffix) = t.lookup (b :: suffix) := by
  cases t with
  | empty =>
      rfl
  | node val children =>
      rfl

/-- If the focus has a value, restoring that root value on the structural export
    reconstructs the rooted snapshot extensionally. -/
theorem FTrie.withRootValue_structuralSubtrieAt_lookup_eq_snapshotAt
    (t : FTrie V) (pfx q : List UInt8) (v : V) (hsome : t.lookup pfx = some v) :
    ((t.structuralSubtrieAt pfx).withRootValue v).lookup q = (t.snapshotAt pfx).lookup q := by
  cases q with
  | nil =>
      simp [FTrie.withRootValue_lookup_nil, FTrie.snapshotAt_lookup_nil, hsome]
  | cons b suffix =>
      rw [FTrie.withRootValue_lookup_cons, FTrie.structuralSubtrieAt_lookup_cons]
      symm
      simpa [FTrie.snapshotAt] using FTrie.subtreeAt_lookup t pfx (b :: suffix)

/-! ## §3: Concrete examples -/

def rootedExample : FTrie Unit :=
  FTrie.node none
    [(10, FTrie.node (some ()) [(20, FTrie.singleton [] ())])]

/-- Positive example: the rooted snapshot re-exposes the focus value at `[]`. -/
example :
    (rootedExample.snapshotAt [10]).lookup [] = some () := by
  simp [rootedExample, FTrie.snapshotAt, FTrie.subtreeAt, FTrie.lookup]

/-- Negative example: the structural subtrie export does not fabricate that root value. -/
example :
    (rootedExample.structuralSubtrieAt [10]).lookup [] = none := by
  simp [rootedExample, FTrie.structuralSubtrieAt_lookup_nil]

/-- Positive example: descendants are still preserved by the structural export. -/
example :
    (rootedExample.structuralSubtrieAt [10]).lookup [20] = some () := by
  simpa [rootedExample, FTrie.lookup, FTrie.lookupChild, FTrie.singleton] using
    (FTrie.structuralSubtrieAt_lookup_cons rootedExample [10] 20 [])

/-! ## §4: Summary

**0 sorries. 0 axioms.**

Key theorems:
- `snapshotAt_lookup_nil` — rooted snapshot keeps the focus value at `[]`
- `structuralSubtrieAt_lookup_nil` — structural export clears the root value
- `structuralSubtrieAt_lookup_cons` — structural export preserves descendants
- `snapshotAt_lookup_cases` — the two views differ only at the root
- `snapshotAt_lookup_eq_structuralSubtrieAt_of_lookup_none` — no-root-value case collapses extensionally
- `withRootValue_structuralSubtrieAt_lookup_eq_snapshotAt` — snapshot = structural export + root graft, extensionally

This is the theorem packet that pins down the chosen Rust ontology:
`make_map` is the structural export, and `make_snapshot_map` is the rooted focus
snapshot.
-/

end Mettapedia.OSLF.PathMap.Trie
