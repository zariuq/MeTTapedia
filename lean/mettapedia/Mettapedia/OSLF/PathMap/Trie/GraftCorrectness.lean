import Mettapedia.OSLF.PathMap.ZipperWritingLaws
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie

/-!
# Graft Correctness — setValue / clearValue / ZipperWritingSpec

Builds on the lookup theorems in `FiniteTrie.lean` (`graftAtPath_lookup_under`,
`graftAtPath_lookup_diff_head`) to define `setValue`/`clearValue` operations
and prove `FTrie` satisfies `ZipperWritingSpec`.

## Key Discovery

During formalization, we found a bug in the original `graftAtPath` definition:
`List.map` doesn't insert new children when the target byte is absent.
Fixed with `FTrie.upsertChild` (update-or-insert).
-/

namespace Mettapedia.OSLF.PathMap.Trie

open Mettapedia.OSLF.PathMap (ZipperWritingSpec)

universe u

variable {V : Type u}

/-! ## §1: setValue / clearValue via graftAtPath -/

/-- Set the value at a path by grafting a singleton. -/
def FTrie.setValueAt (t : FTrie V) (p : List UInt8) (v : V) : FTrie V :=
  t.graftAtPath p (FTrie.singleton [] v)

/-- Clear the value at the root (keeping children). -/
def FTrie.clearValueAtRoot : FTrie V → FTrie V
  | .empty => .empty
  | .node _ children => (FTrie.node none children).normalize

/-! ## §2: Lookup theorems for setValue / clearValue -/

/-- **Set-then-get at any path**: setValue then lookup returns the set value. -/
theorem FTrie.setValueAt_lookup (t : FTrie V) (p : List UInt8) (v : V) :
    (FTrie.setValueAt t p v).lookup p = some v := by
  simp only [FTrie.setValueAt]
  have h := FTrie.graftAtPath_lookup_under t (FTrie.singleton [] v) p []
  simp only [List.append_nil] at h
  exact h

/-- clearValueAtRoot then lookup at root returns none. -/
theorem FTrie.clearValueAtRoot_lookup (t : FTrie V) :
    (FTrie.clearValueAtRoot t).lookup [] = none := by
  match t with
  | .empty => rfl
  | .node _ children =>
    simp only [FTrie.clearValueAtRoot, FTrie.normalize]
    match children with
    | [] => rfl
    | _ :: _ => rfl

/-! ## §3: FTrie satisfies ZipperWritingSpec at root -/

/-- **FTrie satisfies ZipperWritingSpec**: a concrete type satisfies the
    abstract specification record. This closes the council's demand for
    a non-vacuous spec satisfaction proof. -/
theorem ftrieWritingSpec_root :
    ZipperWritingSpec (FTrie V) V
      (fun t => t.lookup [])
      (fun t v => FTrie.setValueAt t [] v)
      FTrie.clearValueAtRoot
      (fun _ => FTrie.empty) where
  setValue_valueAt _ _ := rfl
  clearValue_valueAt := FTrie.clearValueAtRoot_lookup
  pruneSubtrie_clears _ := rfl

/-! ## §4: Summary

**0 sorries. 0 axioms.**

Key theorems:
- `FTrie.setValueAt_lookup` — set-then-get at **any path** (uses graftAtPath_lookup_under)
- `FTrie.clearValueAtRoot_lookup` — clear-then-get at root
- `ftrieWritingSpec_root` — **FTrie satisfies ZipperWritingSpec** (non-vacuous)

The graft lookup theorems (`graftAtPath_lookup_under`, `graftAtPath_lookup_diff_head`,
`graftAtPath_lookup_nil_cons`) are in `FiniteTrie.lean` alongside the definitions,
where name resolution is clean.
-/

end Mettapedia.OSLF.PathMap.Trie
