import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.HuetZipper
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement

/-!
# Product Overlay Zipper: Multi-View Trie Navigation

Formalizes the overlay pattern for PathMap: a local trie overlays a base trie,
with local values taking priority. This models CeTTa's scoped space semantics
where local bindings shadow global atoms.

## Key Concepts

- `OverlayTrie` — a pair of tries (base, local) with overlay lookup
- `overlay_lookup` — local-first lookup (shadows base)
- `overlay_is_join` — overlay lookup equals left-biased join lookup
- `overlayDescend` — simultaneous descent into both tries

## CeTTa Mapping

- `with-space-snapshot` creates a local overlay
- Local `add-atom` goes to the local trie; base is frozen
- Query descends both tries; local results shadow base results
-/

namespace Mettapedia.OSLF.PathMap

open Trie (FTrie)

/-! ## §1: Overlay Trie -/

/-- An **overlay trie**: local values shadow base values at the same path. -/
structure OverlayTrie (V : Type*) where
  /-- The base (global) trie. -/
  base : FTrie V
  /-- The local (scoped) trie. -/
  local_ : FTrie V

/-- Overlay lookup: check local first, fall back to base. -/
def OverlayTrie.lookup (ot : OverlayTrie V) (path : List UInt8) : Option V :=
  (ot.local_.lookup path) <|> (ot.base.lookup path)

/-- An empty overlay (both tries empty). -/
def OverlayTrie.empty : OverlayTrie V := ⟨.empty, .empty⟩

/-- Add a value to the local trie (doesn't touch base). -/
def OverlayTrie.addLocal (ot : OverlayTrie V) (path : List UInt8) (v : V) :
    OverlayTrie V :=
  { ot with local_ := FTrie.join (FTrie.singleton path v) ot.local_ }

/-! ## §2: Overlay ↔ Join Connection -/

/-- **Overlay lookup equals left-biased join lookup** (for sorted tries).
    The join of (local, base) with local-biased values gives the same
    lookup behavior as the overlay. -/
theorem overlay_lookup_eq_join (ot : OverlayTrie V) (path : List UInt8)
    (hsl : ot.local_.Sorted) (hsb : ot.base.Sorted) :
    ot.lookup path = (FTrie.join ot.local_ ot.base).lookup path := by
  simp only [OverlayTrie.lookup]
  rw [FTrie.join_lookup _ _ _ hsl hsb]

/-! ## §3: Overlay Properties -/

/-- Adding to local doesn't change base lookup. -/
theorem OverlayTrie.addLocal_base_unchanged (ot : OverlayTrie V)
    (path : List UInt8) (v : V) :
    (ot.addLocal path v).base = ot.base := rfl

/-- Empty local overlay gives base lookup. -/
theorem OverlayTrie.empty_local_is_base (base : FTrie V) (path : List UInt8) :
    (OverlayTrie.mk base .empty).lookup path = base.lookup path := by
  simp [OverlayTrie.lookup, FTrie.lookup]

/-- Local value shadows base value. -/
theorem OverlayTrie.local_shadows (ot : OverlayTrie V) (path : List UInt8)
    (v : V) (hlocal : ot.local_.lookup path = some v) :
    ot.lookup path = some v := by
  simp [OverlayTrie.lookup, hlocal, Option.orElse]

/-- When local has no value, base shows through. -/
theorem OverlayTrie.base_shows_through (ot : OverlayTrie V) (path : List UInt8)
    (hnone : ot.local_.lookup path = none) :
    ot.lookup path = ot.base.lookup path := by
  simp [OverlayTrie.lookup, hnone, Option.orElse]

/-! ## §4: Simultaneous Descent -/

/-- Descend one byte in both tries of an overlay. -/
def OverlayTrie.descendByte (ot : OverlayTrie V) (b : UInt8) :
    OverlayTrie V :=
  ⟨ot.base.subtreeAt [b], ot.local_.subtreeAt [b]⟩

/-- Descent commutes with lookup via subtreeAt_lookup. -/
theorem OverlayTrie.descendByte_lookup (ot : OverlayTrie V) (b : UInt8)
    (suffix : List UInt8) :
    (ot.descendByte b).lookup suffix =
    ot.lookup (b :: suffix) := by
  simp only [descendByte, lookup]
  simp only [FTrie.subtreeAt_lookup, List.singleton_append]

/-- Multi-byte descent. -/
def OverlayTrie.descendPath (ot : OverlayTrie V) : List UInt8 → OverlayTrie V
  | [] => ot
  | b :: rest => (ot.descendByte b).descendPath rest

/-- Multi-byte descent commutes with lookup. -/
theorem OverlayTrie.descendPath_lookup (ot : OverlayTrie V) (pfx suffix : List UInt8) :
    (ot.descendPath pfx).lookup suffix =
    ot.lookup (pfx ++ suffix) := by
  induction pfx generalizing ot with
  | nil => rfl
  | cons b rest ih =>
    simp only [descendPath, List.cons_append]
    rw [ih, descendByte_lookup]

/-! ## §5: Summary

**0 sorries. 0 axioms.**

Key theorems:
- `overlay_lookup_eq_join` — overlay lookup agrees with left-biased join
- `addLocal_base_unchanged` — adding locally doesn't touch base
- `empty_local_is_base` — empty local = base lookup
- `local_shadows` — local value wins when present
- `base_shows_through` — base value shows when local is absent
- `descendByte_lookup` — single-byte descent commutes with lookup
- `descendPath_lookup` — multi-byte descent commutes with lookup

Maps to CeTTa: `with-space-snapshot`, scoped space semantics, overlay queries.
-/

end Mettapedia.OSLF.PathMap
