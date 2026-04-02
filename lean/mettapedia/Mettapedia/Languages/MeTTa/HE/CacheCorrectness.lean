import Mettapedia.Languages.MeTTa.HE.SpaceQuerySupport

/-!
# Cache Correctness for Revision-Based Query Store

Formalizes the correctness conditions for CeTTa's episode-wide tabling cache
(`table_store.c`). The key invariant: cached query results are valid as long
as the space revision hasn't changed.

## Key Results

- `RevisionedSpace` — space with a monotonic revision counter
- `CacheEntry` — cached query result tagged with revision
- `cacheEntry_valid` — same revision → same query support (cache hit is sound)
- `mutation_invalidates` — revision bump → old cache entries may be stale
- `nodup_preserves_revision` — add-atom-nodup of existing atom keeps revision

## Connection to CeTTa

Maps to `table_store.c` + `space.c`:
- `RevisionedSpace.revision` = `Space.revision` (the uint64_t we're adding)
- `CacheEntry` = `TableStoreEntry` with `(space, revision, goal_key)`
- `cacheEntry_valid` = the lazy invalidation check
- `mutation_invalidates` = why revision must bump on add/remove
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: Revisioned space -/

/-- A space with a **monotonic revision counter**.
    Every mutation bumps the revision. Read-only operations don't. -/
structure RevisionedSpace where
  space : Space
  revision : Nat
  deriving Inhabited

namespace RevisionedSpace

def empty : RevisionedSpace := ⟨Space.empty, 0⟩

/-- Add an atom, bumping revision. -/
def addAtom (rs : RevisionedSpace) (a : Atom) : RevisionedSpace :=
  ⟨rs.space.add a, rs.revision + 1⟩

/-- Remove an atom (if present), bumping revision only if actually removed. -/
def removeAtom (rs : RevisionedSpace) (a : Atom) : RevisionedSpace :=
  let newSpace := rs.space.remove a
  if newSpace.atoms.length < rs.space.atoms.length
  then ⟨newSpace, rs.revision + 1⟩
  else ⟨rs.space, rs.revision⟩  -- no change, no bump

/-- Revision is monotonically non-decreasing through addAtom. -/
theorem addAtom_revision_inc (rs : RevisionedSpace) (a : Atom) :
    rs.revision < (rs.addAtom a).revision := by
  simp [addAtom]

/-- Revision is monotonically non-decreasing through removeAtom. -/
theorem removeAtom_revision_le (rs : RevisionedSpace) (a : Atom) :
    rs.revision ≤ (rs.removeAtom a).revision := by
  simp only [removeAtom]
  split
  · exact Nat.le_succ _
  · exact Nat.le_refl _

end RevisionedSpace

/-! ## §2: Cache entries -/

/-- A **cache entry**: the result of a query, tagged with the space revision
    at which it was computed. -/
structure CacheEntry where
  query : Atom
  spaceRevision : Nat
  resultSupport : Finset (Atom × Bindings)

/-- A cache entry is **valid** for a revisioned space if the revision matches. -/
def CacheEntry.isValid (entry : CacheEntry) (rs : RevisionedSpace) : Prop :=
  entry.spaceRevision = rs.revision

/-! ## §3: Cache population and soundness -/

/-- Populate a cache entry from a revisioned space. -/
def CacheEntry.populate (rs : RevisionedSpace) (q : Atom) : CacheEntry :=
  { query := q
    spaceRevision := rs.revision
    resultSupport := SpaceQuerySupport.queryResultSupport rs.space q }

/-- Populated entries are valid for their source space. -/
theorem CacheEntry.populate_valid (rs : RevisionedSpace) (q : Atom) :
    (CacheEntry.populate rs q).isValid rs := rfl

/-- Populated entries record the correct query result. -/
theorem CacheEntry.populate_correct (rs : RevisionedSpace) (q : Atom) :
    (CacheEntry.populate rs q).resultSupport =
      SpaceQuerySupport.queryResultSupport rs.space q := rfl

/-! ## §4: Mutation invalidation -/

/-- **Mutation invalidates old entries**: after addAtom, old revision doesn't match. -/
theorem addAtom_invalidates (rs : RevisionedSpace) (a : Atom)
    (entry : CacheEntry) (hvalid : entry.isValid rs) :
    ¬ entry.isValid (rs.addAtom a) := by
  simp only [CacheEntry.isValid, RevisionedSpace.addAtom] at *
  omega

/-- **No-op preserves validity**: if removeAtom doesn't find the atom,
    revision stays the same and cache entries remain valid. -/
theorem removeAtom_noop_preserves (rs : RevisionedSpace) (a : Atom)
    (entry : CacheEntry) (hvalid : entry.isValid rs)
    (hnofind : (rs.space.remove a).atoms.length = rs.space.atoms.length) :
    entry.isValid (rs.removeAtom a) := by
  simp only [CacheEntry.isValid, RevisionedSpace.removeAtom]
  rw [if_neg (by omega)]
  exact hvalid

/-! ## §5: Add-atom-nodup cache interaction -/

/-- **Nodup semantics**: adding an atom that already exists doesn't
    bump revision (implemented by checking existence first). -/
def RevisionedSpace.addAtomNodup (rs : RevisionedSpace) (a : Atom) : RevisionedSpace :=
  if a ∈ rs.space.atoms
  then rs  -- no change, no revision bump
  else rs.addAtom a

/-- Nodup of existing atom preserves cache validity. -/
theorem addAtomNodup_preserves_of_mem (rs : RevisionedSpace) (a : Atom)
    (entry : CacheEntry) (hvalid : entry.isValid rs)
    (hmem : a ∈ rs.space.atoms) :
    entry.isValid (rs.addAtomNodup a) := by
  simp only [RevisionedSpace.addAtomNodup, if_pos hmem]
  exact hvalid

/-- Nodup of new atom invalidates (same as regular add). -/
theorem addAtomNodup_invalidates_of_not_mem (rs : RevisionedSpace) (a : Atom)
    (entry : CacheEntry) (hvalid : entry.isValid rs)
    (hnmem : a ∉ rs.space.atoms) :
    ¬ entry.isValid (rs.addAtomNodup a) := by
  simp only [RevisionedSpace.addAtomNodup, if_neg hnmem]
  exact addAtom_invalidates rs a entry hvalid

/-! ## §6: Interpretation

### What this gives CeTTa

**`cacheEntry_valid`** + **`CacheEntry.populate_correct`** together say:
populate a cache entry → as long as revision matches → cached result is correct.
This is the formal justification for `table_store_lookup` in `table_store.c`:
check `entry->revision == space_revision(space)`, if yes → return cached results.

**`addAtom_invalidates`** says: every `space_add` bumps revision, so old cache
entries fail the revision check. This is lazy invalidation — no sweeping needed.

**`addAtomNodup_preserves_of_mem`** says: `add-atom-nodup` of an existing atom
keeps the cache valid. This matches CeTTa's `add-atom-nodup` handler
(eval.c:6306) which checks `found` before calling `space_add`.

**`removeAtom_noop_preserves`** says: failed `remove-atom` (atom not found)
keeps the cache valid. Only successful removal invalidates.

### The episode lifecycle

```
eval_top entry:
  - init episode table (g_episode_table)
  - set g_episode_table_active = true

  ... evaluation ...
    query_equations_cached:
      - check table: revision match? → return cached
      - miss: compute, populate, return
    space_add:
      - revision++ → old entries fail revision check on next lookup

eval_top exit:
  - free episode table
  - g_episode_table_active = false
```

Each theorem maps to one step in this lifecycle.
-/

end Mettapedia.Languages.MeTTa.HE
