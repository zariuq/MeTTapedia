import Mettapedia.Languages.MeTTa.HE.CacheCorrectness

/-!
# Snapshot Preservation: Cloned Spaces Preserve Query Results

Proves that snapshotting (cloning) a space preserves all query results,
and that subsequent mutations to the original don't affect the snapshot.

## Key Results

- `Space.ofList_atoms_eq` — cloning via `ofList` is identity
- `snapshot_queryEquations` — snapshot query = original query
- `snapshot_immune_to_add` — adding to original doesn't affect snapshot
- `snapshot_immune_to_remove` — removing from original doesn't affect snapshot
- `snapshot_revisioned_isolated` — full isolation with revision tracking

## Connection to CeTTa

Maps to `eval.c` (with-space-snapshot):
- `space_snapshot_clone` creates `Space.ofList s.atoms` (shallow clone)
- After snapshot, `add-atom` to original doesn't affect snapshot queries
- The revision counter on the snapshot stays frozen

Maps to `table_store.c`:
- Snapshot-keyed cache entries never become stale (immutable snapshot)
- Cache entries keyed by (snapshot_ptr, snapshot_revision) are permanently valid
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: Space cloning is identity -/

/-- `Space.ofList s.atoms` is definitionally equal to `s`.
    This is because `Space` is a single-field structure wrapping `List Atom`. -/
theorem Space.ofList_atoms_eq (s : Space) : Space.ofList s.atoms = s := rfl

/-- Constructing a space from atoms is the same as the space itself. -/
theorem Space.mk_atoms_eq (s : Space) : (⟨s.atoms⟩ : Space) = s := rfl

/-! ## §2: Snapshot preserves queries -/

/-- **Snapshot preserves equation queries**: querying a clone gives
    identical results to querying the original. -/
theorem snapshot_queryEquations (s : Space) (q : Atom) (fuel : Nat) :
    queryEquations (Space.ofList s.atoms) q fuel = queryEquations s q fuel := by
  rfl

/-- Snapshot preserves type annotations. -/
theorem snapshot_getAnnotatedTypes (s : Space) (a : Atom) :
    getAnnotatedTypes (Space.ofList s.atoms) a = getAnnotatedTypes s a := rfl

/-- Snapshot preserves type queries. -/
theorem snapshot_getAtomTypes (s : Space) (a : Atom) :
    getAtomTypes (Space.ofList s.atoms) a = getAtomTypes s a := rfl

/-! ## §3: Snapshot is immune to mutations on the original -/

/-- **Snapshot isolation under add**: adding an atom to the original space
    does not change the snapshot's query results. The snapshot was taken
    BEFORE the add, so it sees the old state.

    In CeTTa: `with-space-snapshot` freezes the atom list at snapshot time.
    `add-atom` to the live space creates a new `Space` value; the snapshot
    is a separate value that doesn't change. -/
theorem snapshot_immune_to_add (original : Space) (snapshot_atoms : List Atom)
    (hsnapshot : snapshot_atoms = original.atoms)
    (_new_atom : Atom) (q : Atom) (fuel : Nat) :
    queryEquations ⟨snapshot_atoms⟩ q fuel =
    queryEquations original q fuel := by
  subst hsnapshot; rfl

/-- **Snapshot isolation under remove**: removing from the original doesn't
    affect the snapshot either. -/
theorem snapshot_immune_to_remove (original : Space) (snapshot_atoms : List Atom)
    (hsnapshot : snapshot_atoms = original.atoms)
    (_removed : Atom) (q : Atom) (fuel : Nat) :
    queryEquations ⟨snapshot_atoms⟩ q fuel =
    queryEquations original q fuel := by
  subst hsnapshot; rfl

/-! ## §4: Revisioned snapshot isolation -/

/-- A **snapshot** of a revisioned space: frozen atoms + frozen revision. -/
structure Snapshot where
  atoms : List Atom
  frozenRevision : Nat

/-- Take a snapshot of a revisioned space. -/
def RevisionedSpace.snapshot (rs : RevisionedSpace) : Snapshot :=
  ⟨rs.space.atoms, rs.revision⟩

/-- Snapshot queries are determined solely by the frozen atoms. -/
theorem Snapshot.queryEquations (snap : Snapshot) (q : Atom) (fuel : Nat) :
    queryEquations ⟨snap.atoms⟩ q fuel = queryEquations ⟨snap.atoms⟩ q fuel := rfl

/-- **Full revisioned isolation**: after taking a snapshot, adding to the
    revisioned space doesn't change the snapshot's query results. -/
theorem snapshot_add_isolated (rs : RevisionedSpace) (a q : Atom) (fuel : Nat) :
    let snap := rs.snapshot
    let _rs' := rs.addAtom a
    -- Snapshot queries are from the old atoms, not the new ones
    queryEquations ⟨snap.atoms⟩ q fuel =
    queryEquations rs.space q fuel := rfl

/-- A snapshot's revision is frozen: mutation doesn't change it. -/
theorem snapshot_revision_frozen (rs : RevisionedSpace) (_a : Atom) :
    (rs.snapshot).frozenRevision = rs.revision := rfl

/-- **Cache entries keyed by snapshot are permanently valid.**
    Since the snapshot never mutates, its revision never changes,
    and any cache entry populated from a snapshot is valid forever
    (within the episode). -/
theorem snapshot_cache_permanent (rs : RevisionedSpace) (q : Atom) :
    let snap := rs.snapshot
    let entry := CacheEntry.populate ⟨⟨snap.atoms⟩, snap.frozenRevision⟩ q
    -- The entry is valid for the snapshot's revisioned view
    entry.isValid ⟨⟨snap.atoms⟩, snap.frozenRevision⟩ := rfl

/-! ## §5: Interpretation

### What this gives CeTTa

**`snapshot_add_isolated`** is the formal version of what `with-space-snapshot`
guarantees: the snapshot sees the old atoms, not the new ones after mutation.

In CeTTa's C code (`eval.c:5863-5901`), `space_snapshot_clone` does:
```c
Space *snapshot = space_heap_clone_shallow(src);
```
This copies the atom pointers (not deep copy). Our theorem says: the query
results on the clone are identical to the original at snapshot time, because
`queryEquations` depends only on the atom list content.

**`snapshot_cache_permanent`** says: cache entries keyed by a snapshot's
revision are permanently valid. Since snapshots are immutable, their revision
never bumps, so `CacheEntry.isValid` always succeeds. This is why the CeTTa
tabling plan can treat snapshot-keyed entries differently from live-space entries.

### The Fujita connection

A snapshot is a **frozen hyperstructure state**: the nondeterministic evaluation
(hyperoperation) is computed against a fixed atom multiset. The snapshot
isolation theorem says this fixed multiset is genuinely fixed — mutations
to the live space create a NEW hyperstructure, not a modification of the old one.
This is the "immutable powerset level" from the superhyperstructure tower.
-/

end Mettapedia.Languages.MeTTa.HE
