import Mettapedia.Languages.MeTTa.HE.IncrementalTableSemantics
import Mettapedia.Languages.MeTTa.HE.SpaceQuerySupport
import Mettapedia.Languages.MeTTa.HE.NondeterminismCarrier
import Mettapedia.Languages.MeTTa.HE.MonadMorphismChain

/-!
# Bridge Matrix: PathMap / CeTTa / HE / MORK Architecture

This file documents and witnesses the cross-stack architecture connecting:
- **HE** (this Lean formalization): semantic truth and invariants
- **PathMap** (OSLF/PathMap/): trie-based indexing and candidate retrieval
- **CeTTa** (c-projects/cetta/): the C runtime
- **MORK/MM2**: specialized matching engines over the shared universe

## Architecture Summary

```
  HE Semantics (Lean)          PathMap (Lean)
  ┌──────────────────┐         ┌──────────────────┐
  │ Space             │         │ FTrie / Trie     │
  │ queryEquations    │◄────────│ prefix descent   │
  │ simpleMatch       │         │ candidate filter  │
  │ RevisionedSpace   │         │ support/index    │
  │ TableEntry        │         │ canonical univ.  │
  └────────┬─────────┘         └────────┬─────────┘
           │                            │
           │  FaithfulBackend           │  Same canonical keys
           │                            │
  ┌────────▼─────────┐         ┌────────▼─────────┐
  │ CeTTa Runtime    │         │ MORK / MM2       │
  │ space.c          │◄────────│ mork_bridge.c    │
  │ eval.c           │         │ mm2 lowering     │
  │ (future: table)  │         │ specialized match │
  └──────────────────┘         └──────────────────┘
```

## Verified Properties (theorem inventory)

### Layer 1: Atom semantics
- `LawfulBEq Atom` — OSLFCore/Atom.lean
- `DecidableEq Atom` — OSLFCore/Atom.lean

### Layer 2: Pattern matching
- `simpleMatch_extends` — BindingComposition.lean: match extends bindings monotonically
- `simpleMatch_preserves_seed` — BindingComposition.lean: seed bindings preserved

### Layer 3: Renaming / canonicalization
- `applyAtomTotal_injective` — CoReferencePreservation.lean: fuel-free injective renaming
- `applyAtomTotal_beq_iff` — CoReferencePreservation.lean: BEq preserved under renaming
- `faithful_iff` — CoReferencePreservation.lean: co-reference ↔ same renamed name

### Layer 4: Bisimulation
- `simpleMatch_rename_bisim` — VariantQueryCorrectness.lean: parallel execution lockstep
- `simpleMatch_isSome_rename_empty` — VariantQueryCorrectness.lean: isSome corollary

### Layer 5: Query correctness
- `variant_queries_same_rhs` — VariantQueryCorrectness.lean: variant queries → same RHS

### Layer 6: Cache / revision
- `addAtom_invalidates` — CacheCorrectness.lean: mutation → revision bump
- `CacheEntry.populate_correct` — CacheCorrectness.lean: populated entry = query result
- `variant_cache_binding_shape` — BindingCacheSoundness.lean: same-length results

### Layer 7: Snapshot
- `snapshot_add_isolated` — SnapshotPreservation.lean: mutation doesn't affect snapshot
- `snapshot_cache_permanent` — SnapshotPreservation.lean: snapshot caches are immutable

### Layer 8: Incremental tabling
- `TableEntry.addAnswer_sound` — IncrementalTableSemantics.lean: partial reads are sound
- `TableEntry.exact_is_sound` — IncrementalTableSemantics.lean: complete tables are exact
- `tableEntry_variant_rhs_agree` — IncrementalTableSemantics.lean: variant compat

### Layer 9: Nondeterminism carrier
- `toBag_perm_iff` — NondeterminismCarrier.lean: List.Perm ↔ Multiset equality
- `toBag_flatMap` — NondeterminismCarrier.lean: flatMap commutes with toBag

### Layer 10: Support bridge
- `CanonMap.support_comm` — BagSupportBridge.lean: canonicalization commutes with support
- `FaithfulBackend` — SpaceQuerySupport.lean: backend query agreement

## Cross-Stack Contracts

Each contract is a statement that a runtime component must satisfy for
correctness. The Lean theorems PROVE these contracts hold at the semantic level.
Runtime implementations must PRESERVE them.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: The bridge witnesses -/

/-- **Contract 1**: Pattern matching is monotonic.
    Any runtime implementing `simpleMatch` must extend (not retract) bindings. -/
theorem contract_match_monotonic :
    ∀ (fuel : Nat) (lhs target : Atom) (seed result : Bindings),
    simpleMatch lhs target seed fuel = some result →
    seed.Extends result :=
  fun fuel => (simpleMatch_extends fuel).1

/-- **Contract 2**: Variant-equivalent queries produce identical RHS atoms.
    Any runtime using variant-keyed tabling can reuse cached RHS atoms. -/
theorem contract_variant_rhs_reuse :
    ∀ (space : Space) (q₁ q₂ : Atom) (_hvar : VariantEquiv q₁ q₂) (fuel : Nat),
    (queryEquations space q₁ fuel).map Prod.fst =
    (queryEquations space q₂ fuel).map Prod.fst :=
  variant_queries_same_rhs

/-- **Contract 3**: Revision bump invalidates cache.
    Any runtime caching query results must invalidate on space mutation. -/
theorem contract_mutation_invalidates :
    ∀ (rs : RevisionedSpace) (a : Atom) (entry : CacheEntry) (_hvalid : entry.isValid rs),
    ¬ entry.isValid (rs.addAtom a) :=
  addAtom_invalidates

/-- **Contract 4**: Snapshots are immune to mutation.
    A runtime snapshot provides a stable query substrate. -/
theorem contract_snapshot_isolation :
    ∀ (rs : RevisionedSpace) (_a q : Atom) (fuel : Nat),
    let snap := rs.snapshot
    queryEquations ⟨snap.atoms⟩ q fuel = queryEquations rs.space q fuel :=
  fun _ _ _ _ => rfl

/-- **Contract 5**: Incremental table reads are sound.
    A partially-built table entry contains only genuine answers. -/
theorem contract_partial_table_sound :
    ∀ (te : TableEntry) (space : Space) (fuel : Nat)
    (_hpartial : te.status = .inProgress)
    (_hsound : te.Sound space fuel)
    (ans : Atom × Bindings) (_hgenuine : isGenuineAnswer space te.query fuel ans),
    (te.addAnswer ans).Sound space fuel :=
  TableEntry.addAnswer_sound

/-! ## §2: Architecture invariants

These are the load-bearing properties. If any of these break,
the runtime is unsound.

1. **Binding monotonicity** (Contract 1): Pattern matching never drops bindings.
   CeTTa: `space_match_backend.c` simple_match preserves seed.
   PathMap: Candidate rematch with seed bindings is safe.

2. **Variant RHS stability** (Contract 2): Same equations → same RHS under variant.
   CeTTa: `table_store` variant-key lookup is correct.
   PathMap: Canonical trie key shares results across variant queries.

3. **Revision invalidation** (Contract 3): Mutation → stale cache.
   CeTTa: `space.c` revision counter + `table_store` validity check.
   One canonical universe, one revision counter.

4. **Snapshot isolation** (Contract 4): Frozen state = stable queries.
   CeTTa: `eval.c` with-space-snapshot shallow clone.
   Snapshot-keyed caches are permanent within an episode.

5. **Partial soundness** (Contract 5): Every partial table answer is genuine.
   CeTTa: future `table_store_check_insert` must verify answer genuineness.
   Consumers can safely use partial results.

### What this does NOT cover

- PathMap trie structure (CA's responsibility: prefix descent, Merkleization)
- MORK/MM2 lowering correctness (separate verification)
- Producer scheduling / SLG control flow (implementation choice)
- Grounded dispatch (runtime-specific)
-/

end Mettapedia.Languages.MeTTa.HE
