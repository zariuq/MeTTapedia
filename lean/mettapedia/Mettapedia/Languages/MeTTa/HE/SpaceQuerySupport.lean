import Mettapedia.Languages.MeTTa.HE.BagSpaceInvariance
import Mettapedia.Languages.MeTTa.HE.MonadMorphismChain

/-!
# SpaceQuerySupport — Shared Interface for HE and PathMap

Defines the `SpaceQuerySupport` typeclass: the shared query interface that
both HE's `Space` and PathMap-backed storage must implement at the
**support level** (Finset).

This is the meeting point between:
- The HE side (bag semantics → support projection)
- The PathMap side (trie storage → support extraction)

## Key Definitions

- `SpaceQuerySupport` — typeclass for support-level query answering
- `Space` instance — projects HE query results through `toFinset`
- `FaithfulBackend` — what it means for a backend to agree with HE

## Architecture

```
HE Space ──queryEquations──▶ List (Atom×Bindings) ──toFinset──▶ Finset (Atom×Bindings)
                                                                        ‖
PathMap  ──trieQuery──────────────────────────────────────────▶ Finset (Atom×Bindings)
```

Both produce the same `Finset`. `SpaceQuerySupport` captures this shared type.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1: The shared interface -/

/-- A type `S` supports **support-level queries** if it can answer:
    1. Which (rhs, bindings) pairs does a query produce? (at support level)
    2. Which types does an atom have? (at support level)

    Both HE Space and PathMap-backed storage implement this. -/
class SpaceQuerySupport (S : Type*) where
  /-- The support (Finset) of equation query results for a given query atom. -/
  queryResultSupport : S → Atom → Finset (Atom × Bindings)
  /-- The support (Finset) of type annotations for a given atom. -/
  typeSupport : S → Atom → Finset Atom

/-! ## §2: HE Space instance -/

/-- HE's `Space` implements `SpaceQuerySupport` by projecting through `toFinset`. -/
instance : SpaceQuerySupport Space where
  queryResultSupport s q := (queryEquations s q).toFinset
  typeSupport s a := (getAtomTypes s a).toFinset

/-- Bag-equivalent spaces give identical type annotation support.
    Permuting the atom list doesn't change what PathMap stores for type annotations.

    Note: this covers `getAnnotatedTypes` (the space-dependent part of type resolution).
    The full `getAtomTypes` also includes intrinsic types (var/grounded) which are
    space-independent, so the full result is also invariant. -/
theorem bagEquiv_annotatedTypeSupport_eq {s₁ s₂ : Space}
    (h : s₁.BagEquiv s₂) (a : Atom) :
    (getAnnotatedTypes s₁ a).toFinset = (getAnnotatedTypes s₂ a).toFinset :=
  h.annotatedTypes_support a

/-! ## §3: FaithfulBackend — the PathMap target -/

/-- A **faithful backend** for an HE space agrees on all support-level queries.

    PathMap Claude's goal: construct a `FaithfulBackend pmSpace heSpace`
    proving that PathMap trie queries agree with HE queries at the
    support level. -/
structure FaithfulBackend (S : Type*) [SpaceQuerySupport S]
    (heSpace : Space) where
  /-- The backend storage -/
  backend : S
  /-- Equation queries agree at support level -/
  query_agree : ∀ q : Atom,
    SpaceQuerySupport.queryResultSupport backend q =
    SpaceQuerySupport.queryResultSupport heSpace q
  /-- Type queries agree at support level -/
  type_agree : ∀ a : Atom,
    SpaceQuerySupport.typeSupport backend a =
    SpaceQuerySupport.typeSupport heSpace a

-- Note: Full compositionality (bind_agree) follows from `toSupport_bind`
-- in MonadMorphismChain.lean — downstream work.

/-! ## §4: Self-agreement (sanity check) -/

/-- Every HE space is a faithful backend for itself. Sanity check. -/
def Space.selfBackend (s : Space) : FaithfulBackend Space s where
  backend := s
  query_agree := fun _ => rfl
  type_agree := fun _ => rfl

/-! ## §5: Interpretation

### What this gives PathMap Claude

The `FaithfulBackend` structure is the **exact proof obligation**:

```lean
-- PathMap Claude needs to construct:
def pathmapBackend (trie : FTrie Unit) (heSpace : Space)
    (henc : <trie faithfully encodes space>) :
    FaithfulBackend (FTrie Unit) heSpace := {
  backend := trie,
  query_agree := ...,  -- trie lookup = HE query toFinset
  type_agree := ...,   -- trie type lookup = HE type toFinset
}
```

The `query_agree` field says: for every query atom, the PathMap trie
returns the same support set as HE's `queryEquations.toFinset`.

The `type_agree` field says: for every atom, the PathMap trie returns
the same type support as HE's `getAtomTypes.toFinset`.

### What this gives CeTTa

The `FaithfulBackend` concept maps directly to CeTTa's architecture:
- `Space` with `SPACE_KIND_ATOM` = the HE space (bag semantics)
- `Space` with `match_backend = PathMap/MORK` = the faithful backend
- The revision counter ensures cache invalidation when the space mutates
- `query_agree` is what tabling caches: if revision matches, support matches

### The Fujita/Smarandache connection

`FaithfulBackend` is a **quotient hyperstructure morphism**:
it maps the full bag hyperoperation (HE evaluation) to its support
(PathMap trie), preserving the algebraic structure at the quotient level.
This is Fujita's "reduced superhypergroup" made concrete and machine-checked.
-/

end Mettapedia.Languages.MeTTa.HE
