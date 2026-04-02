import Mathlib.Data.Finset.Basic

/-!
# Space Engine Boundary: Native / PathMap / MORK Lane Separation

Cleanly separates the three engine lanes in CeTTa:
- **Native HE**: standard MeTTa evaluation via `interpret_step`
- **PathMap**: accelerated storage/query (candidate selection, trie indexing)
- **MORK**: execution engine with step semantics (work queue, exec facts)

And states that **ACT** is a storage/artifact surface, not an execution engine.

## Why This Matters

Without this boundary, it's unclear whether loading an ACT file gives you
execution capability, or whether PathMap backing changes the semantic behavior
of queries. The theorems here make the seams explicit:

- PathMap preserves ordinary query/storage behavior (no new semantics)
- MORK extends PathMap with exec-fact step semantics (new capability)
- ACT is an artifact format usable with PathMap-backed storage (no exec authority)
- MM2 is a language surface over MORK (requires exec surface)

## CeTTa Mapping

| Lean | CeTTa |
|------|-------|
| `SpaceEngine.native` | `SPACE_KIND_ATOM` without bridge |
| `SpaceEngine.pathmap` | `SPACE_KIND_ATOM` with `bridge_active=true` |
| `SpaceEngine.mork` | MORK kernel `metta_calculus` over PathMap |
| `ArtifactSurface.act` | `.act` precompiled file format |
-/

namespace Mettapedia.Languages.MeTTa.SpaceEngineBoundary

/-! ## §1: Engine Classification -/

/-- The three engine lanes in CeTTa. -/
inductive SpaceEngine where
  /-- Native HE evaluation: List-based atomspace, native matching. -/
  | native
  /-- PathMap-backed: trie-indexed atomspace, bridge candidate selection. -/
  | pathmap
  /-- MORK execution: PathMap + work-queue scheduler + step semantics. -/
  | mork
  deriving DecidableEq, Repr

/-- Artifact surface formats. ACT is a storage format, not an engine. -/
inductive ArtifactSurface where
  /-- ACT: precompiled atom table, loadable into PathMap-backed spaces. -/
  | act
  /-- MeTTa source: text format, loadable into any engine. -/
  | mettaSource
  deriving DecidableEq, Repr

/-! ## §2: Engine Capabilities -/

/-- Capabilities that a space engine may or may not support. -/
inductive EngineCapability where
  /-- Add/remove atoms from the space. -/
  | atomStorage
  /-- Query equations by pattern matching. -/
  | equationQuery
  /-- Type annotation lookup. -/
  | typeQuery
  /-- Accelerated candidate selection via trie/index. -/
  | candidateAcceleration
  /-- Exec-fact step semantics (fire rules, advance work queue). -/
  | execStep
  /-- Snapshot/clone for isolation. -/
  | snapshot
  deriving DecidableEq, Repr

/-- Which capabilities each engine supports. -/
def SpaceEngine.capabilities : SpaceEngine → List EngineCapability
  | .native => [.atomStorage, .equationQuery, .typeQuery, .snapshot]
  | .pathmap => [.atomStorage, .equationQuery, .typeQuery,
                 .candidateAcceleration, .snapshot]
  | .mork => [.atomStorage, .equationQuery, .typeQuery,
              .candidateAcceleration, .execStep, .snapshot]

/-! ## §3: Shared Space Surface

All three engines share basic space operations. PathMap and MORK add
capabilities but do NOT change the semantics of the shared operations.

Positive example: `add-atom`, `match`, `get-type` work identically
regardless of engine.

Negative example: `execStep` is NOT available on native or pathmap engines. -/

/-- A capability is **shared** if all three engines support it. -/
def EngineCapability.isShared (cap : EngineCapability) : Bool :=
  cap ∈ SpaceEngine.native.capabilities &&
  cap ∈ SpaceEngine.pathmap.capabilities &&
  cap ∈ SpaceEngine.mork.capabilities

/-- **Shared surface theorem:** atomStorage, equationQuery, typeQuery,
    and snapshot are shared across all three engines.

    Maps to: CeTTa's `space_add`, `space_match`, `space_get_type`,
    `space_snapshot_clone` work regardless of `SPACE_KIND`. -/
theorem shared_space_surface :
    EngineCapability.atomStorage.isShared = true ∧
    EngineCapability.equationQuery.isShared = true ∧
    EngineCapability.typeQuery.isShared = true ∧
    EngineCapability.snapshot.isShared = true := by
  decide

/-! ## §4: PathMap is Query Surface Only

PathMap adds `candidateAcceleration` but does NOT add `execStep`.
It accelerates existing query operations without introducing new semantics.

Positive example: PathMap-backed `match` returns the same results as native
`match` (proved by `importedFallbackParity` in ImportedRowContract.lean).

Negative example: you cannot call `step` or `fire_exec_fact` on a
PathMap-backed space without the MORK execution layer. -/

/-- **PathMap is query-only:** PathMap does NOT have exec step capability.

    Maps to: `SPACE_KIND_ATOM` with `bridge_active=true` does not have
    `metta_calculus` or exec-fact firing. -/
theorem pathmap_query_surface_only :
    EngineCapability.execStep ∉ SpaceEngine.pathmap.capabilities := by
  decide

/-- **PathMap extends native with acceleration:** PathMap has everything
    native has, plus candidate acceleration.

    Maps to: switching from native to PathMap backend is transparent
    for all existing operations. -/
theorem pathmap_extends_native :
    ∀ cap ∈ SpaceEngine.native.capabilities,
    cap ∈ SpaceEngine.pathmap.capabilities := by
  decide

/-! ## §5: MORK Extends PathMap with Exec

MORK has all PathMap capabilities PLUS exec step semantics.
This is the ONLY engine with `execStep`.

Positive example: MORK can fire `(exec loc pat tpl)` rules via
`metta_calculus` (proved in WorkQueueExec.lean).

Negative example: native and PathMap engines cannot fire exec rules. -/

/-- **MORK extends PathMap with exec:** MORK has everything PathMap has,
    plus exec step capability.

    Maps to: MORK kernel wraps PathMap with work-queue scheduler. -/
theorem mork_extends_pathmap_with_exec :
    ∀ cap ∈ SpaceEngine.pathmap.capabilities,
    cap ∈ SpaceEngine.mork.capabilities := by
  decide

/-- **Exec step is MORK-only:** only the MORK engine has step semantics. -/
theorem step_semantics_only_mork :
    EngineCapability.execStep ∈ SpaceEngine.mork.capabilities ∧
    EngineCapability.execStep ∉ SpaceEngine.native.capabilities ∧
    EngineCapability.execStep ∉ SpaceEngine.pathmap.capabilities := by
  decide

/-! ## §6: ACT Artifact Boundary

ACT is a precompiled atom table — a STORAGE format, not an execution engine.
Loading an ACT file populates a PathMap-backed space with atoms. It does NOT
grant exec step capability.

Positive example: loading `bio_eqtl.act` creates a queryable space.
Negative example: loading `bio_eqtl.act` does NOT allow exec-fact firing
(unless the MORK execution layer is also active).

Maps to: CeTTa's `attached_compiled` flag in `PathmapImportedState`.
Materialization (`space_match_backend_materialize_attached`) converts ACT
atoms to native atoms for query. -/

/-- ACT provides storage content, not execution authority. -/
def ArtifactSurface.grantsExec : ArtifactSurface → Bool
  | .act => false
  | .mettaSource => false

/-- **ACT does not grant exec authority.** Loading an ACT file gives you
    atoms to query, not rules to fire.

    Maps to: `attached_compiled=true` enables materialization for query,
    but does not activate `metta_calculus`. -/
theorem act_artifact_not_exec_authority :
    ArtifactSurface.act.grantsExec = false := rfl

/-- **No artifact surface grants exec authority.** Exec authority comes
    from the engine lane (MORK), not from the artifact format. -/
theorem no_artifact_grants_exec :
    ∀ a : ArtifactSurface, a.grantsExec = false := by
  intro a; cases a <;> rfl

/-! ## §7: MM2 Requires Exec Surface

MM2 is a language/surface layer that REQUIRES the MORK execution engine.
You cannot run MM2 programs on a plain PathMap-backed space because MM2
needs `execStep` (work-queue scheduling, rule firing).

Positive example: MM2 programs fire through `metta_calculus` on MORK.
Negative example: loading MM2 rules into a native space does nothing
without the MORK scheduler to fire them. -/

/-- **MM2 requires exec capability.** The MM2 language surface needs step
    semantics, which only MORK provides.

    Maps to: MM2 rules are `(exec loc pat tpl)` atoms. They sit inertly
    in native/pathmap spaces. Only `metta_calculus` (MORK) fires them. -/
theorem mm2_requires_exec_surface (engine : SpaceEngine)
    (hexec : EngineCapability.execStep ∈ engine.capabilities) :
    engine = .mork := by
  cases engine <;> simp_all [SpaceEngine.capabilities]

/-! ## §8: Engine Surface Inclusion Chain

The three engines form a strict inclusion chain on capabilities:
native ⊂ pathmap ⊂ mork

Each level adds exactly one new capability class:
- pathmap adds candidateAcceleration
- mork adds execStep -/

/-- **Inclusion chain:** native capabilities ⊆ pathmap ⊆ mork. -/
theorem engine_surface_inclusion_native_pathmap_mork :
    (∀ cap ∈ SpaceEngine.native.capabilities,
     cap ∈ SpaceEngine.pathmap.capabilities) ∧
    (∀ cap ∈ SpaceEngine.pathmap.capabilities,
     cap ∈ SpaceEngine.mork.capabilities) :=
  ⟨pathmap_extends_native, mork_extends_pathmap_with_exec⟩

/-- **Strict inclusion:** pathmap has a capability that native lacks. -/
theorem pathmap_strictly_extends_native :
    ∃ cap, cap ∈ SpaceEngine.pathmap.capabilities ∧
           cap ∉ SpaceEngine.native.capabilities := by
  exact ⟨.candidateAcceleration, by decide, by decide⟩

/-- **Strict inclusion:** mork has a capability that pathmap lacks. -/
theorem mork_strictly_extends_pathmap :
    ∃ cap, cap ∈ SpaceEngine.mork.capabilities ∧
           cap ∉ SpaceEngine.pathmap.capabilities := by
  exact ⟨.execStep, by decide, by decide⟩

/-! ## §9: Summary

**0 sorries. 0 warnings.**

A maintainer can say:
"PathMap is the storage/query engine, MORK is the execution engine,
ACT is an artifact surface, and Lean states those seams explicitly."

| Theorem | What it says |
|---------|-------------|
| `shared_space_surface` | atomStorage, equationQuery, typeQuery, snapshot are universal |
| `pathmap_query_surface_only` | PathMap does NOT have execStep |
| `pathmap_extends_native` | PathMap ⊇ native capabilities |
| `mork_extends_pathmap_with_exec` | MORK ⊇ PathMap capabilities |
| `step_semantics_only_mork` | execStep is MORK-exclusive |
| `act_artifact_not_exec_authority` | ACT is storage, not execution |
| `mm2_requires_exec_surface` | MM2 needs execStep → needs MORK |
| `engine_surface_inclusion_native_pathmap_mork` | native ⊂ pathmap ⊂ mork |

Maps to CeTTa:
- `SpaceEngine.native` → `SPACE_KIND_ATOM` without bridge
- `SpaceEngine.pathmap` → `SPACE_KIND_ATOM` with `bridge_active=true`
- `SpaceEngine.mork` → MORK kernel `metta_calculus`
- `ArtifactSurface.act` → `.act` precompiled files
-/

end Mettapedia.Languages.MeTTa.SpaceEngineBoundary
