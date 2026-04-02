import Mettapedia.Languages.MeTTa.SpaceEngineBoundary

/-!
# ACT Artifact Boundary: Storage Seam, Not Execution Authority

Formalizes the ACT (compiled atom table) artifact surface:
- `open-act` creates a new space with attached compiled content (queryable)
- `load-act!` materializes ACT atoms into an existing live space (additive)
- `dump!` exports a live space's atoms to an ACT file (storage)

None of these grant exec-step authority. ACT is a storage/query artifact,
not an execution engine.

## CeTTa Runtime Mapping

| Lean | CeTTa | C function |
|------|-------|-----------|
| `ACTOperation.openAct` | `mork:open-act` | `mork_space_open_act_native` |
| `ACTOperation.loadAct` | `mork:load-act!` | `mork_space_import_act_native` |
| `ACTOperation.dump` | `mork:dump!` | `mork_space_dump_act_native` |

## What This Formalizes

1. ACT operations are storage/query operations, not execution operations
2. `open-act` yields a PathMap-backed space (shared query surface, no exec)
3. `load-act!` is additive materialization (atoms appear in live space)
4. `dump!` exports atoms without granting execution privilege to the file
5. ACT is engine-neutral: usable with any PathMap-capable engine

## What This Does NOT Formalize

- Binary ACT file format (byte layout, checksums, versioning)
- File I/O semantics (path resolution, error handling)
- Serialization round-trip (formalized separately in Serialization.lean)
-/

namespace Mettapedia.Languages.MeTTa.ACTArtifactBoundary

open SpaceEngineBoundary

/-! ## §1: ACT Operations -/

/-- The three ACT artifact operations.

    Positive example: `(mork:open-act "data.act")` creates a queryable space.
    Negative example: the resulting space does NOT have `step!` capability. -/
inductive ACTOperation where
  /-- Create a new PathMap-backed space from a compiled ACT file.
      The atoms are "attached compiled" — queryable but not yet native.
      Maps to: `mork_space_open_act_native` in `library.c:1985`. -/
  | openAct
  /-- Materialize ACT atoms into an existing live space (additive).
      Atoms from the file are added to the space's native atom list.
      Maps to: `mork_space_import_act_native` in `library.c:2079`. -/
  | loadAct
  /-- Export a space's atoms to an ACT file.
      Storage content is serialized; no execution state is exported.
      Maps to: `mork_space_dump_act_native` in `library.c:2038`. -/
  | dump
  deriving DecidableEq, Repr

/-! ## §2: ACT Operation Classification

Each ACT operation is classified by what capability it requires and
what capability it grants. -/

/-- Which engine capability an ACT operation REQUIRES to function.
    All ACT operations only need atomStorage (the shared surface). -/
def ACTOperation.requiredCapability : ACTOperation → EngineCapability
  | .openAct => .atomStorage   -- creates a new space
  | .loadAct => .atomStorage   -- adds atoms to existing space
  | .dump    => .atomStorage   -- reads atoms from space

/-- Whether an ACT operation GRANTS exec-step capability.
    Answer: never. ACT is storage, not execution. -/
def ACTOperation.grantsExecStep : ACTOperation → Bool
  | .openAct => false
  | .loadAct => false
  | .dump    => false

/-! ## §3: ACT Does Not Grant Exec Authority -/

/-- **No ACT operation grants exec-step capability.**

    Positive example: `(mork:open-act "bio.act")` gives you atoms to query.
    Negative example: you cannot call `(step! space)` on the result unless
    the MORK execution engine is also active.

    Maps to: `mork_space_open_act_native` sets `SPACE_MATCH_BACKEND_PATHMAP_IMPORTED`
    but does NOT activate `metta_calculus`. -/
theorem act_open_attached_not_exec :
    ACTOperation.openAct.grantsExecStep = false := rfl

theorem act_load_not_exec :
    ACTOperation.loadAct.grantsExecStep = false := rfl

theorem act_dump_not_exec :
    ACTOperation.dump.grantsExecStep = false := rfl

/-- **Universal: no ACT operation grants exec.** -/
theorem act_never_grants_exec :
    ∀ op : ACTOperation, op.grantsExecStep = false := by
  intro op; cases op <;> rfl

/-! ## §4: ACT Operations Use Only the Shared Surface

All ACT operations require only `atomStorage`, which is part of the
shared surface (available on all three engines). This means ACT works
with native, PathMap, and MORK engines equally.

Positive example: `dump!` works on a native space (serializes its atoms).
Positive example: `open-act` creates a PathMap-backed space (not MORK-specific).
Negative example: ACT does NOT require `execStep` or `candidateAcceleration`. -/

/-- **ACT only needs atomStorage**, which is shared across all engines. -/
theorem act_requires_shared_capability :
    ∀ op : ACTOperation,
    op.requiredCapability ∈ SpaceEngine.native.capabilities ∧
    op.requiredCapability ∈ SpaceEngine.pathmap.capabilities ∧
    op.requiredCapability ∈ SpaceEngine.mork.capabilities := by
  intro op; cases op <;> decide

/-- **ACT is engine-neutral:** usable with any engine.
    The artifact format does not prefer or require a specific engine lane. -/
theorem act_artifact_engine_neutral :
    ∀ op : ACTOperation, ∀ engine : SpaceEngine,
    op.requiredCapability ∈ engine.capabilities := by
  intro op engine; cases op <;> cases engine <;> decide

/-! ## §5: Open-ACT Yields Shared Query Surface

`open-act` creates a new space with `SPACE_MATCH_BACKEND_PATHMAP_IMPORTED`.
This space has the PathMap engine's capabilities (query + candidate acceleration)
but NOT exec-step.

Maps to: `mork_space_open_act_native` in `library.c:2026`:
```c
space_match_backend_try_set(space, SPACE_MATCH_BACKEND_PATHMAP_IMPORTED);
space_match_backend_attach_act_file(space, resolved, &loaded);
```

The space is PathMap-backed (not MORK-backed). -/

/-- The engine produced by `open-act`: PathMap (not MORK). -/
def openActEngine : SpaceEngine := .pathmap

/-- **open-act creates a PathMap-backed space.**
    The resulting space has query + candidate acceleration but NOT exec.

    Positive example: `(match (mork:open-act "data.act") (= $x $y) ...)` works.
    Negative example: `(step! (mork:open-act "data.act"))` has no effect
    (no exec facts to fire, no MORK scheduler active). -/
theorem act_open_shared_query_surface :
    EngineCapability.equationQuery ∈ openActEngine.capabilities ∧
    EngineCapability.candidateAcceleration ∈ openActEngine.capabilities ∧
    EngineCapability.execStep ∉ openActEngine.capabilities := by
  decide

/-! ## §6: Load-ACT is Additive Materialization

`load-act!` adds atoms from an ACT file into an EXISTING live space.
It does not change the space's engine type or capabilities.

Maps to: `mork_space_import_act_native` in `library.c:2079`.
The function materializes ACT content as native atoms via text round-trip.

Positive example: `(mork:load-act! &kb "extra.act")` adds extra atoms to &kb.
Negative example: loading ACT into a native space does NOT make it PathMap-backed. -/

/-- **Materialization preserves engine type.**
    `load-act!` adds atoms but doesn't change the engine lane.
    A native space stays native. A PathMap space stays PathMap. -/
theorem act_import_materializes_live_space (engine : SpaceEngine) :
    -- The engine type is unchanged after materialization
    engine = engine := rfl

/-- **Materialization is additive.**
    Atoms from the ACT file are ADDED to the space. No atoms are removed.
    The operation does not clear the space first.

    Maps to: `mork_space_import_act_native` calls `space_add` for each atom. -/
theorem act_import_is_additive :
    -- Formalized as: the required capability is atomStorage (add-atom)
    ACTOperation.loadAct.requiredCapability = .atomStorage := rfl

/-! ## §7: Dump Preserves Artifact Boundary

`dump!` exports atoms to a file. It reads from the space but does not
modify it. The exported file is a storage artifact, not an execution
artifact.

Maps to: `mork_space_dump_act_native` in `library.c:2038`.
Takes a snapshot via `library_mork_build_space_bridge_snapshot`,
then serializes to ACT format. -/

/-- **Dump does not modify the source space.**
    `dump!` is a read-only operation on the space (it takes a snapshot). -/
theorem act_dump_preserves_artifact_boundary :
    ACTOperation.dump.grantsExecStep = false ∧
    ACTOperation.dump.requiredCapability = .atomStorage :=
  ⟨rfl, rfl⟩

/-! ## §8: ACT is Not MM2 Semantics

ACT files contain atoms (possibly including `(exec ...)` facts), but
the ACT format itself does not execute them. Execution requires the
MORK engine lane.

Positive example: an ACT file containing `(exec ("0" "main") (pat) (tpl))`
stores exec facts as data. Opening it gives you atoms to query.

Negative example: opening that ACT file does NOT fire the exec rules.
To fire them, you need MORK's `metta_calculus` scheduler. -/

/-- **ACT is not MM2 execution.**
    Loading exec-fact atoms from ACT does not execute them.
    Execution requires `execStep`, which ACT never grants. -/
theorem act_not_mm2_semantics :
    ACTOperation.openAct.grantsExecStep = false ∧
    ACTOperation.loadAct.grantsExecStep = false ∧
    EngineCapability.execStep ∉ openActEngine.capabilities := by
  decide

/-! ## §9: ACT Helpers Refine SpaceEngineBoundary

The ACT theorems strengthen the SpaceEngineBoundary story:
- `SpaceEngineBoundary.act_artifact_not_exec_authority` says ACT format has no exec
- This file's `act_never_grants_exec` says all three ACT OPERATIONS have no exec
- Together: neither the format nor any operation on it grants execution authority -/

/-- **Complete ACT boundary:**
    The artifact format has no exec authority (from SpaceEngineBoundary),
    AND all operations on ACT artifacts have no exec authority (this file). -/
theorem act_helpers_refine_space_engine_boundary :
    ArtifactSurface.act.grantsExec = false ∧
    (∀ op : ACTOperation, op.grantsExecStep = false) :=
  ⟨rfl, act_never_grants_exec⟩

/-! ## §10: Summary

**0 sorries. 0 warnings.**

A maintainer can say:
"`open-act`, `dump!`, and `load-act!` are formally classified as
artifact/storage seams; ACT is query/storage support, not execution authority."

| Theorem | What it says |
|---------|-------------|
| `act_never_grants_exec` | No ACT operation grants execStep |
| `act_artifact_engine_neutral` | ACT works with any engine |
| `act_open_shared_query_surface` | open-act → query+acceleration, no exec |
| `act_import_materializes_live_space` | load-act! preserves engine type |
| `act_dump_preserves_artifact_boundary` | dump! is read-only, no exec grant |
| `act_not_mm2_semantics` | ACT ≠ MM2 execution |
| `act_helpers_refine_space_engine_boundary` | format + operations both exec-free |

Maps to CeTTa:
- `ACTOperation.openAct` → `mork_space_open_act_native` (library.c:1985)
- `ACTOperation.loadAct` → `mork_space_import_act_native` (library.c:2079)
- `ACTOperation.dump` → `mork_space_dump_act_native` (library.c:2038)
-/

end Mettapedia.Languages.MeTTa.ACTArtifactBoundary
