import Mettapedia.Languages.MeTTa.SpaceEngineBoundary

/-!
# ACT artifacts carry no execution authority

ACT (compiled atom table) files are a storage and query artifact. Three
operations use them: `open-act` creates a new space backed by the PathMap
engine with the file's atoms attached, `load-act!` adds the file's atoms to an
existing space, and `dump!` writes a space's atoms to a file.

Execution authority (`execStep`) is a capability of the engine that backs a
space. Every ACT operation needs only atom storage, which every engine has
(`act_artifact_engine_neutral`). No ACT operation moves a space to an engine
with more authority: after an ACT operation, `execStep` is available only if
the target space already had it (`act_never_grants_exec`). In particular a
space opened from an ACT file can be queried but not stepped
(`act_open_query_without_exec`), so exec facts stored in the file stay data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ACTArtifactBoundary

open SpaceEngineBoundary

/-- The three ACT artifact operations. -/
inductive ACTOperation where
  /-- Create a new PathMap-backed space with the file's atoms attached. -/
  | openAct
  /-- Add the file's atoms to an existing space. -/
  | loadAct
  /-- Write a space's atoms to a file. -/
  | dump
  deriving DecidableEq, Repr

/-- The capability each operation needs from the engine it runs on. -/
def ACTOperation.requiredCapability : ACTOperation → EngineCapability
  | .openAct => .atomStorage
  | .loadAct => .atomStorage
  | .dump => .atomStorage

/-- The engine backing the space an operation leaves, given the engine of its
target space: `open-act` creates a PathMap-backed space; `load-act!` and
`dump!` keep the target's engine. -/
def ACTOperation.resultEngine : ACTOperation → SpaceEngine → SpaceEngine
  | .openAct, _ => .pathmap
  | .loadAct, engine => engine
  | .dump, engine => engine

/-- Every ACT operation runs on every engine. -/
theorem act_artifact_engine_neutral (op : ACTOperation) (engine : SpaceEngine) :
    op.requiredCapability ∈ engine.capabilities := by
  cases op <;> cases engine <;> decide

/-- **No ACT operation grants execution authority.** -/
theorem act_never_grants_exec (op : ACTOperation) (engine : SpaceEngine)
    (granted : EngineCapability.execStep ∈ (op.resultEngine engine).capabilities) :
    EngineCapability.execStep ∈ engine.capabilities := by
  cases op with
  | openAct => exact absurd granted pathmap_query_only
  | loadAct => exact granted
  | dump => exact granted

/-- A space opened from an ACT file answers queries with candidate
acceleration but cannot be stepped, whatever space it was opened from. -/
theorem act_open_query_without_exec (engine : SpaceEngine) :
    EngineCapability.equationQuery ∈ (ACTOperation.openAct.resultEngine engine).capabilities ∧
      EngineCapability.candidateAcceleration ∈
        (ACTOperation.openAct.resultEngine engine).capabilities ∧
      EngineCapability.execStep ∉ (ACTOperation.openAct.resultEngine engine).capabilities := by
  simp only [ACTOperation.resultEngine]
  decide

namespace Controls

/-- `act_artifact_engine_neutral`: `dump!` runs on a native space ... -/
theorem dump_on_native :
    ACTOperation.dump.requiredCapability ∈ SpaceEngine.native.capabilities := by decide

/-- ... while an operation that needed `execStep` would not run on every engine. -/
theorem exec_not_on_every_engine :
    ¬ ∀ engine : SpaceEngine, EngineCapability.execStep ∈ engine.capabilities := by
  intro everywhere
  exact absurd (everywhere .native) (by decide)

/-- `act_never_grants_exec` does not remove authority: loading an ACT file
into a MORK space keeps its `execStep`. -/
theorem load_into_mork_keeps_exec :
    EngineCapability.execStep ∈ (ACTOperation.loadAct.resultEngine .mork).capabilities := by
  decide

/-- An operation that re-backed its target by the MORK engine would grant
`execStep` to a native space: the ACT operations' engine discipline is what
the law rests on. -/
theorem rebacking_by_mork_grants_exec :
    ¬ ∀ engine : SpaceEngine, EngineCapability.execStep ∈ SpaceEngine.mork.capabilities →
      EngineCapability.execStep ∈ engine.capabilities := by
  intro law
  exact absurd (law .native (by decide)) (by decide)

/-- `act_open_query_without_exec`: opening from a MORK space does not inherit
its `execStep`, although that space has it. -/
theorem open_from_mork_drops_exec :
    EngineCapability.execStep ∈ SpaceEngine.mork.capabilities ∧
      EngineCapability.execStep ∉ (ACTOperation.openAct.resultEngine .mork).capabilities := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.ACTArtifactBoundary
