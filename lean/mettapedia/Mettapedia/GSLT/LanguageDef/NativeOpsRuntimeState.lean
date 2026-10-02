import Mettapedia.GSLT.LanguageDef.NativeOpsPrimitives
import Mettapedia.GSLT.LanguageDef.NativeOpsAllocatorState

/-!
# Stateful native observations and sticky context faults

The external state is separate from the operational context fault.  A reader
may poison its own view while leaving that context clear.  Operations receive
and return their exact post-state; a later fault never rolls back earlier
storage or external effects.  Default C return values after a context fault
are observed as faults, rather than admitted source values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Fault)

structure SourceState (ExternalState : Type) where
  memory : SourceMemory
  fault : Option Fault
  allocatorAvailable : Bool
  releaseAvailable : Bool
  external : ExternalState
  allocatorStats : SourceAllocatorStats

structure TargetState (ExternalState : Type) where
  memory : TargetMemory
  fault : Option Fault
  allocatorAvailable : Bool
  releaseAvailable : Bool
  external : ExternalState
  allocatorStats : TargetAllocatorStats

structure StateRelated {SourceExternal TargetExternal : Type}
    (externalRelated : SourceExternal → TargetExternal → Prop)
    (source : SourceState SourceExternal) (target : TargetState TargetExternal) : Prop where
  memory : MemoryRelated source.memory target.memory
  fault : target.fault = source.fault
  allocator : target.allocatorAvailable = source.allocatorAvailable
  release : target.releaseAvailable = source.releaseAvailable
  external : externalRelated source.external target.external
  allocatorStats : AllocatorStatsRelated source.allocatorStats target.allocatorStats

def sourcePoison {ExternalState : Type} (state : SourceState ExternalState) (fault : Fault) :
    SourceState ExternalState :=
  match state.fault with
  | none => { state with fault := some fault }
  | some _ => state

def targetPoison {ExternalState : Type} (state : TargetState ExternalState) (fault : Fault) :
    TargetState ExternalState :=
  if state.fault.isNone then { state with fault := some fault } else state

theorem poison_correspondence {SourceExternal TargetExternal : Type}
    {externalRelated : SourceExternal → TargetExternal → Prop}
    {source : SourceState SourceExternal} {target : TargetState TargetExternal}
    (related : StateRelated externalRelated source target) (fault : Fault) :
    StateRelated externalRelated (sourcePoison source fault) (targetPoison target fault) := by
  cases prior : source.fault with
  | none =>
      simp only [sourcePoison, prior, targetPoison, related.fault, Option.isNone_none,
        if_true]
      exact ⟨related.memory, rfl, related.allocator, related.release, related.external,
        related.allocatorStats⟩
  | some previous =>
      simp only [sourcePoison, prior, targetPoison, related.fault, Option.isNone_some,
        Bool.false_eq_true, if_false]
      exact related

theorem source_first_fault {ExternalState : Type} (state : SourceState ExternalState)
    (previous next : Fault) (prior : state.fault = some previous) :
    sourcePoison state next = state := by simp [sourcePoison, prior]

theorem target_first_fault {ExternalState : Type} (state : TargetState ExternalState)
    (previous next : Fault) (prior : state.fault = some previous) :
    targetPoison state next = state := by simp [targetPoison, prior]

theorem source_poison_preserves_effects {ExternalState : Type}
    (state : SourceState ExternalState) (fault : Fault) :
    (sourcePoison state fault).memory = state.memory ∧
      (sourcePoison state fault).external = state.external := by
  cases prior : state.fault <;>
    simp [sourcePoison, prior]

theorem target_poison_preserves_effects {ExternalState : Type}
    (state : TargetState ExternalState) (fault : Fault) :
    (targetPoison state fault).memory = state.memory ∧
      (targetPoison state fault).external = state.external := by
  unfold targetPoison
  split <;> exact ⟨rfl, rfl⟩

theorem source_poison_preserves_allocator_stats {ExternalState : Type}
    (state : SourceState ExternalState) (fault : Fault) :
    (sourcePoison state fault).allocatorStats = state.allocatorStats := by
  cases prior : state.fault <;> simp [sourcePoison, prior]

theorem target_poison_preserves_allocator_stats {ExternalState : Type}
    (state : TargetState ExternalState) (fault : Fault) :
    (targetPoison state fault).allocatorStats = state.allocatorStats := by
  unfold targetPoison
  split <;> rfl

structure SourceOutcome (ExternalState : Type) where
  result : Except Fault SourceValue
  state : SourceState ExternalState

structure TargetOutcome (ExternalState : Type) where
  result : Except Fault TargetValue
  state : TargetState ExternalState

structure OutcomeRelated {SourceExternal TargetExternal : Type}
    (externalRelated : SourceExternal → TargetExternal → Prop)
    (source : SourceOutcome SourceExternal) (target : TargetOutcome TargetExternal) : Prop where
  state : StateRelated externalRelated source.state target.state
  result : target.result = source.result.map encodeValue

def sourceObserve {ExternalState : Type} (state : SourceState ExternalState)
    (raw : SourceValue) : SourceOutcome ExternalState :=
  match state.fault with
  | none => ⟨.ok raw, state⟩
  | some fault => ⟨.error fault, state⟩

def targetObserve {ExternalState : Type} (state : TargetState ExternalState)
    (raw : TargetValue) : TargetOutcome ExternalState :=
  if state.fault.isNone then ⟨.ok raw, state⟩
  else match state.fault with
    | some fault => ⟨.error fault, state⟩
    | none => ⟨.ok raw, state⟩

theorem sourceObserve_state {ExternalState : Type} (state : SourceState ExternalState)
    (raw : SourceValue) : (sourceObserve state raw).state = state := by
  cases prior : state.fault <;> simp [sourceObserve, prior]

theorem targetObserve_state {ExternalState : Type} (state : TargetState ExternalState)
    (raw : TargetValue) : (targetObserve state raw).state = state := by
  cases prior : state.fault <;> simp [targetObserve, prior]

theorem observation_correspondence {SourceExternal TargetExternal : Type}
    {externalRelated : SourceExternal → TargetExternal → Prop}
    {source : SourceState SourceExternal} {target : TargetState TargetExternal}
    (related : StateRelated externalRelated source target) (raw : SourceValue) :
    OutcomeRelated externalRelated (sourceObserve source raw)
      (targetObserve target (encodeValue raw)) := by
  cases prior : source.fault with
  | none =>
      simp only [sourceObserve, prior, targetObserve, related.fault, Option.isNone_none,
        if_true]
      exact ⟨related, rfl⟩
  | some fault =>
      simp only [sourceObserve, prior, targetObserve, related.fault, Option.isNone_some,
        Bool.false_eq_true, if_false]
      exact ⟨related, rfl⟩

theorem target_default_after_fault {ExternalState : Type}
    (state : TargetState ExternalState) (fault : Fault) (raw : TargetValue)
    (failed : state.fault = some fault) :
    (targetObserve state raw).result = .error fault := by
  simp [targetObserve, failed]

theorem target_normal_result_iff {ExternalState : Type}
    (state : TargetState ExternalState) (raw result : TargetValue) :
    (targetObserve state raw).result = .ok result ↔ state.fault = none ∧ raw = result := by
  cases prior : state.fault <;> simp [targetObserve, prior]

theorem related_normal_result_iff {SourceExternal TargetExternal : Type}
    {externalRelated : SourceExternal → TargetExternal → Prop}
    {source : SourceOutcome SourceExternal} {target : TargetOutcome TargetExternal}
    (related : OutcomeRelated externalRelated source target) (result : SourceValue) :
    target.result = .ok (encodeValue result) ↔ source.result = .ok result := by
  rw [related.result]
  cases source.result <;> simp [Except.map, encodeValue_injective.eq_iff]

theorem related_fault_result_iff {SourceExternal TargetExternal : Type}
    {externalRelated : SourceExternal → TargetExternal → Prop}
    {source : SourceOutcome SourceExternal} {target : TargetOutcome TargetExternal}
    (related : OutcomeRelated externalRelated source target) (fault : Fault) :
    target.result = .error fault ↔ source.result = .error fault := by
  rw [related.result]
  cases source.result <;> simp [Except.map]

/-- A primitive has already executed before this operation checks its context. -/
def sourceFinish {ExternalState : Type} (postState : SourceState ExternalState)
    (operation : Except Fault SourceValue) : SourceOutcome ExternalState :=
  match operation with
  | .ok value => sourceObserve postState value
  | .error fault => sourceObserve (sourcePoison postState fault) .unit

/-- The emitted C keeps its type-correct default return on the private fault path. -/
def targetFinish {ExternalState : Type} (postState : TargetState ExternalState)
    (operation : Except Fault TargetValue) (default : TargetValue) : TargetOutcome ExternalState :=
  match operation with
  | .ok value => targetObserve postState value
  | .error fault => targetObserve (targetPoison postState fault) default

theorem finish_correspondence {SourceExternal TargetExternal : Type}
    {externalRelated : SourceExternal → TargetExternal → Prop}
    {source : SourceState SourceExternal} {target : TargetState TargetExternal}
    (related : StateRelated externalRelated source target)
    (operation : Except Fault SourceValue) (default : TargetValue) :
    OutcomeRelated externalRelated (sourceFinish source operation)
      (targetFinish target (operation.map encodeValue) default) := by
  cases operation with
  | ok value => exact observation_correspondence related value
  | error fault =>
      have poisoned := poison_correspondence related fault
      have failed : ∃ previous, (sourcePoison source fault).fault = some previous := by
        cases prior : source.fault with
        | none => exact ⟨fault, by simp [sourcePoison, prior]⟩
        | some previous => exact ⟨previous, by simp [sourcePoison, prior]⟩
      obtain ⟨previous, failed⟩ := failed
      change OutcomeRelated externalRelated
        (sourceObserve (sourcePoison source fault) .unit)
        (targetObserve (targetPoison target fault) default)
      constructor
      · simpa only [sourceObserve_state, targetObserve_state] using poisoned
      · rw [target_default_after_fault _ previous default (poisoned.fault.trans failed)]
        simp only [sourceObserve, failed, Except.map]

end Mettapedia.GSLT.LanguageDef.NativeOps
