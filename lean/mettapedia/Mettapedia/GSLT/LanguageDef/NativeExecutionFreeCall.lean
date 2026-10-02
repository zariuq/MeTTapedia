import Mettapedia.GSLT.LanguageDef.NativeExecutionNodeRelease
import Mettapedia.GSLT.LanguageDef.NativeExecutionFreeObservation

/-!
The execution-free interface removes an owned node before destroying the
observation and then the node allocation. Null arguments return before any
scope lookup. Foreign handles return before any observation-memory read.
Nonnull missing scope storage, invalid payload pointers and repeated system
frees have no defined transition. Both relations retain the complete context
and allocator post-state; they do not grant any logical authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionFreeCall

open NativeOps (Address SourceMemory TargetMemory SourceState TargetState StateRelated MemoryRelated)
open NativeExecutionNodeRelease (World Node)

def sourceUpdated (state : SourceState World) (memory : SourceMemory)
    (scope : Address) (nodes : List Node) : SourceState World :=
  { state with
    memory := memory
    external := ⟨NativeExecutionNodeRelease.sourceCells state.external.scopes scope nodes⟩ }

def targetUpdated (state : TargetState World) (memory : TargetMemory)
    (scope : Address) (nodes : List Node) : TargetState World :=
  { state with
    memory := memory
    external := ⟨NativeExecutionNodeRelease.targetCells state.external.scopes scope nodes⟩ }

theorem update_correspondence (source : SourceState World) (target : TargetState World)
    (related : StateRelated Eq source target) (sourceMemory : SourceMemory)
    (targetMemory : TargetMemory) (memories : MemoryRelated sourceMemory targetMemory)
    (scope : Address) (nodes : List Node) :
    StateRelated Eq (sourceUpdated source sourceMemory scope nodes)
      (targetUpdated target targetMemory scope nodes) := by
  refine ⟨memories, related.fault, related.allocator, related.release, ?_, related.allocatorStats⟩
  change World.mk (NativeExecutionNodeRelease.sourceCells source.external.scopes scope nodes) =
    World.mk (NativeExecutionNodeRelease.targetCells target.external.scopes scope nodes)
  rw [← related.external, NativeExecutionNodeRelease.store_correspondence]

inductive SourceCall : SourceState World → Option Address → Option Address →
    SourceState World → Prop where
  | nullScope (state : SourceState World) (handle : Option Address) :
    SourceCall state none handle state
  | nullObservation (state : SourceState World) (scope : Address) :
    SourceCall state (some scope) none state
  | foreign {state : SourceState World} {scope handle : Address} {nodes : List Node}
      (found : NativeExecutionNodeRelease.sourceFind state.external.scopes scope = some nodes)
      (absent : NativeExecutionNodeRelease.sourceExtract nodes handle = none) :
    SourceCall state (some scope) (some handle) state
  | owned {state : SourceState World} {scope handle : Address} {nodes rest : List Node}
      {selected : Node} {intermediate post : SourceMemory}
      (found : NativeExecutionNodeRelease.sourceFind state.external.scopes scope = some nodes)
      (selectedNode : NativeExecutionNodeRelease.sourceExtract nodes handle = some (selected, rest))
      (observationFreed : NativeExecutionFreeObservation.sourceFree state.memory (some handle) =
        some intermediate)
      (nodeFreed : NativeExecutionFreeStorage.sourceFree intermediate (some selected.address) =
        some post) :
    SourceCall state (some scope) (some handle) (sourceUpdated state post scope rest)

inductive TargetCall : TargetState World → Option Address → Option Address →
    TargetState World → Prop where
  | nullScope (state : TargetState World) (handle : Option Address) :
    TargetCall state none handle state
  | nullObservation (state : TargetState World) (scope : Address) :
    TargetCall state (some scope) none state
  | foreign {state : TargetState World} {scope handle : Address} {nodes : List Node}
      (found : NativeExecutionNodeRelease.targetFind state.external.scopes scope = some nodes)
      (absent : NativeExecutionNodeRelease.targetExtract nodes handle = none) :
    TargetCall state (some scope) (some handle) state
  | owned {state : TargetState World} {scope handle : Address} {nodes rest : List Node}
      {selected : Node} {intermediate post : TargetMemory}
      (found : NativeExecutionNodeRelease.targetFind state.external.scopes scope = some nodes)
      (selectedNode : NativeExecutionNodeRelease.targetExtract nodes handle = some (selected, rest))
      (observationFreed : NativeExecutionFreeObservation.targetFree state.memory (some handle) =
        some intermediate)
      (nodeFreed : NativeExecutionFreeStorage.targetFree intermediate (some selected.address) =
        some post) :
    TargetCall state (some scope) (some handle) (targetUpdated state post scope rest)

theorem call_forward (source : SourceState World) (target : TargetState World)
    (related : StateRelated Eq source target) (scope handle : Option Address)
    (post : SourceState World) (called : SourceCall source scope handle post) :
    ∃ native, TargetCall target scope handle native ∧ StateRelated Eq post native := by
  cases called with
  | nullScope => exact ⟨target, .nullScope target _, related⟩
  | nullObservation => exact ⟨target, .nullObservation target _, related⟩
  | @foreign _ _ nodes found absent =>
    refine ⟨target, .foreign (nodes := nodes) ?_ ?_, related⟩
    · rw [← related.external, NativeExecutionNodeRelease.find_correspondence]
      exact found
    · rw [NativeExecutionNodeRelease.extraction_correspondence]
      exact absent
  | @owned scopeAddress requested nodes rest selected intermediate sourcePost
      found extracted observationFreed nodeFreed =>
    obtain ⟨nativeIntermediate, nativeObservation, intermediateRelated⟩ :=
      NativeExecutionFreeObservation.observation_free_forward source.memory target.memory
        related.memory (some requested) intermediate observationFreed
    obtain ⟨nativePost, nativeNode, memories⟩ := NativeExecutionFreeStorage.free_forward
      intermediate nativeIntermediate intermediateRelated (some selected.address) sourcePost nodeFreed
    refine ⟨targetUpdated target nativePost scopeAddress rest,
      .owned (nodes := nodes) ?_ ?_ nativeObservation nativeNode,
      update_correspondence source target related sourcePost nativePost memories scopeAddress rest⟩
    · rw [← related.external, NativeExecutionNodeRelease.find_correspondence]
      exact found
    · rw [NativeExecutionNodeRelease.extraction_correspondence]
      exact extracted

theorem call_backward (source : SourceState World) (target : TargetState World)
    (related : StateRelated Eq source target) (scope handle : Option Address)
    (native : TargetState World) (called : TargetCall target scope handle native) :
    ∃ post, SourceCall source scope handle post ∧ StateRelated Eq post native := by
  cases called with
  | nullScope => exact ⟨source, .nullScope source _, related⟩
  | nullObservation => exact ⟨source, .nullObservation source _, related⟩
  | @foreign _ _ nodes found absent =>
    refine ⟨source, .foreign (nodes := nodes) ?_ ?_, related⟩
    · rw [← NativeExecutionNodeRelease.find_correspondence, related.external]
      exact found
    · rw [← NativeExecutionNodeRelease.extraction_correspondence]
      exact absent
  | @owned scopeAddress requested nodes rest selected intermediate nativePost
      found extracted observationFreed nodeFreed =>
    obtain ⟨sourceIntermediate, sourceObservation, intermediateRelated⟩ :=
      NativeExecutionFreeObservation.observation_free_backward source.memory target.memory
        related.memory (some requested) intermediate observationFreed
    obtain ⟨sourcePost, sourceNode, memories⟩ := NativeExecutionFreeStorage.free_backward
      sourceIntermediate intermediate intermediateRelated (some selected.address) nativePost nodeFreed
    refine ⟨sourceUpdated source sourcePost scopeAddress rest,
      .owned (nodes := nodes) ?_ ?_ sourceObservation sourceNode,
      update_correspondence source target related sourcePost nativePost memories scopeAddress rest⟩
    · rw [← NativeExecutionNodeRelease.find_correspondence, related.external]
      exact found
    · rw [← NativeExecutionNodeRelease.extraction_correspondence]
      exact extracted

end Mettapedia.GSLT.LanguageDef.NativeExecutionFreeCall
