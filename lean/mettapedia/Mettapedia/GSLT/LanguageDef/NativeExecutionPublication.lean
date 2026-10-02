import Mettapedia.GSLT.LanguageDef.NativeExecutionScope
import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryEffects

/-!
The observation-pointer publication suffix of the native execution interface.
The physical call supplies its status, completed handle and observation. A
nonzero status leaves the scope and caller's slot unchanged. Success prepends
the completed node and stores its handle through the caller's slot. Source
and target stores are independent, and the proof retains their exact memory
effects. Null scope/output checks precede the physical call. Actual physical
execution and concrete pointer realization are explicit separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionPublication

open NativeOps (Address SourceValue TargetValue SourceMemory TargetMemory MemoryRelated
  sourceWrite targetWrite sourceRead targetRead encodeValue)
open NativeExecutionScope (Scope Observation Contract)
open NativeWord64 (Word encode)

def sourcePrecheck (scope caller : Option Address) : Option Word :=
  if scope.isNone || caller.isNone then some 1 else none

def targetPrecheck (scope caller : Option Address) : Option (BitVec 64) :=
  match scope with
  | none => some 1
  | some _ => match caller with
    | none => some 1
    | some _ => none

theorem precheck_correspondence (scope caller : Option Address) :
    targetPrecheck scope caller = (sourcePrecheck scope caller).map encode := by
  cases scope <;> cases caller <;> rfl

structure SourcePublished where
  memory : SourceMemory
  scope : Scope
  status : Word

structure TargetPublished where
  memory : TargetMemory
  scope : Scope
  status : BitVec 64

def PublishedRelated (source : SourcePublished) (target : TargetPublished) : Prop :=
  MemoryRelated source.memory target.memory ∧
    target.scope = source.scope ∧ target.status = encode source.status

def sourcePublish (memory : SourceMemory) (scope : Scope) (caller : Address)
    (status : Word) (handle : Address) (observation : Observation) : Option SourcePublished :=
  if status.val = 0 then do
    let post ← sourceWrite memory caller (.reference (some handle))
    some ⟨post, NativeExecutionScope.complete scope handle observation, status⟩
  else some ⟨memory, scope, status⟩

def targetPublish (memory : TargetMemory) (scope : Scope) (caller : Address)
    (status : BitVec 64) (handle : Address) (observation : Observation) : Option TargetPublished :=
  if status = 0 then
    let next := NativeExecutionScope.Entry.mk handle observation :: scope
    match targetWrite memory caller (.reference (some handle)) with
    | none => none
    | some post => some ⟨post, next, status⟩
  else some ⟨memory, scope, status⟩

theorem source_failure_no_publication (memory : SourceMemory) (scope : Scope)
    (caller : Address) (status : Word) (failed : status.val ≠ 0)
    (handle : Address) (observation : Observation) :
    sourcePublish memory scope caller status handle observation = some ⟨memory, scope, status⟩ := by
  simp only [sourcePublish, if_neg failed]

theorem target_failure_no_publication (memory : TargetMemory) (scope : Scope)
    (caller : Address) (status : BitVec 64) (failed : status ≠ 0)
    (handle : Address) (observation : Observation) :
    targetPublish memory scope caller status handle observation = some ⟨memory, scope, status⟩ := by
  simp only [targetPublish, if_neg failed]

theorem publication_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (scope : Scope) (caller : Address)
    (status : Word) (handle : Address) (observation : Observation) (post : SourcePublished)
    (published : sourcePublish source scope caller status handle observation = some post) :
    ∃ native, targetPublish target scope caller (encode status) handle observation = some native ∧
      PublishedRelated post native := by
  by_cases succeeded : status.val = 0
  · have targetSucceeded : encode status = 0 := (NativeWord64.encode_eq_zero status).mpr succeeded
    simp only [sourcePublish, if_pos succeeded] at published
    cases wrote : sourceWrite source caller (.reference (some handle)) with
    | none =>
      simp only [wrote, bind, Option.bind_none] at published
      cases published
    | some changed =>
      have same : SourcePublished.mk changed (NativeExecutionScope.complete scope handle observation)
          status = post := by
        apply Option.some.inj
        simpa only [wrote, bind, Option.bind_some] using published
      obtain ⟨native, nativeWrote, memories⟩ := NativeOps.memory_write_forward source target
        related caller (.reference (some handle)) changed wrote
      change targetWrite target caller (.reference (some handle)) = some native at nativeWrote
      refine ⟨⟨native, NativeExecutionScope.complete scope handle observation, encode status⟩, ?_, ?_⟩
      · simp only [targetPublish, if_pos targetSucceeded, nativeWrote]
        rfl
      · rw [← same]
        exact ⟨memories, rfl, rfl⟩
  · have targetFailed : encode status ≠ 0 := fun equal =>
      succeeded ((NativeWord64.encode_eq_zero status).mp equal)
    have same : SourcePublished.mk source scope status = post := by
      apply Option.some.inj
      simpa only [sourcePublish, if_neg succeeded] using published
    refine ⟨⟨target, scope, encode status⟩, target_failure_no_publication _ _ _ _ targetFailed _ _, ?_⟩
    rw [← same]
    exact ⟨related, rfl, rfl⟩

theorem publication_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (scope : Scope) (caller : Address)
    (status : Word) (handle : Address) (observation : Observation) (native : TargetPublished)
    (published : targetPublish target scope caller (encode status) handle observation = some native) :
    ∃ post, sourcePublish source scope caller status handle observation = some post ∧
      PublishedRelated post native := by
  by_cases succeeded : status.val = 0
  · have targetSucceeded : encode status = 0 := (NativeWord64.encode_eq_zero status).mpr succeeded
    simp only [targetPublish, if_pos targetSucceeded] at published
    cases wrote : targetWrite target caller (.reference (some handle)) with
    | none => simp only [wrote] at published; cases published
    | some changed =>
      have same : TargetPublished.mk changed (NativeExecutionScope.complete scope handle observation)
          (encode status) = native := by
        apply Option.some.inj
        simpa only [wrote, NativeExecutionScope.complete] using published
      obtain ⟨post, sourceWrote, memories⟩ := NativeOps.memory_write_backward source target
        related caller (.reference (some handle)) changed wrote
      refine ⟨⟨post, NativeExecutionScope.complete scope handle observation, status⟩, ?_, ?_⟩
      · simp only [sourcePublish, if_pos succeeded, sourceWrote, bind, Option.bind_some]
      · rw [← same]
        exact ⟨memories, rfl, rfl⟩
  · have targetFailed : encode status ≠ 0 := fun equal =>
      succeeded ((NativeWord64.encode_eq_zero status).mp equal)
    have same : TargetPublished.mk target scope (encode status) = native := by
      apply Option.some.inj
      simpa only [targetPublish, if_neg targetFailed] using published
    refine ⟨⟨source, scope, status⟩, source_failure_no_publication _ _ _ _ succeeded _ _, ?_⟩
    rw [← same]
    exact ⟨related, rfl, rfl⟩

theorem source_success_publishes_caller_alias (memory : SourceMemory) (scope : Scope)
    (caller handle : Address) (observation : Observation) (post : SourcePublished)
    (published : sourcePublish memory scope caller 0 handle observation = some post) :
    sourceRead post.memory caller = some (.reference (some handle)) ∧
      post.scope = NativeExecutionScope.complete scope handle observation := by
  rw [sourcePublish, if_pos (show (0 : Word).val = 0 from rfl)] at published
  cases wrote : sourceWrite memory caller (.reference (some handle)) with
  | none => simp only [wrote, bind, Option.bind_none] at published; cases published
  | some changed =>
    have same : SourcePublished.mk changed (NativeExecutionScope.complete scope handle observation)
        0 = post := by
      apply Option.some.inj
      simpa only [wrote, bind, Option.bind_some] using published
    rw [← same]
    exact ⟨NativeOps.source_read_after_write _ _ _ _ wrote, rfl⟩

theorem target_success_publishes_caller_alias (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (scope : Scope) (caller handle : Address)
    (observation : Observation) (post : TargetPublished)
    (published : targetPublish target scope caller 0 handle observation = some post) :
    targetRead post.memory caller = some (.reference (some handle)) ∧
      NativeExecutionScope.targetRead post.scope (some handle) = some observation := by
  obtain ⟨sourcePost, sourcePublished, postRelated⟩ :=
    publication_backward source target related scope caller 0 handle observation post published
  obtain ⟨readBack, scopeEqual⟩ := source_success_publishes_caller_alias _ _ _ _ _ _ sourcePublished
  constructor
  · rw [NativeOps.memory_read_correspondence sourcePost.memory post.memory postRelated.1, readBack]
    rfl
  · rw [postRelated.2.1, scopeEqual]
    simp only [NativeExecutionScope.complete, NativeExecutionScope.targetRead,
      NativeExecutionScope.targetFind, if_true]

theorem source_success_preserves_reached (contract : Contract) (scope : Scope)
    (reached : NativeExecutionScope.Reached contract scope) (memory : SourceMemory)
    (caller handle : Address) (observation : Observation)
    (fresh : handle ∉ scope.map NativeExecutionScope.Entry.handle)
    (physical : observation.realized contract) (post : SourcePublished)
    (published : sourcePublish memory scope caller 0 handle observation = some post) :
    NativeExecutionScope.Reached contract post.scope := by
  rw [(source_success_publishes_caller_alias _ _ _ _ _ _ published).2]
  exact .completed reached fresh physical

theorem target_success_preserves_reached (contract : Contract) (scope : Scope)
    (reached : NativeExecutionScope.Reached contract scope)
    (source : SourceMemory) (target : TargetMemory) (related : MemoryRelated source target)
    (caller handle : Address) (observation : Observation)
    (fresh : handle ∉ scope.map NativeExecutionScope.Entry.handle)
    (physical : observation.realized contract) (post : TargetPublished)
    (published : targetPublish target scope caller 0 handle observation = some post) :
    NativeExecutionScope.Reached contract post.scope := by
  obtain ⟨sourcePost, sourcePublished, postRelated⟩ :=
    publication_backward source target related scope caller 0 handle observation post published
  rw [postRelated.2.1]
  exact source_success_preserves_reached contract scope reached source caller handle observation
    fresh physical sourcePost sourcePublished

private def caller : Address := ⟨1, 0, []⟩
private def oldHandle : Address := ⟨2, 0, []⟩
private def completedHandle : Address := ⟨3, 0, []⟩
private def emptyObservation : Observation := ⟨⟨⟨[], [], []⟩, 0⟩, []⟩
private def callerMemory : SourceMemory :=
  ⟨fun storage element => if storage = 1 ∧ element = 0 then
      some (.reference (some oldHandle)) else none, fun _ => none⟩

theorem null_scope_refused_before_call : sourcePrecheck none (some caller) = some 1 := rfl

theorem null_output_slot_refused_before_call :
    targetPrecheck (some caller) none = some 1 := rfl

theorem completed_call_replaces_previous_slot :
    (sourcePublish callerMemory [] caller 0 completedHandle emptyObservation).bind
      (fun post => sourceRead post.memory caller) = some (.reference (some completedHandle)) := rfl

theorem resource_failure_retains_previous_slot :
    (sourcePublish callerMemory [] caller 2 completedHandle emptyObservation).bind
      (fun post => sourceRead post.memory caller) = some (.reference (some oldHandle)) := rfl

theorem physical_failure_retains_previous_scope :
    (sourcePublish callerMemory [⟨oldHandle, emptyObservation⟩] caller 3 completedHandle
      emptyObservation).map SourcePublished.scope = some [⟨oldHandle, emptyObservation⟩] := rfl

theorem success_with_missing_slot_is_undefined :
    sourcePublish callerMemory [] ⟨7, 0, []⟩ 0 completedHandle emptyObservation = none := rfl

theorem failed_call_does_not_dereference_missing_slot :
    (sourcePublish callerMemory [] ⟨7, 0, []⟩ 4 completedHandle emptyObservation).map
      SourcePublished.status = some 4 := rfl

end Mettapedia.GSLT.LanguageDef.NativeExecutionPublication
