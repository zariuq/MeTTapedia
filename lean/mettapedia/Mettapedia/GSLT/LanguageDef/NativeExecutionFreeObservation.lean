import Mettapedia.GSLT.LanguageDef.NativeExecutionFreeStorage
import Mettapedia.GSLT.LanguageDef.NativeExecutionOutputExternal

/-!
The physical observation destructor reads and frees its four pointer fields
in order, then frees the observation allocation. Each later field read uses
the memory left by the earlier free. The length fields are not inspected.
Concrete record layout and pointer realization remain ABI obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionFreeObservation

open NativeOps (Address SourceMemory TargetMemory MemoryRelated)

def fieldAddress (handle : Address) (index : Nat) : Address :=
  { handle with fields := handle.fields ++ [index] }

def sourceField (memory : SourceMemory) (handle : Address) (index : Nat) :
    Option (Option Address) := do
  let value ← NativeOps.sourceRead memory (fieldAddress handle index)
  NativeExecutionOutputExternal.sourcePointer value

def targetField (memory : TargetMemory) (handle : Address) (index : Nat) :
    Option (Option Address) :=
  match NativeOps.targetRead memory (fieldAddress handle index) with
  | none => none
  | some value => NativeExecutionOutputExternal.targetPointer value

theorem field_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (handle : Address) (index : Nat) :
    targetField target handle index = sourceField source handle index := by
  simp only [targetField, sourceField,
    NativeOps.memory_read_correspondence source target related]
  cases NativeOps.sourceRead source (fieldAddress handle index) with
  | none => rfl
  | some value =>
    simp only [Option.map_some, bind, Option.bind_some]
    exact NativeExecutionOutputExternal.pointer_correspondence value

def sourceFields (memory : SourceMemory) (handle : Address) (index : Nat) :
    Nat → Option SourceMemory
  | 0 => some memory
  | count + 1 => do
    let pointer ← sourceField memory handle index
    let post ← NativeExecutionFreeStorage.sourceFree memory pointer
    sourceFields post handle (index + 1) count

def targetFields (memory : TargetMemory) (handle : Address) (index : Nat) :
    Nat → Option TargetMemory
  | 0 => some memory
  | count + 1 =>
    match targetField memory handle index with
    | none => none
    | some pointer =>
      match NativeExecutionFreeStorage.targetFree memory pointer with
      | none => none
      | some post => targetFields post handle (index + 1) count

theorem fields_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (handle : Address) (index count : Nat)
    (post : SourceMemory) (freed : sourceFields source handle index count = some post) :
    ∃ native, targetFields target handle index count = some native ∧ MemoryRelated post native := by
  induction count generalizing source target index post with
  | zero =>
    have same : source = post := Option.some.inj freed
    exact ⟨target, rfl, same ▸ related⟩
  | succ count ih =>
    cases pointer : sourceField source handle index with
    | none => simp only [sourceFields, pointer, bind, Option.bind_none] at freed; cases freed
    | some address =>
      cases first : NativeExecutionFreeStorage.sourceFree source address with
      | none => simp only [sourceFields, pointer, first, bind, Option.bind_some,
          Option.bind_none] at freed; cases freed
      | some changed =>
        have continued : sourceFields changed handle (index + 1) count = some post := by
          simpa only [sourceFields, pointer, first, bind, Option.bind_some] using freed
        obtain ⟨nativeChanged, nativeFirst, firstRelated⟩ :=
          NativeExecutionFreeStorage.free_forward source target related address changed first
        obtain ⟨nativePost, nativeContinued, finalRelated⟩ :=
          ih changed nativeChanged firstRelated (index + 1) post continued
        refine ⟨nativePost, ?_, finalRelated⟩
        simp only [targetFields, field_correspondence source target related, pointer,
          nativeFirst, nativeContinued]

theorem fields_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (handle : Address) (index count : Nat)
    (native : TargetMemory) (freed : targetFields target handle index count = some native) :
    ∃ post, sourceFields source handle index count = some post ∧ MemoryRelated post native := by
  induction count generalizing source target index native with
  | zero =>
    have same : target = native := Option.some.inj freed
    exact ⟨source, rfl, same ▸ related⟩
  | succ count ih =>
    cases pointer : sourceField source handle index with
    | none =>
      simp only [targetFields, field_correspondence source target related, pointer] at freed
      cases freed
    | some address =>
      cases first : NativeExecutionFreeStorage.targetFree target address with
      | none =>
        simp only [targetFields, field_correspondence source target related, pointer, first] at freed
        cases freed
      | some changed =>
        have continued : targetFields changed handle (index + 1) count = some native := by
          simpa only [targetFields, field_correspondence source target related, pointer, first]
            using freed
        obtain ⟨sourceChanged, sourceFirst, firstRelated⟩ :=
          NativeExecutionFreeStorage.free_backward source target related address changed first
        obtain ⟨sourcePost, sourceContinued, finalRelated⟩ :=
          ih sourceChanged changed firstRelated (index + 1) native continued
        refine ⟨sourcePost, ?_, finalRelated⟩
        simp only [sourceFields, pointer, sourceFirst, bind, Option.bind_some, sourceContinued]

def sourceFree (memory : SourceMemory) (pointer : Option Address) : Option SourceMemory :=
  match pointer with
  | none => some memory
  | some handle => do
    let post ← sourceFields memory handle 0 4
    NativeExecutionFreeStorage.sourceFree post (some handle)

def targetFree (memory : TargetMemory) (pointer : Option Address) : Option TargetMemory :=
  match pointer with
  | none => some memory
  | some handle =>
    match targetFields memory handle 0 4 with
    | none => none
    | some post => NativeExecutionFreeStorage.targetFree post (some handle)

theorem observation_free_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (pointer : Option Address) (post : SourceMemory)
    (freed : sourceFree source pointer = some post) :
    ∃ native, targetFree target pointer = some native ∧ MemoryRelated post native := by
  cases pointer with
  | none =>
    have same : source = post := Option.some.inj freed
    exact ⟨target, rfl, same ▸ related⟩
  | some handle =>
    cases fields : sourceFields source handle 0 4 with
    | none => simp only [sourceFree, fields, bind, Option.bind_none] at freed; cases freed
    | some changed =>
      have final : NativeExecutionFreeStorage.sourceFree changed (some handle) = some post := by
        simpa only [sourceFree, fields, bind, Option.bind_some] using freed
      obtain ⟨nativeChanged, nativeFields, firstRelated⟩ :=
        fields_forward source target related handle 0 4 changed fields
      obtain ⟨nativePost, nativeFinal, finalRelated⟩ :=
        NativeExecutionFreeStorage.free_forward changed nativeChanged firstRelated
          (some handle) post final
      exact ⟨nativePost, by simp only [targetFree, nativeFields, nativeFinal], finalRelated⟩

theorem observation_free_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (pointer : Option Address) (native : TargetMemory)
    (freed : targetFree target pointer = some native) :
    ∃ post, sourceFree source pointer = some post ∧ MemoryRelated post native := by
  cases pointer with
  | none =>
    have same : target = native := Option.some.inj freed
    exact ⟨source, rfl, same ▸ related⟩
  | some handle =>
    cases fields : targetFields target handle 0 4 with
    | none => simp only [targetFree, fields] at freed; cases freed
    | some changed =>
      have final : NativeExecutionFreeStorage.targetFree changed (some handle) = some native := by
        simpa only [targetFree, fields] using freed
      obtain ⟨sourceChanged, sourceFields, firstRelated⟩ :=
        fields_backward source target related handle 0 4 changed fields
      obtain ⟨sourcePost, sourceFinal, finalRelated⟩ :=
        NativeExecutionFreeStorage.free_backward sourceChanged changed firstRelated
          (some handle) native final
      exact ⟨sourcePost, by simp only [sourceFree, sourceFields, bind, Option.bind_some,
        sourceFinal], finalRelated⟩

theorem source_destructor_kills_observation (memory : SourceMemory) (handle : Address)
    (post : SourceMemory) (freed : sourceFree memory (some handle) = some post) :
    (∀ element, post.cells handle.storage element = none) ∧ post.owned handle.storage = none := by
  cases fields : sourceFields memory handle 0 4 with
  | none => simp only [sourceFree, fields, bind, Option.bind_none] at freed; cases freed
  | some changed =>
    have final : NativeExecutionFreeStorage.sourceFree changed (some handle) = some post := by
      simpa only [sourceFree, fields, bind, Option.bind_some] using freed
    exact NativeExecutionFreeStorage.source_freed_allocation_is_dead changed handle post final

theorem null_observation_free_is_noop (memory : TargetMemory) :
    targetFree memory none = some memory := rfl

end Mettapedia.GSLT.LanguageDef.NativeExecutionFreeObservation
