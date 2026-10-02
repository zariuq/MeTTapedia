import Mettapedia.GSLT.LanguageDef.NativeOpsExternal
import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryEffects

/-!
Typed field access for the native binary-record interface. The record view has
a record pointer followed by its own error flag. Reads use the existing live
memory profile and retain aliases. Setting that flag changes memory without
changing the operational context or any allocator or external state. Logical
field paths require a separate concrete structure-layout realization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordAccess

open NativeOps (Address SourceValue TargetValue SourceMemory TargetMemory SourceState
  TargetState MemoryRelated StateRelated encodeValue)
open NativeWord64 (Word encode)

def field (address : Address) (index : Nat) : Address :=
  { address with fields := address.fields ++ [index] }

def sourcePointer : SourceValue → Option (Option Address)
  | .reference pointer => some pointer
  | _ => none

def targetPointer : TargetValue → Option (Option Address)
  | .reference pointer => some pointer
  | _ => none

def sourceBool : SourceValue → Option Bool
  | .bool value => some value
  | _ => none

def targetBool : TargetValue → Option Bool
  | .bool value => some value
  | _ => none

def sourceWord : SourceValue → Option Word
  | .word value => some value
  | _ => none

def targetWord : TargetValue → Option (BitVec 64)
  | .word value => some value
  | _ => none

def sourceByteWord : SourceValue → Option Word
  | .byte value => some (NativeWord64.sourceToWord value)
  | _ => none

def targetByteWord : TargetValue → Option (BitVec 64)
  | .byte value => some (NativeWord64.targetToWord value)
  | _ => none

theorem pointer_correspondence (value : SourceValue) :
    targetPointer (encodeValue value) = sourcePointer value := by cases value <;> rfl

theorem bool_correspondence (value : SourceValue) :
    targetBool (encodeValue value) = sourceBool value := by cases value <;> rfl

theorem word_correspondence (value : SourceValue) :
    targetWord (encodeValue value) = (sourceWord value).map encode := by cases value <;> rfl

theorem byte_word_correspondence (value : SourceValue) :
    targetByteWord (encodeValue value) = (sourceByteWord value).map encode := by
  cases value <;> rfl

def sourceReadPointer (memory : SourceMemory) (address : Address) : Option (Option Address) :=
  (NativeOps.sourceRead memory address).bind sourcePointer

def targetReadPointer (memory : TargetMemory) (address : Address) : Option (Option Address) :=
  (NativeOps.targetRead memory address).bind targetPointer

def sourceReadBool (memory : SourceMemory) (address : Address) : Option Bool :=
  (NativeOps.sourceRead memory address).bind sourceBool

def targetReadBool (memory : TargetMemory) (address : Address) : Option Bool :=
  (NativeOps.targetRead memory address).bind targetBool

def sourceReadWord (memory : SourceMemory) (address : Address) : Option Word :=
  (NativeOps.sourceRead memory address).bind sourceWord

def targetReadWord (memory : TargetMemory) (address : Address) : Option (BitVec 64) :=
  (NativeOps.targetRead memory address).bind targetWord

def sourceReadByteWord (memory : SourceMemory) (address : Address) : Option Word :=
  (NativeOps.sourceRead memory address).bind sourceByteWord

def targetReadByteWord (memory : TargetMemory) (address : Address) : Option (BitVec 64) :=
  (NativeOps.targetRead memory address).bind targetByteWord

theorem read_pointer_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) :
    targetReadPointer target address = sourceReadPointer source address := by
  simp only [targetReadPointer, sourceReadPointer,
    NativeOps.memory_read_correspondence source target related]
  cases read : NativeOps.sourceRead source address with
  | none => rfl
  | some value => exact pointer_correspondence value

theorem read_bool_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) :
    targetReadBool target address = sourceReadBool source address := by
  simp only [targetReadBool, sourceReadBool,
    NativeOps.memory_read_correspondence source target related]
  cases read : NativeOps.sourceRead source address with
  | none => rfl
  | some value => exact bool_correspondence value

theorem read_word_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) :
    targetReadWord target address = (sourceReadWord source address).map encode := by
  simp only [targetReadWord, sourceReadWord,
    NativeOps.memory_read_correspondence source target related]
  cases read : NativeOps.sourceRead source address with
  | none => rfl
  | some value => exact word_correspondence value

theorem read_byte_word_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) :
    targetReadByteWord target address = (sourceReadByteWord source address).map encode := by
  simp only [targetReadByteWord, sourceReadByteWord,
    NativeOps.memory_read_correspondence source target related]
  cases read : NativeOps.sourceRead source address with
  | none => rfl
  | some value => exact byte_word_correspondence value

private theorem encoded_word_eq_iff (left right : Word) :
    encode left = encode right ↔ left = right := by
  constructor
  · intro same
    apply Fin.ext
    have values := congrArg BitVec.toNat same
    simpa only [NativeWord64.encode_toNat] using values
  · intro same; rw [same]

theorem read_word_result_iff (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (value : Word) :
    targetReadWord target address = some (encode value) ↔
      sourceReadWord source address = some value := by
  rw [read_word_correspondence source target related]
  cases sourceReadWord source address <;> simp only [Option.map_none, Option.map_some,
    Option.some.injEq, encoded_word_eq_iff, reduceCtorEq]

theorem read_byte_word_result_iff (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (value : Word) :
    targetReadByteWord target address = some (encode value) ↔
      sourceReadByteWord source address = some value := by
  rw [read_byte_word_correspondence source target related]
  cases sourceReadByteWord source address <;> simp only [Option.map_none, Option.map_some,
    Option.some.injEq, encoded_word_eq_iff, reduceCtorEq]

theorem read_byte_word_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (native : BitVec 64)
    (read : targetReadByteWord target address = some native) :
    ∃ value, sourceReadByteWord source address = some value ∧ native = encode value := by
  rw [read_byte_word_correspondence source target related] at read
  cases found : sourceReadByteWord source address with
  | none => simp only [found, Option.map_none] at read; cases read
  | some value =>
    simp only [found, Option.map_some] at read
    exact ⟨value, rfl, (Option.some.inj read).symm⟩

theorem read_word_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (native : BitVec 64)
    (read : targetReadWord target address = some native) :
    ∃ value, sourceReadWord source address = some value ∧ native = encode value := by
  rw [read_word_correspondence source target related] at read
  cases found : sourceReadWord source address with
  | none => simp only [found, Option.map_none] at read; cases read
  | some value =>
    simp only [found, Option.map_some] at read
    exact ⟨value, rfl, (Option.some.inj read).symm⟩

def sourceSetFault {World : Type} (state : SourceState World) (view : Address) :
    Option (SourceState World) := do
  let memory ← NativeOps.sourceWrite state.memory (field view 1) (.bool true)
  some { state with memory := memory }

def targetSetFault {World : Type} (state : TargetState World) (view : Address) :
    Option (TargetState World) :=
  match NativeOps.targetWrite state.memory (field view 1) (.bool true) with
  | none => none
  | some memory => some { state with memory := memory }

theorem set_fault_forward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Address)
    (post : SourceState SourceWorld) (wrote : sourceSetFault source view = some post) :
    ∃ native, targetSetFault target view = some native ∧
      StateRelated worldRelated post native := by
  cases written : NativeOps.sourceWrite source.memory (field view 1) (.bool true) with
  | none => simp only [sourceSetFault, written, bind, Option.bind_none] at wrote; cases wrote
  | some memory =>
    have equal : { source with memory := memory } = post := by
      apply Option.some.inj
      simpa only [sourceSetFault, written, bind, Option.bind_some] using wrote
    rw [← equal]
    obtain ⟨nativeMemory, nativeWrite, memoryRelated⟩ := NativeOps.memory_write_forward
      source.memory target.memory related.memory (field view 1) (.bool true) memory written
    refine ⟨{ target with memory := nativeMemory }, ?_,
      ⟨memoryRelated, related.fault, related.allocator, related.release, related.external,
        related.allocatorStats⟩⟩
    change NativeOps.targetWrite target.memory (field view 1) (.bool true) = some nativeMemory
      at nativeWrite
    simp only [targetSetFault, nativeWrite]

theorem set_fault_backward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Address)
    (native : TargetState TargetWorld) (wrote : targetSetFault target view = some native) :
    ∃ post, sourceSetFault source view = some post ∧
      StateRelated worldRelated post native := by
  cases written : NativeOps.targetWrite target.memory (field view 1) (.bool true) with
  | none => simp only [targetSetFault, written] at wrote; cases wrote
  | some memory =>
    have equal : { target with memory := memory } = native := by
      apply Option.some.inj
      simpa only [targetSetFault, written] using wrote
    rw [← equal]
    obtain ⟨sourceMemory, sourceWrite, memoryRelated⟩ := NativeOps.memory_write_backward
      source.memory target.memory related.memory (field view 1) (.bool true) memory written
    refine ⟨{ source with memory := sourceMemory }, ?_,
      ⟨memoryRelated, related.fault, related.allocator, related.release, related.external,
        related.allocatorStats⟩⟩
    simp only [sourceSetFault, sourceWrite, bind, Option.bind_some]

theorem source_set_fault_preserves_context {World : Type} (state : SourceState World)
    (view : Address) (post : SourceState World) (wrote : sourceSetFault state view = some post) :
    post.fault = state.fault ∧ post.external = state.external ∧
      post.allocatorStats = state.allocatorStats ∧ post.allocatorAvailable = state.allocatorAvailable ∧
      post.releaseAvailable = state.releaseAvailable := by
  cases written : NativeOps.sourceWrite state.memory (field view 1) (.bool true) with
  | none => simp only [sourceSetFault, written, bind, Option.bind_none] at wrote; cases wrote
  | some memory =>
    have equal : { state with memory := memory } = post := by
      apply Option.some.inj
      simpa only [sourceSetFault, written, bind, Option.bind_some] using wrote
    rw [← equal]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem source_set_fault_readback {World : Type} (state : SourceState World)
    (view : Address) (post : SourceState World) (wrote : sourceSetFault state view = some post) :
    sourceReadBool post.memory (field view 1) = some true := by
  cases written : NativeOps.sourceWrite state.memory (field view 1) (.bool true) with
  | none => simp only [sourceSetFault, written, bind, Option.bind_none] at wrote; cases wrote
  | some memory =>
    have equal : { state with memory := memory } = post := by
      apply Option.some.inj
      simpa only [sourceSetFault, written, bind, Option.bind_some] using wrote
    rw [← equal]
    simp only [sourceReadBool, NativeOps.source_read_after_write _ _ _ _ written,
      Option.bind_some, sourceBool]

end Mettapedia.GSLT.LanguageDef.NativeRecordAccess
