import Mettapedia.GSLT.LanguageDef.NativeRecordAccess

/-!
The whole native record-opcode call, including its raw zero return and reader
flag write on a null record. A present record is read even if the view's error
flag was already set. This interface never reads or clears that flag. Source
and target calls use their independent typed reads and preserve the complete
operational post-state; undefined pointer reads are not converted to faults.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordOpcodeExternal

open NativeOps (Address SourceValue TargetValue SourceState TargetState StateRelated
  encodeValue encodeValues SourceExternalSemantics TargetExternalSemantics ExternalCorrespondence)
open NativeRecordAccess
open NativeWord64 (Word encode)

inductive SourceOpcode {World : Type} : SourceState World → Option Address → Word →
    SourceState World → Prop where
  | null (state : SourceState World) : SourceOpcode state none 0 state
  | absentRecord {state post : SourceState World} {view : Address}
      (absent : sourceReadPointer state.memory (field view 0) = some none)
      (poisoned : sourceSetFault state view = some post) :
      SourceOpcode state (some view) 0 post
  | present {state : SourceState World} {view record : Address} {word : Word}
      (present : sourceReadPointer state.memory (field view 0) = some (some record))
      (read : sourceReadByteWord state.memory (field record 0) = some word) :
      SourceOpcode state (some view) word state

inductive TargetOpcode {World : Type} : TargetState World → Option Address → BitVec 64 →
    TargetState World → Prop where
  | null (state : TargetState World) : TargetOpcode state none 0 state
  | absentRecord {state post : TargetState World} {view : Address}
      (absent : targetReadPointer state.memory (field view 0) = some none)
      (poisoned : targetSetFault state view = some post) :
      TargetOpcode state (some view) 0 post
  | present {state : TargetState World} {view record : Address} {word : BitVec 64}
      (present : targetReadPointer state.memory (field view 0) = some (some record))
      (read : targetReadByteWord state.memory (field record 0) = some word) :
      TargetOpcode state (some view) word state

theorem opcode_forward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Option Address)
    (word : Word) (post : SourceState SourceWorld) (called : SourceOpcode source view word post) :
    ∃ native, TargetOpcode target view (encode word) native ∧
      StateRelated worldRelated post native := by
  cases called with
  | null => exact ⟨target, .null target, related⟩
  | absentRecord absent poisoned =>
    obtain ⟨native, nativePoisoned, postRelated⟩ :=
      set_fault_forward source target related _ post poisoned
    exact ⟨native, .absentRecord
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory])
      nativePoisoned, postRelated⟩
  | present present read =>
    exact ⟨target, .present
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory])
      ((read_byte_word_result_iff source.memory target.memory related.memory _ word).mpr read), related⟩

theorem opcode_backward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Option Address)
    (word : BitVec 64) (native : TargetState TargetWorld) (called : TargetOpcode target view word native) :
    ∃ value post, SourceOpcode source view value post ∧ word = encode value ∧
      StateRelated worldRelated post native := by
  cases called with
  | null => exact ⟨0, source, .null source, rfl, related⟩
  | absentRecord absent poisoned =>
    obtain ⟨post, sourcePoisoned, postRelated⟩ :=
      set_fault_backward source target related _ native poisoned
    exact ⟨0, post, .absentRecord
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory] at absent)
      sourcePoisoned, rfl, postRelated⟩
  | present present read =>
    obtain ⟨value, sourceRead, rawEqual⟩ :=
      read_byte_word_backward source.memory target.memory related.memory _ word read
    exact ⟨value, source, .present
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory] at present)
      sourceRead, rawEqual, related⟩

def sourceExternal (World : Type) : SourceExternalSemantics World :=
  ⟨fun name arguments pre raw post => name = "record-opcode" ∧
    ∃ view word, arguments = [.reference view] ∧ raw = .word word ∧
      SourceOpcode pre view word post⟩

def targetExternal (World : Type) : TargetExternalSemantics World :=
  ⟨fun name arguments pre raw post => name = "record-opcode" ∧
    ∃ view word, arguments = [.reference view] ∧ raw = .word word ∧
      TargetOpcode pre view word post⟩

theorem external_correspondence {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) :
    ExternalCorrespondence (sourceExternal SourceWorld) (targetExternal TargetWorld) worldRelated := by
  constructor
  · intro name arguments source target raw post related called
    obtain ⟨named, view, word, args, rawEqual, opcode⟩ := called
    subst arguments raw
    obtain ⟨native, executed, postRelated⟩ := opcode_forward source target related view word post opcode
    exact ⟨native, ⟨named, view, encode word, rfl, rfl, executed⟩, postRelated⟩
  · intro name arguments source target raw native related called
    obtain ⟨named, view, word, args, rawEqual, opcode⟩ := called
    have encodedArguments : NativeOps.decodeValues (encodeValues arguments) =
        NativeOps.decodeValues [.reference view] := congrArg NativeOps.decodeValues args
    have sourceArguments : arguments = [.reference view] := by
      simpa only [NativeOps.decode_encode_values, NativeOps.decodeValues, NativeOps.decodeValue]
        using encodedArguments
    subst arguments raw
    obtain ⟨value, post, executed, valueEqual, postRelated⟩ :=
      opcode_backward source target related view word native opcode
    exact ⟨.word value, post, ⟨named, view, value, rfl, rfl, executed⟩,
      congrArg TargetValue.word valueEqual, postRelated⟩

theorem opcode_preserves_nonmemory_state {World : Type} (state : SourceState World)
    (view : Option Address) (word : Word) (post : SourceState World)
    (called : SourceOpcode state view word post) :
    post.fault = state.fault ∧ post.external = state.external ∧
      post.allocatorStats = state.allocatorStats ∧ post.allocatorAvailable = state.allocatorAvailable ∧
      post.releaseAvailable = state.releaseAvailable := by
  cases called with
  | null => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | absentRecord _ poisoned => exact source_set_fault_preserves_context _ _ _ poisoned
  | present _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem null_opcode_return_is_exact {World : Type} (state post : SourceState World)
    (word : Word) (called : SourceOpcode state none word post) : word = 0 ∧ post = state := by
  cases called
  exact ⟨rfl, rfl⟩

private def view : Address := ⟨4, 0, []⟩
private def record : Address := ⟨9, 0, []⟩
private def validMemory : NativeOps.SourceMemory :=
  ⟨fun storage element => if element = 0 then
      if storage = 4 then some (.record "RecordView" [.reference (some record), .bool true])
      else if storage = 9 then some (.record "BinaryRecord"
        [.byte 255, .reference none, .reference none, .word 0, .word 0, .word 0]) else none
    else none, fun _ => none⟩
private def emptyMemory : NativeOps.SourceMemory :=
  ⟨fun storage element => if storage = 4 ∧ element = 0 then
    some (.record "RecordView" [.reference none, .bool false]) else none, fun _ => none⟩

theorem opcode_reads_a_present_record_despite_prior_reader_fault {World : Type}
    (state : SourceState World) :
    SourceOpcode { state with memory := validMemory } (some view) 255
      { state with memory := validMemory } := .present (record := record) rfl rfl

theorem opcode_returns_zero_for_null_view {World : Type} (state : SourceState World) :
    SourceOpcode state none 0 state := .null state

theorem null_view_cannot_return_a_nonzero_opcode {World : Type} (state post : SourceState World)
    (word : Word) (nonzero : word ≠ 0) : ¬ SourceOpcode state none word post := by
  intro called
  exact nonzero (null_opcode_return_is_exact state post word called).1

theorem absent_record_sets_the_reader_flag {World : Type} (state : SourceState World) :
    ∃ post, SourceOpcode { state with memory := emptyMemory } (some view) 0 post ∧
      sourceReadBool post.memory (field view 1) = some true := by
  let post := { state with memory :=
    NativeOps.sourceStoreCell emptyMemory 4 0 (.record "RecordView" [.reference none, .bool true]) }
  have wrote : sourceSetFault { state with memory := emptyMemory } view = some post := rfl
  exact ⟨post, .absentRecord rfl wrote, source_set_fault_readback _ _ _ wrote⟩

theorem present_opcode_does_not_clear_the_reader_flag {World : Type} (state : SourceState World) :
    sourceReadBool ({ state with memory := validMemory } : SourceState World).memory
      (field view 1) = some true := rfl

end Mettapedia.GSLT.LanguageDef.NativeRecordOpcodeExternal
