import Mettapedia.GSLT.LanguageDef.NativeRecordOperand

/-!
Whole native record-word, record-count and record-bytes interfaces. The shared
operand guard executes before payload access, and its post-state is retained.
Missing operands return the exact C default. Bytes return a borrowed pointer
and length, without copying, allocation or a nullness test. The logical union
profile uses the active payload: a word, a Bytes record, or a Words record.
Concrete union and structure layout is a separate ABI obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordSelectorsExternal

open NativeOps (Address SourceValue TargetValue SourceMemory TargetMemory SourceState
  TargetState StateRelated MemoryRelated encodeValue encodeValues SourceExternalSemantics
  TargetExternalSemantics ExternalCorrespondence)
open NativeRecordAccess
open NativeWord64 (Word encode)

inductive Selector where
  | word | count | bytes
  deriving DecidableEq, Repr

def name : Selector → String
  | .word => "record-word" | .count => "record-count" | .bytes => "record-bytes"

def kind : Selector → NativeRecordOperand.Kind
  | .word => .word | .count => .words | .bytes => .bytes

def sourceDefault : Selector → SourceValue
  | .word | .count => .word 0
  | .bytes => .array .byte none 0

def targetDefault : Selector → TargetValue
  | .word | .count => .word 0
  | .bytes => .array .byte none 0

theorem default_correspondence (selector : Selector) :
    targetDefault selector = encodeValue (sourceDefault selector) := by cases selector <;> rfl

def sourcePayload (selector : Selector) (memory : SourceMemory) (operand : Address) :
    Option SourceValue :=
  match selector with
  | .word => (sourceReadWord memory (field operand 2)).map SourceValue.word
  | .count => (sourceReadWord memory (field (field operand 2) 2)).map SourceValue.word
  | .bytes => do
    let pointer ← sourceReadPointer memory (field (field operand 2) 0)
    let length ← sourceReadWord memory (field (field operand 2) 1)
    some (.array .byte pointer length)

def targetPayload (selector : Selector) (memory : TargetMemory) (operand : Address) :
    Option TargetValue :=
  match selector with
  | .word => (targetReadWord memory (field operand 2)).map TargetValue.word
  | .count => (targetReadWord memory (field (field operand 2) 2)).map TargetValue.word
  | .bytes =>
    match targetReadPointer memory (field (field operand 2) 0) with
    | none => none
    | some pointer =>
      match targetReadWord memory (field (field operand 2) 1) with
      | none => none
      | some length => some (.array .byte pointer length)

theorem payload_correspondence (selector : Selector) (source : SourceMemory)
    (target : TargetMemory) (related : MemoryRelated source target) (operand : Address) :
    targetPayload selector target operand =
      (sourcePayload selector source operand).map encodeValue := by
  cases selector with
  | word =>
    simp only [targetPayload, sourcePayload, read_word_correspondence source target related]
    cases sourceReadWord source (field operand 2) <;> rfl
  | count =>
    simp only [targetPayload, sourcePayload, read_word_correspondence source target related]
    cases sourceReadWord source (field (field operand 2) 2) <;> rfl
  | bytes =>
    simp only [targetPayload, sourcePayload, read_pointer_correspondence source target related,
      read_word_correspondence source target related]
    cases sourceReadPointer source (field (field operand 2) 0) with
    | none => rfl
    | some pointer => cases sourceReadWord source (field (field operand 2) 1) <;> rfl

inductive SourceRead {World : Type} : Selector → SourceState World → Option Address → Word →
    SourceValue → SourceState World → Prop where
  | missing {selector : Selector} {state post : SourceState World} {view : Option Address} {index : Word}
      (selected : NativeRecordOperand.SourceOperand state view index (kind selector) none post) :
      SourceRead selector state view index (sourceDefault selector) post
  | present {selector : Selector} {state post : SourceState World} {view : Option Address}
      {index : Word} {operand : Address} {value : SourceValue}
      (selected : NativeRecordOperand.SourceOperand state view index (kind selector) (some operand) post)
      (read : sourcePayload selector post.memory operand = some value) :
      SourceRead selector state view index value post

inductive TargetRead {World : Type} : Selector → TargetState World → Option Address → BitVec 64 →
    TargetValue → TargetState World → Prop where
  | missing {selector : Selector} {state post : TargetState World} {view : Option Address} {index : BitVec 64}
      (selected : NativeRecordOperand.TargetOperand state view index (kind selector) none post) :
      TargetRead selector state view index (targetDefault selector) post
  | present {selector : Selector} {state post : TargetState World} {view : Option Address}
      {index : BitVec 64} {operand : Address} {value : TargetValue}
      (selected : NativeRecordOperand.TargetOperand state view index (kind selector) (some operand) post)
      (read : targetPayload selector post.memory operand = some value) :
      TargetRead selector state view index value post

theorem payload_backward (selector : Selector) (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (operand : Address) (native : TargetValue)
    (read : targetPayload selector target operand = some native) :
    ∃ value, sourcePayload selector source operand = some value ∧ native = encodeValue value := by
  rw [payload_correspondence selector source target related] at read
  cases found : sourcePayload selector source operand with
  | none => simp only [found, Option.map_none] at read; cases read
  | some value =>
    simp only [found, Option.map_some] at read
    exact ⟨value, rfl, (Option.some.inj read).symm⟩

theorem read_forward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (selector : Selector) (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Option Address) (index : Word)
    (value : SourceValue) (post : SourceState SourceWorld)
    (called : SourceRead selector source view index value post) :
    ∃ native, TargetRead selector target view (encode index) (encodeValue value) native ∧
      StateRelated worldRelated post native := by
  cases called with
  | missing selected =>
    obtain ⟨native, nativeSelected, postRelated⟩ := NativeRecordOperand.operand_forward
      source target related view index (kind selector) none post selected
    exact ⟨native, by simpa only [default_correspondence] using TargetRead.missing nativeSelected,
      postRelated⟩
  | present selected read =>
    obtain ⟨native, nativeSelected, postRelated⟩ := NativeRecordOperand.operand_forward
      source target related view index (kind selector) _ post selected
    refine ⟨native, .present nativeSelected ?_, postRelated⟩
    rw [payload_correspondence selector post.memory native.memory postRelated.memory, read]
    rfl

theorem read_backward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (selector : Selector) (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Option Address) (index : Word)
    (value : TargetValue) (native : TargetState TargetWorld)
    (called : TargetRead selector target view (encode index) value native) :
    ∃ raw post, SourceRead selector source view index raw post ∧ value = encodeValue raw ∧
      StateRelated worldRelated post native := by
  cases called with
  | missing selected =>
    obtain ⟨post, sourceSelected, postRelated⟩ := NativeRecordOperand.operand_backward
      source target related view index (kind selector) none native selected
    exact ⟨sourceDefault selector, post, .missing sourceSelected, default_correspondence selector,
      postRelated⟩
  | present selected read =>
    obtain ⟨post, sourceSelected, postRelated⟩ := NativeRecordOperand.operand_backward
      source target related view index (kind selector) _ native selected
    obtain ⟨raw, sourceRead, rawEqual⟩ :=
      payload_backward selector post.memory native.memory postRelated.memory _ value read
    exact ⟨raw, post, .present sourceSelected sourceRead, rawEqual, postRelated⟩

def sourceExternal (World : Type) : SourceExternalSemantics World :=
  ⟨fun calledName arguments pre raw post =>
    ∃ selector view index, calledName = name selector ∧
      arguments = [.reference view, .word index] ∧ SourceRead selector pre view index raw post⟩

def targetExternal (World : Type) : TargetExternalSemantics World :=
  ⟨fun calledName arguments pre raw post =>
    ∃ selector view index, calledName = name selector ∧
      arguments = [.reference view, .word index] ∧ TargetRead selector pre view index raw post⟩

theorem external_correspondence {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) :
    ExternalCorrespondence (sourceExternal SourceWorld) (targetExternal TargetWorld) worldRelated := by
  constructor
  · intro calledName arguments source target raw post related called
    obtain ⟨selector, view, index, named, args, read⟩ := called
    subst arguments
    obtain ⟨native, executed, postRelated⟩ :=
      read_forward selector source target related view index raw post read
    exact ⟨native, ⟨selector, view, encode index, named, rfl, executed⟩, postRelated⟩
  · intro calledName arguments source target raw native related called
    obtain ⟨selector, view, index, named, args, read⟩ := called
    have decodedArguments := congrArg NativeOps.decodeValues args
    have sourceArguments : arguments = [.reference view, .word index.toFin] := by
      simpa only [NativeOps.decode_encode_values, NativeOps.decodeValues, NativeOps.decodeValue]
        using decodedArguments
    have normalized : encode index.toFin = index := BitVec.ofFin_toFin index
    rw [← normalized] at read
    obtain ⟨value, post, executed, rawEqual, postRelated⟩ :=
      read_backward selector source target related view index.toFin raw native read
    exact ⟨value, post, ⟨selector, view, index.toFin, named, sourceArguments, executed⟩,
      rawEqual, postRelated⟩

theorem selector_preserves_nonmemory_state {World : Type} (selector : Selector)
    (state : SourceState World) (view : Option Address) (index : Word) (value : SourceValue)
    (post : SourceState World) (called : SourceRead selector state view index value post) :
    post.fault = state.fault ∧ post.external = state.external ∧
      post.allocatorStats = state.allocatorStats ∧ post.allocatorAvailable = state.allocatorAvailable ∧
      post.releaseAvailable = state.releaseAvailable := by
  cases called with
  | missing selected => exact NativeRecordOperand.operand_preserves_nonmemory_state _ _ _ _ _ _ selected
  | present selected _ => exact NativeRecordOperand.operand_preserves_nonmemory_state _ _ _ _ _ _ selected

theorem null_selector_returns_its_exact_default {World : Type} (selector : Selector)
    (state : SourceState World) (index : Word) :
    SourceRead selector state none index (sourceDefault selector) state :=
  .missing (.null state index (kind selector))

theorem null_selector_has_no_other_value_or_effect {World : Type} (selector : Selector)
    (state post : SourceState World) (index : Word) (value : SourceValue)
    (called : SourceRead selector state none index value post) :
    value = sourceDefault selector ∧ post = state := by
  cases called with
  | missing selected => cases selected; exact ⟨rfl, rfl⟩
  | present selected _ => cases selected

private def view : Address := ⟨4, 0, []⟩
private def record : Address := ⟨9, 0, []⟩
private def operands : Address := ⟨12, 0, []⟩
private def bytes : Address := ⟨30, 0, []⟩
private def memory (tag : Word) (payload : SourceValue) (poisoned : Bool := false) : SourceMemory :=
  ⟨fun storage element => if element = 0 then
      if storage = 4 then some (.record "RecordView" [.reference (some record), .bool poisoned])
      else if storage = 9 then some (.record "BinaryRecord"
        [.byte 14, .reference none, .reference (some operands), .word 1, .word 0, .word 0])
      else if storage = 12 then some (.record "Operand" [.reference none, .word tag, payload])
      else none else none, fun _ => none⟩

private theorem selected_operand {World : Type} (state : SourceState World)
    (selectedKind : NativeRecordOperand.Kind) (payload : SourceValue) :
    NativeRecordOperand.SourceOperand
      { state with memory := memory (NativeRecordOperand.sourceKind selectedKind) payload }
      (some view) 0 selectedKind (some operands)
      { state with memory := memory (NativeRecordOperand.sourceKind selectedKind) payload } := by
  apply NativeRecordOperand.SourceOperand.found selectedKind (record := record)
    (operands := operands) (index := 0) (count := 1)
  · exact ⟨rfl, rfl⟩
  · rfl
  · decide
  · rfl
  · rfl

theorem word_reads_the_selected_union_word {World : Type} (state : SourceState World) :
    SourceRead .word { state with memory := memory 0 (.word 17) } (some view) 0 (.word 17)
      { state with memory := memory 0 (.word 17) } := by
  apply SourceRead.present (operand := operands)
  · exact selected_operand state .word (.word 17)
  · rfl

theorem count_reads_word_count_without_reading_word_bytes {World : Type} (state : SourceState World) :
    SourceRead .count
      { state with memory := memory 2 (.record "Words"
          [.reference (some bytes), .word 73, .word 73,
            .record "WordCodec" [.byte 247, .byte 8, .bool false]]) }
      (some view) 0 (.word 73)
      { state with memory := memory 2 (.record "Words"
          [.reference (some bytes), .word 73, .word 73,
            .record "WordCodec" [.byte 247, .byte 8, .bool false]]) } := by
  apply SourceRead.present (operand := operands)
  · exact selected_operand state .words (.record "Words"
      [.reference (some bytes), .word 73, .word 73,
        .record "WordCodec" [.byte 247, .byte 8, .bool false]])
  · rfl

theorem bytes_preserve_the_borrowed_pointer_and_length {World : Type} (state : SourceState World) :
    SourceRead .bytes
      { state with memory := memory 1 (.record "Bytes" [.reference (some bytes), .word 3]) }
      (some view) 0 (.array .byte (some bytes) 3)
      { state with memory := memory 1 (.record "Bytes" [.reference (some bytes), .word 3]) } := by
  apply SourceRead.present (operand := operands)
  · exact selected_operand state .bytes (.record "Bytes" [.reference (some bytes), .word 3])
  · rfl

theorem poisoned_selector_returns_default_without_payload_access {World : Type}
    (selector : Selector) (state : SourceState World) :
    SourceRead selector { state with memory := memory 7 .unit true } (some view) 0
      (sourceDefault selector) { state with memory := memory 7 .unit true } :=
  .missing (.poisoned 0 (kind selector) rfl)

private def poisonedMemory (tag : Word) (payload : SourceValue) : SourceMemory :=
  NativeOps.sourceStoreCell (memory tag payload) 4 0
    (.record "RecordView" [.reference (some record), .bool true])

theorem wrong_kind_returns_zero_and_sets_the_reader_flag {World : Type}
    (state : SourceState World) :
    SourceRead .word { state with memory := memory 1 .unit } (some view) 0 (.word 0)
      { state with memory := poisonedMemory 1 .unit } ∧
    sourceReadBool (poisonedMemory 1 .unit) (field view 1) = some true := by
  constructor
  · apply SourceRead.missing
    exact NativeRecordOperand.SourceOperand.wrongKind .word (record := record)
      (operands := operands) (index := 0) (count := 1) (actual := 1)
      ⟨rfl, rfl⟩ rfl (by decide) rfl rfl (by decide) rfl
  · rfl

theorem bad_index_returns_default_before_selected_operand_access {World : Type}
    (selector : Selector) (state : SourceState World) :
    SourceRead selector { state with memory := memory 7 .unit } (some view) 1
      (sourceDefault selector) { state with memory := poisonedMemory 7 .unit } ∧
    sourceReadBool (poisonedMemory 7 .unit) (field view 1) = some true := by
  constructor
  · apply SourceRead.missing
    exact NativeRecordOperand.SourceOperand.outOfRange (kind selector) (record := record)
      (index := 1) (count := 1) ⟨rfl, rfl⟩ rfl (by decide) rfl
  · rfl

theorem reader_fault_does_not_become_a_context_fault {World : Type} (state : SourceState World) :
    ({ state with memory := poisonedMemory 1 .unit } : SourceState World).fault = state.fault := rfl

end Mettapedia.GSLT.LanguageDef.NativeRecordSelectorsExternal
