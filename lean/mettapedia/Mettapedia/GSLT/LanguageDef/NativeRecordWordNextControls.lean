import Mettapedia.GSLT.LanguageDef.NativeRecordWordNextExternal

/-! Whole-call controls for ordered operand selection and word iteration. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration

open NativeOps (Address SourceMemory SourceState sourceRead)
open NativeRecordAccess

private def view : Address := ⟨1, 0, []⟩
private def record : Address := ⟨2, 0, []⟩
private def operand : Address := ⟨3, 0, []⟩
private def data : Address := ⟨4, 0, []⟩
private def output : Address := ⟨5, 0, []⟩
private def position : Address := ⟨6, 0, []⟩

private def memory : SourceMemory :=
  ⟨fun storage element =>
    if storage = 1 ∧ element = 0 then
      some (.record "RecordView" [.reference (some record), .bool false])
    else if storage = 2 ∧ element = 0 then
      some (.record "BinaryRecord" [.byte 25, .reference none, .reference (some operand),
        .word 1, .word 0, .word 2])
    else if storage = 3 ∧ element = 0 then
      some (.record "Operand" [.reference none, .word 2,
        .record "Words" [.reference (some data), .word 2, .word 0,
          .record "Codec" [.byte 247, .byte 8, .bool false]]])
    else if storage = 4 ∧ element = 0 then some (.byte 248)
    else if storage = 4 ∧ element = 1 then some (.byte 0)
    else if storage = 5 ∧ element = 0 then some (.word 99)
    else if storage = 6 ∧ element = 0 then some (.word 0)
    else none, fun _ => none⟩

private def state : SourceState Nat := ⟨memory, none, true, true, 23, ⟨0, 0, 0, 0, 0⟩⟩

private theorem selected : NativeRecordOperand.SourceOperand state (some view) 0 .words
    (some operand) state := by
  change NativeRecordOperand.SourceOperand state (some view) 0 .words
    (some (NativeRecordOperand.element operand 0)) state
  apply NativeRecordOperand.SourceOperand.found (record := record) (count := 1)
  · constructor <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem decoded : Parsing.NativeBinaryMemoryWord.sourceRun ⟨247, 8, false⟩
    memory (some data) 2 0 = some (.ok (0, 2)) := by decide +kernel

private theorem codec_read : NativeRecordWordCodec.sourceCodec memory operand =
    some ⟨247, 8, false⟩ := by decide +kernel

private def completed : SourceState Nat :=
  {state with memory := ((NativeRecordWordPublication.sourcePublish memory output position 0 2).getD memory)}

theorem whole_call_accepts_bytes_even_when_word_count_is_zero :
    SourceCall ⟨247, 8, false⟩ state (some view) 0 (some position) (some output) true completed := by
  apply SourceCall.present selected
  apply SourceBody.decoded (offset := 0) (length := 2) (data := some data)
    (result := .ok (0, 2))
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Or.inl (by decide)
  · exact codec_read
  · exact decoded
  · rfl

theorem successful_call_retains_the_decoded_word_and_position :
    sourceRead completed.memory output = some (.word 0) ∧
      sourceRead completed.memory position = some (.word 2) := by constructor <;> rfl

private def aliased : SourceState Nat :=
  {state with memory := ((NativeRecordWordPublication.sourcePublish memory position position 0 2).getD memory)}

theorem whole_call_allows_the_two_output_pointers_to_alias :
    SourceCall ⟨247, 8, false⟩ state (some view) 0 (some position) (some position) true aliased := by
  apply SourceCall.present selected
  apply SourceBody.decoded (offset := 0) (length := 2) (data := some data)
    (result := .ok (0, 2))
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Or.inl (by decide)
  · exact codec_read
  · exact decoded
  · rfl

theorem aliased_call_retains_the_final_position :
    sourceRead aliased.memory position = some (.word 2) := rfl

private def poisoned : SourceState Nat :=
  (sourceSetFault state view).getD state

theorem null_word_pointer_refuses_before_reading_the_position :
    SourceCall ⟨247, 8, false⟩ state (some view) 0 (some ⟨99, 0, []⟩) none false poisoned := by
  apply SourceCall.present selected
  exact SourceBody.nullWord rfl

theorem null_position_pointer_refuses_before_reading_the_word :
    SourceCall ⟨247, 8, false⟩ state (some view) 0 none (some ⟨99, 0, []⟩) false poisoned := by
  apply SourceCall.present selected
  exact SourceBody.nullPosition _ rfl

theorem refusal_changes_the_reader_flag_but_retains_caller_slots :
    sourceReadBool poisoned.memory (field view 1) = some true ∧
      sourceRead poisoned.memory output = some (.word 99) ∧
      sourceRead poisoned.memory position = some (.word 0) := by
  constructor
  · rfl
  · constructor <;> rfl

theorem reader_poisoning_retains_the_operational_context_and_world :
    poisoned.fault = none ∧ poisoned.external = 23 ∧
      poisoned.allocatorStats = state.allocatorStats := by
  constructor
  · rfl
  · constructor <;> rfl

theorem null_word_has_no_extra_native_success {World : Type}
    (codec : Parsing.BinaryRecordCodec.WordCodec) (pre post : NativeOps.TargetState World)
    (view position : Option Address) (index : BitVec 64) :
    ¬ TargetCall codec pre view index position none true post := by
  intro called
  cases called with
  | present _ body => cases body

theorem null_position_has_no_extra_native_success {World : Type}
    (codec : Parsing.BinaryRecordCodec.WordCodec) (pre post : NativeOps.TargetState World)
    (view word : Option Address) (index : BitVec 64) :
    ¬ TargetCall codec pre view index none word true post := by
  intro called
  cases called with
  | present _ body => cases body

private def endState : SourceState Nat :=
  {state with memory := (NativeOps.sourceWrite memory position (.word 2)).getD memory}

private def endPoisoned : SourceState Nat := (sourceSetFault endState view).getD endState

theorem end_of_buffer_refuses_without_overwriting_the_word :
    SourceCall ⟨247, 8, false⟩ endState (some view) 0 (some position) (some output)
      false endPoisoned := by
  apply SourceCall.present
  · apply NativeRecordOperand.SourceOperand.found (record := record) (operands := operand) (count := 1)
    · constructor <;> decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · apply SourceBody.decoded (offset := 2) (length := 2) (data := some data)
      (result := .error .truncatedWord)
    · rfl
    · rfl
    · decide +kernel
    · rfl
    · exact Or.inl (by decide)
    · rfl
    · rfl
    · rfl

theorem end_of_buffer_preserves_both_caller_values :
    sourceRead endPoisoned.memory output = some (.word 99) ∧
      sourceRead endPoisoned.memory position = some (.word 2) := by constructor <;> rfl

end Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration
