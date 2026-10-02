import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryEffects

/-!
The successful word-iterator publication suffix writes the decoded word before
the cursor position. These pointers may alias. Independent source and target
stores preserve that order and their complete memory effects. A decode failure
performs neither store. The reader's decoding and separate error flag belong
to its preceding interface steps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordWordPublication

open NativeOps (Address SourceMemory TargetMemory MemoryRelated SourceValue TargetValue
  sourceWrite targetWrite sourceRead targetRead encodeValue)
open NativeWord64 (Word encode)

def sourcePublish (memory : SourceMemory) (word position : Address)
    (decoded next : Word) : Option SourceMemory := do
  let intermediate ← sourceWrite memory word (.word decoded)
  sourceWrite intermediate position (.word next)

def targetPublish (memory : TargetMemory) (word position : Address)
    (decoded next : BitVec 64) : Option TargetMemory :=
  match targetWrite memory word (.word decoded) with
  | none => none
  | some intermediate =>
    match targetWrite intermediate position (.word next) with
    | none => none
    | some post => some post

theorem publication_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (word position : Address) (decoded next : Word)
    (post : SourceMemory) (published : sourcePublish source word position decoded next = some post) :
    ∃ native, targetPublish target word position (encode decoded) (encode next) = some native ∧
      MemoryRelated post native := by
  cases first : sourceWrite source word (.word decoded) with
  | none => simp only [sourcePublish, first, bind, Option.bind_none] at published; cases published
  | some intermediate =>
    have second : sourceWrite intermediate position (.word next) = some post := by
      simpa only [sourcePublish, first, bind, Option.bind_some] using published
    obtain ⟨nativeIntermediate, nativeFirst, intermediateRelated⟩ :=
      NativeOps.memory_write_forward source target related word (.word decoded) intermediate first
    obtain ⟨nativePost, nativeSecond, postRelated⟩ := NativeOps.memory_write_forward intermediate
      nativeIntermediate intermediateRelated position (.word next) post second
    refine ⟨nativePost, ?_, postRelated⟩
    change targetWrite target word (.word (encode decoded)) = some nativeIntermediate at nativeFirst
    change targetWrite nativeIntermediate position (.word (encode next)) = some nativePost at nativeSecond
    simp only [targetPublish, nativeFirst, nativeSecond]

theorem publication_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (word position : Address) (decoded next : Word)
    (native : TargetMemory)
    (published : targetPublish target word position (encode decoded) (encode next) = some native) :
    ∃ post, sourcePublish source word position decoded next = some post ∧ MemoryRelated post native := by
  cases first : targetWrite target word (.word (encode decoded)) with
  | none => simp only [targetPublish, first] at published; cases published
  | some intermediate =>
    have second : targetWrite intermediate position (.word (encode next)) = some native := by
      have identity : (match targetWrite intermediate position (.word (encode next)) with
          | none => none | some post => some post) =
            targetWrite intermediate position (.word (encode next)) := by
        cases targetWrite intermediate position (.word (encode next)) <;> rfl
      simpa only [targetPublish, first, identity] using published
    obtain ⟨sourceIntermediate, sourceFirst, intermediateRelated⟩ :=
      NativeOps.memory_write_backward source target related word (.word decoded) intermediate first
    obtain ⟨post, sourceSecond, postRelated⟩ := NativeOps.memory_write_backward sourceIntermediate
      intermediate intermediateRelated position (.word next) native second
    refine ⟨post, ?_, postRelated⟩
    simp only [sourcePublish, sourceFirst, sourceSecond, bind, Option.bind_some]

theorem successful_position_readback (memory : SourceMemory) (word position : Address)
    (decoded next : Word) (post : SourceMemory)
    (published : sourcePublish memory word position decoded next = some post) :
    sourceRead post position = some (.word next) := by
  cases first : sourceWrite memory word (.word decoded) with
  | none => simp only [sourcePublish, first, bind, Option.bind_none] at published; cases published
  | some intermediate =>
    have second : sourceWrite intermediate position (.word next) = some post := by
      simpa only [sourcePublish, first, bind, Option.bind_some] using published
    exact NativeOps.source_read_after_write _ _ _ _ second

theorem distinct_word_cell_retains_decoded_value (memory : SourceMemory) (word position : Address)
    (separate : word.storage ≠ position.storage ∨ word.element ≠ position.element)
    (decoded next : Word) (post : SourceMemory)
    (published : sourcePublish memory word position decoded next = some post) :
    sourceRead post word = some (.word decoded) := by
  cases first : sourceWrite memory word (.word decoded) with
  | none => simp only [sourcePublish, first, bind, Option.bind_none] at published; cases published
  | some intermediate =>
    have second : sourceWrite intermediate position (.word next) = some post := by
      simpa only [sourcePublish, first, bind, Option.bind_some] using published
    rw [NativeOps.source_write_preserves_other_reads _ _ _ _ second word separate]
    exact NativeOps.source_read_after_write _ _ _ _ first

theorem target_position_readback (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (word position : Address) (decoded next : Word)
    (post : TargetMemory)
    (published : targetPublish target word position (encode decoded) (encode next) = some post) :
    targetRead post position = some (.word (encode next)) := by
  obtain ⟨sourcePost, sourcePublished, postRelated⟩ :=
    publication_backward source target related word position decoded next post published
  rw [NativeOps.memory_read_correspondence sourcePost post postRelated,
    successful_position_readback source word position decoded next sourcePost sourcePublished]
  rfl

private def first : Address := ⟨1, 0, []⟩
private def second : Address := ⟨2, 0, []⟩
private def memory : SourceMemory :=
  ⟨fun storage element => if (storage = 1 ∨ storage = 2) ∧ element = 0 then
      some (.word 99) else none, fun _ => none⟩

theorem aliasing_pointers_retain_the_position :
    (sourcePublish memory first first 247 1).bind (fun post => sourceRead post first) =
      some (.word 1) := rfl

theorem separate_pointers_retain_both_values :
    (sourcePublish memory first second 247 1).bind
      (fun post => do
        let decoded ← sourceRead post first
        let position ← sourceRead post second
        some (decoded, position)) = some (.word 247, .word 1) := rfl

theorem absent_word_slot_has_no_publication :
    sourcePublish memory ⟨7, 0, []⟩ second 247 1 = none := rfl

theorem absent_position_slot_has_no_defined_completed_publication :
    sourcePublish memory first ⟨7, 0, []⟩ 247 1 = none := rfl

end Mettapedia.GSLT.LanguageDef.NativeRecordWordPublication
