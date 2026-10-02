import Mettapedia.GSLT.LanguageDef.NativeRecordWordBodyForward

/-! No-invention reflection for every defined native word-iterator body branch. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration

open NativeOps (Address SourceState TargetState StateRelated)
open NativeRecordAccess
open NativeWord64 (encode)
open Parsing.BinaryRecordCodec (WordCodec)

theorem body_backward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (codec : WordCodec) (nonShortest : codec.requireShortest = false)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view operand : Address)
    (position word : Option Address) (returned : Bool) (native : TargetState TargetWorld)
    (called : TargetBody codec target view operand position word returned native) :
    ∃ post, SourceBody codec source view operand position word returned post ∧
      StateRelated worldRelated post native := by
  cases called with
  | nullPosition word poisoned =>
    obtain ⟨post, sourcePoisoned, postRelated⟩ :=
      set_fault_backward source target related view native poisoned
    exact ⟨post, .nullPosition word sourcePoisoned, postRelated⟩
  | nullWord poisoned =>
    obtain ⟨post, sourcePoisoned, postRelated⟩ :=
      set_fault_backward source target related view native poisoned
    exact ⟨post, .nullWord sourcePoisoned, postRelated⟩
  | outside positionRead lengthRead outside poisoned =>
    obtain ⟨offset, sourcePosition, offsetEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ _ positionRead
    obtain ⟨length, sourceLength, lengthEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ _ lengthRead
    obtain ⟨post, sourcePoisoned, postRelated⟩ :=
      set_fault_backward source target related view native poisoned
    exact ⟨post, .outside sourcePosition sourceLength
      (by simpa only [offsetEqual, lengthEqual, NativeWord64.encode_toNat] using outside)
      sourcePoisoned, postRelated⟩
  | invalidData positionRead lengthRead inside dataRead nonempty poisoned =>
    obtain ⟨offset, sourcePosition, offsetEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ _ positionRead
    obtain ⟨length, sourceLength, lengthEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ _ lengthRead
    obtain ⟨post, sourcePoisoned, postRelated⟩ :=
      set_fault_backward source target related view native poisoned
    exact ⟨post, .invalidData sourcePosition sourceLength
      (by simpa only [offsetEqual, lengthEqual, NativeWord64.encode_toNat] using inside)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory] at dataRead)
      (by simpa only [lengthEqual, NativeWord64.encode_toNat] using nonempty)
      sourcePoisoned, postRelated⟩
  | @decoded _ _ _ position word offset length data result returned positionRead lengthRead
      inside dataRead validData codecRead decoded finished =>
    obtain ⟨sourceOffset, sourcePosition, offsetEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ _ positionRead
    obtain ⟨sourceLength, sourceLengthRead, lengthEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ _ lengthRead
    have sourceInside : sourceOffset.val ≤ sourceLength.val := by
      simpa only [offsetEqual, lengthEqual, NativeWord64.encode_toNat] using inside
    have sourceValidData : data ≠ none ∨ sourceLength.val = 0 := by
      simpa only [lengthEqual, NativeWord64.encode_toNat] using validData
    have nativeDecoded : Parsing.NativeBinaryMemoryWord.targetRun codec target.memory data
        sourceLength.val sourceOffset.val = some result := by
      simpa only [offsetEqual, lengthEqual, NativeWord64.encode_toNat] using decoded
    obtain ⟨raw, sourceDecoded, rawEqual⟩ :=
      Parsing.NativeBinaryMemoryWord.native_result_reflects codec nonShortest source.memory
        target.memory related.memory data sourceLength.val sourceOffset.val result nativeDecoded
    rw [rawEqual] at finished
    obtain ⟨post, sourceFinished, postRelated⟩ :=
      finish_backward source target related view word position raw returned native finished
    exact ⟨post, .decoded sourcePosition sourceLengthRead sourceInside
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory] at dataRead)
      sourceValidData
      (by rwa [NativeRecordWordCodec.codec_correspondence source.memory target.memory related.memory]
        at codecRead)
      sourceDecoded sourceFinished, postRelated⟩

end Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration
