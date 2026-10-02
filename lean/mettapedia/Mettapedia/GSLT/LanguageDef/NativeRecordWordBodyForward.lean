import Mettapedia.GSLT.LanguageDef.NativeRecordWordFinish

/-! Forward preservation for every defined branch of the word-iterator body. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration

open NativeOps (Address SourceState TargetState StateRelated)
open NativeRecordAccess
open NativeWord64 (encode)
open Parsing.BinaryRecordCodec (WordCodec)

theorem body_forward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (codec : WordCodec) (nonShortest : codec.requireShortest = false)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view operand : Address)
    (position word : Option Address) (returned : Bool) (post : SourceState SourceWorld)
    (called : SourceBody codec source view operand position word returned post) :
    ∃ native, TargetBody codec target view operand position word returned native ∧
      StateRelated worldRelated post native := by
  cases called with
  | nullPosition word poisoned =>
    obtain ⟨native, nativePoisoned, postRelated⟩ :=
      set_fault_forward source target related view post poisoned
    exact ⟨native, .nullPosition word nativePoisoned, postRelated⟩
  | nullWord poisoned =>
    obtain ⟨native, nativePoisoned, postRelated⟩ :=
      set_fault_forward source target related view post poisoned
    exact ⟨native, .nullWord nativePoisoned, postRelated⟩
  | outside positionRead lengthRead outside poisoned =>
    obtain ⟨native, nativePoisoned, postRelated⟩ :=
      set_fault_forward source target related view post poisoned
    exact ⟨native, .outside
      ((read_word_result_iff source.memory target.memory related.memory _ _).mpr positionRead)
      ((read_word_result_iff source.memory target.memory related.memory _ _).mpr lengthRead)
      (by simpa only [NativeWord64.encode_toNat] using outside) nativePoisoned, postRelated⟩
  | invalidData positionRead lengthRead inside dataRead nonempty poisoned =>
    obtain ⟨native, nativePoisoned, postRelated⟩ :=
      set_fault_forward source target related view post poisoned
    exact ⟨native, .invalidData
      ((read_word_result_iff source.memory target.memory related.memory _ _).mpr positionRead)
      ((read_word_result_iff source.memory target.memory related.memory _ _).mpr lengthRead)
      (by simpa only [NativeWord64.encode_toNat] using inside)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory])
      (by simpa only [NativeWord64.encode_toNat] using nonempty) nativePoisoned, postRelated⟩
  | @decoded _ _ _ position word offset length data result returned positionRead lengthRead
      inside dataRead validData codecRead decoded finished =>
    obtain ⟨native, nativeFinished, postRelated⟩ :=
      finish_forward source target related view word position result returned post finished
    have nativeDecoded : Parsing.NativeBinaryMemoryWord.targetRun codec target.memory data
        (encode length).toNat (encode offset).toNat =
          some (Parsing.NativeBinaryMemoryWord.encodeResult result) := by
      rw [NativeWord64.encode_toNat, NativeWord64.encode_toNat,
        Parsing.NativeBinaryMemoryWord.memory_word_correspondence codec nonShortest
          source.memory target.memory related.memory, decoded]
      rfl
    exact ⟨native, .decoded
      ((read_word_result_iff source.memory target.memory related.memory _ _).mpr positionRead)
      ((read_word_result_iff source.memory target.memory related.memory _ _).mpr lengthRead)
      (by simpa only [NativeWord64.encode_toNat] using inside)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory])
      (by simpa only [NativeWord64.encode_toNat] using validData)
      (by rwa [NativeRecordWordCodec.codec_correspondence source.memory target.memory related.memory])
      nativeDecoded nativeFinished, postRelated⟩

end Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration
