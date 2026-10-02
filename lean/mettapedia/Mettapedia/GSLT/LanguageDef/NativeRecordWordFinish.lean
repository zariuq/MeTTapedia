import Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration

/-! Preservation and reflection of iterator failure and ordered publication. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration

open NativeOps (Address SourceState TargetState StateRelated MemoryRelated)
open NativeWord64 (encode bounded)

theorem encode_bounded (value : Nat) :
    encode (bounded 64 value) = BitVec.ofNat 64 value := by
  apply BitVec.eq_of_toNat_eq
  simp only [NativeWord64.encode_toNat, bounded, BitVec.toNat_ofNat]

theorem finish_forward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view word position : Address)
    (result : Except Parsing.NativeBinaryMemoryWord.Failure (Nat × Nat))
    (returned : Bool) (post : SourceState SourceWorld)
    (finished : sourceFinish source view word position result = some (returned, post)) :
    ∃ native, targetFinish target view word position
        (Parsing.NativeBinaryMemoryWord.encodeResult result) = some (returned, native) ∧
      StateRelated worldRelated post native := by
  cases result with
  | error error =>
    cases poisoned : NativeRecordAccess.sourceSetFault source view with
    | none => simp only [sourceFinish, poisoned, Option.map_none] at finished; cases finished
    | some changed =>
      have same : (false, changed) = (returned, post) := by
        simpa only [sourceFinish, poisoned, Option.map_some, Option.some.injEq] using finished
      cases same
      obtain ⟨native, nativePoisoned, postRelated⟩ :=
        NativeRecordAccess.set_fault_forward source target related view post poisoned
      exact ⟨native, by simp only [targetFinish, Parsing.NativeBinaryMemoryWord.encodeResult,
        Except.map, nativePoisoned], postRelated⟩
  | ok pair =>
    rcases pair with ⟨value, next⟩
    cases published : NativeRecordWordPublication.sourcePublish source.memory word position
        (bounded 64 value) (bounded 64 next) with
    | none => simp only [sourceFinish, published, bind, Option.bind_none] at finished; cases finished
    | some memory =>
      have same : (true, {source with memory := memory}) = (returned, post) := by
        simpa only [sourceFinish, published, bind, Option.bind_some, Option.some.injEq] using finished
      cases same
      obtain ⟨nativeMemory, nativePublished, memoryRelated⟩ :=
        NativeRecordWordPublication.publication_forward source.memory target.memory related.memory
          word position (bounded 64 value) (bounded 64 next) memory published
      rw [encode_bounded, encode_bounded] at nativePublished
      refine ⟨{target with memory := nativeMemory}, ?_, ?_⟩
      · simp only [targetFinish, Parsing.NativeBinaryMemoryWord.encodeResult, Except.map,
          nativePublished]
      · exact ⟨memoryRelated, related.fault, related.allocator, related.release,
          related.external, related.allocatorStats⟩

theorem finish_backward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view word position : Address)
    (result : Except Parsing.NativeBinaryMemoryWord.Failure (Nat × Nat))
    (returned : Bool) (native : TargetState TargetWorld)
    (finished : targetFinish target view word position
      (Parsing.NativeBinaryMemoryWord.encodeResult result) = some (returned, native)) :
    ∃ post, sourceFinish source view word position result = some (returned, post) ∧
      StateRelated worldRelated post native := by
  cases result with
  | error error =>
    cases poisoned : NativeRecordAccess.targetSetFault target view with
    | none => simp only [targetFinish, Parsing.NativeBinaryMemoryWord.encodeResult,
                Except.map, poisoned] at finished; cases finished
    | some changed =>
      have same : (false, changed) = (returned, native) := by
        simpa only [targetFinish, Parsing.NativeBinaryMemoryWord.encodeResult,
          Except.map, poisoned, Option.some.injEq] using finished
      cases same
      obtain ⟨post, sourcePoisoned, postRelated⟩ :=
        NativeRecordAccess.set_fault_backward source target related view native poisoned
      exact ⟨post, by simp only [sourceFinish, sourcePoisoned, Option.map_some], postRelated⟩
  | ok pair =>
    rcases pair with ⟨value, next⟩
    cases published : NativeRecordWordPublication.targetPublish target.memory word position
        (BitVec.ofNat 64 value) (BitVec.ofNat 64 next) with
    | none => simp only [targetFinish, Parsing.NativeBinaryMemoryWord.encodeResult,
                Except.map, published] at finished; cases finished
    | some memory =>
      have same : (true, {target with memory := memory}) = (returned, native) := by
        simpa only [targetFinish, Parsing.NativeBinaryMemoryWord.encodeResult,
          Except.map, published, Option.some.injEq] using finished
      cases same
      have encodedPublished : NativeRecordWordPublication.targetPublish target.memory word position
          (encode (bounded 64 value)) (encode (bounded 64 next)) = some memory := by
        simpa only [encode_bounded] using published
      obtain ⟨sourceMemory, sourcePublished, memoryRelated⟩ :=
        NativeRecordWordPublication.publication_backward source.memory target.memory related.memory
          word position (bounded 64 value) (bounded 64 next) memory encodedPublished
      refine ⟨{source with memory := sourceMemory}, ?_, ?_⟩
      · simp only [sourceFinish, sourcePublished, bind, Option.bind_some]
      · exact ⟨memoryRelated, related.fault, related.allocator, related.release,
          related.external, related.allocatorStats⟩

end Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration
