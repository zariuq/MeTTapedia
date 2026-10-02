import Mettapedia.GSLT.LanguageDef.NativeRecordAccess
import Mettapedia.GSLT.Parsing.NativeBinaryMemoryWord

/-!
The inline limit, payload limit and policy stored in a Words operand's codec.
The logical nested-field profile preserves the original byte widths and bool.
Concrete structure layout and pointer realization remain ABI obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordWordCodec

open NativeOps (Address SourceMemory TargetMemory MemoryRelated)
open NativeRecordAccess
open Parsing.BinaryRecordCodec (WordCodec)

def codecAddress (operand : Address) : Address := field (field operand 2) 3

def sourceCodec (memory : SourceMemory) (operand : Address) : Option WordCodec := do
  let inlineLimit ← sourceReadByteWord memory (field (codecAddress operand) 0)
  let payloadLimit ← sourceReadByteWord memory (field (codecAddress operand) 1)
  let shortest ← sourceReadBool memory (field (codecAddress operand) 2)
  some ⟨inlineLimit.val, payloadLimit.val, shortest⟩

def targetCodec (memory : TargetMemory) (operand : Address) : Option WordCodec :=
  match targetReadByteWord memory (field (codecAddress operand) 0) with
  | none => none
  | some inlineLimit =>
    match targetReadByteWord memory (field (codecAddress operand) 1) with
    | none => none
    | some payloadLimit =>
      match targetReadBool memory (field (codecAddress operand) 2) with
      | none => none
      | some shortest => some ⟨inlineLimit.toNat, payloadLimit.toNat, shortest⟩

theorem codec_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (operand : Address) :
    targetCodec target operand = sourceCodec source operand := by
  simp only [targetCodec, sourceCodec,
    read_byte_word_correspondence source target related,
    read_bool_correspondence source target related]
  cases inlineRead : sourceReadByteWord source (field (codecAddress operand) 0) with
  | none => rfl
  | some inlineLimit =>
    cases payloadRead : sourceReadByteWord source (field (codecAddress operand) 1) with
    | none => rfl
    | some payloadLimit =>
      cases sourceReadBool source (field (codecAddress operand) 2) <;>
        simp only [Option.map_some, NativeWord64.encode_toNat, bind, Option.bind_some,
          Option.bind_none]

private theorem read_byte_word_bound (memory : SourceMemory) (address : Address)
    (word : NativeWord64.Word) (read : sourceReadByteWord memory address = some word) :
    word.val < 256 := by
  unfold sourceReadByteWord at read
  cases accessed : NativeOps.sourceRead memory address with
  | none => simp only [accessed, Option.bind_none] at read; cases read
  | some value =>
    simp only [accessed, Option.bind_some] at read
    cases value <;> simp only [sourceByteWord, reduceCtorEq] at read
    case byte byte =>
      cases read
      exact byte.isLt

theorem codec_bounds_follow_the_byte_fields (memory : SourceMemory) (operand : Address)
    (codec : WordCodec) (read : sourceCodec memory operand = some codec) :
    codec.inlineMax < 256 ∧ codec.payloadMax < 256 := by
  unfold sourceCodec at read
  cases inlineRead : sourceReadByteWord memory (field (codecAddress operand) 0) with
  | none => simp only [inlineRead, bind, Option.bind_none] at read; cases read
  | some inlineLimit =>
    cases payloadRead : sourceReadByteWord memory (field (codecAddress operand) 1) with
    | none => simp only [inlineRead, payloadRead, bind, Option.bind_some, Option.bind_none] at read
              cases read
    | some payloadLimit =>
      cases shortestRead : sourceReadBool memory (field (codecAddress operand) 2) with
      | none => simp only [inlineRead, payloadRead, shortestRead, bind,
                  Option.bind_some, Option.bind_none] at read; cases read
      | some shortest =>
        have same : WordCodec.mk inlineLimit.val payloadLimit.val shortest = codec := by
          apply Option.some.inj
          simpa only [inlineRead, payloadRead, shortestRead, bind, Option.bind_some] using read
        rw [← same]
        exact ⟨read_byte_word_bound _ _ _ inlineRead, read_byte_word_bound _ _ _ payloadRead⟩

end Mettapedia.GSLT.LanguageDef.NativeRecordWordCodec
