import Mettapedia.GSLT.Parsing.NativeBinaryWord
import Mettapedia.GSLT.LanguageDef.NativeOpsByteViews

/-!
The memory-reading portion of the binary word call used by the native record
iterator. Cursor and codec refusals occur before byte reads. Only the header
and its required payload are read; unrelated buffer cells need not be live.
The source uses arithmetic little-endian decoding and the target uses the
unsigned OR/shift loop. The declared non-shortest codec policy is preserved.
Caller publication and concrete size_t/pointer layout are separate steps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.NativeBinaryMemoryWord

open LanguageDef.NativeOps
open BinaryRecordCodec (WordCodec)

inductive Failure where
  | invalidRequest | invalidHeader | truncatedWord | noncanonicalWord
  deriving DecidableEq, Repr

def byteAddress (base : Address) (offset : Nat) : Address :=
  { base with element := base.element + offset }

def cCodecValid (codec : WordCodec) : Prop :=
  1 ≤ codec.payloadMax ∧ codec.payloadMax ≤ 8 ∧ codec.inlineMax + codec.payloadMax ≤ 255

instance (codec : WordCodec) : Decidable (cCodecValid codec) :=
  inferInstanceAs (Decidable
    (1 ≤ codec.payloadMax ∧ codec.payloadMax ≤ 8 ∧ codec.inlineMax + codec.payloadMax ≤ 255))

theorem codec_valid_correspondence (codec : WordCodec) : cCodecValid codec ↔ codec.Valid := by
  constructor
  · intro valid
    rcases valid with ⟨minimum, maximum, sum⟩
    exact ⟨by omega, minimum, maximum, sum⟩
  · intro valid
    exact ⟨valid.2.1, valid.2.2.1, valid.2.2.2⟩

def sourceRun (codec : WordCodec) (memory : SourceMemory) (data : Option Address)
    (length position : Nat) : Option (Except Failure (Nat × Nat)) :=
  if length < position then some (.error .invalidRequest)
  else if data = none ∧ length ≠ 0 then some (.error .invalidRequest)
  else if ¬ codec.Valid then some (.error .invalidRequest)
  else if position = length then some (.error .truncatedWord)
  else do
    let base ← data
    let header ← ByteViews.sourceAt memory (byteAddress base position)
    if header.toNat ≤ codec.inlineMax then some (.ok (header.toNat, position + 1))
    else
      let count := header.toNat - codec.inlineMax
      if codec.payloadMax < count then some (.error .invalidHeader)
      else if length - (position + 1) < count then some (.error .truncatedWord)
      else do
        let payload ← ByteViews.sourceBlock memory (byteAddress base (position + 1)) count
        let value := BinaryRecordCodec.littleEndian payload
        if codec.requireShortest &&
            (value ≤ codec.inlineMax || (1 < count && payload.getLast? == some 0)) then
          some (.error .noncanonicalWord)
        else some (.ok (value, position + 1 + count))

def targetRun (codec : WordCodec) (memory : TargetMemory) (data : Option Address)
    (length position : Nat) : Option (Except Failure (BitVec 64 × Nat)) :=
  if length < position then some (.error .invalidRequest)
  else if data = none ∧ length ≠ 0 then some (.error .invalidRequest)
  else if ¬ cCodecValid codec then some (.error .invalidRequest)
  else if position = length then some (.error .truncatedWord)
  else
    match data with
    | none => none
    | some base =>
      match ByteViews.targetAt memory (byteAddress base position) with
      | none => none
      | some header =>
        if header.toNat ≤ codec.inlineMax then
          some (.ok (BitVec.ofNat 64 header.toNat, position + 1))
        else
          let count := header.toNat - codec.inlineMax
          if codec.payloadMax < count then some (.error .invalidHeader)
          else if length - (position + 1) < count then some (.error .truncatedWord)
          else
            match ByteViews.targetBlock memory (byteAddress base (position + 1)) count with
            | none => none
            | some payload =>
              let value := NativeBinaryPayload.nativeLoop payload 0 (BitVec.ofNat 64 0)
              if codec.requireShortest &&
                  (value.ule (BitVec.ofNat 64 codec.inlineMax) ||
                    (1 < count && (value >>> (8 * (count - 1))) == (BitVec.ofNat 64 0))) then
                some (.error .noncanonicalWord)
              else some (.ok (value, position + 1 + count))

def encodeResult : Except Failure (Nat × Nat) → Except Failure (BitVec 64 × Nat) :=
  fun result => result.map (fun pair => (BitVec.ofNat 64 pair.1, pair.2))

theorem memory_word_correspondence (codec : WordCodec)
    (nonShortest : codec.requireShortest = false) (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (data : Option Address) (length position : Nat) :
    targetRun codec target data length position =
      (sourceRun codec source data length position).map encodeResult := by
  unfold targetRun sourceRun
  simp only [codec_valid_correspondence]
  by_cases outside : length < position
  · simp only [outside, if_true, Option.map_some, encodeResult, Except.map]
  · simp only [outside, if_false]
    by_cases invalidData : data = none ∧ length ≠ 0
    · simp only [if_pos invalidData, Option.map_some, encodeResult, Except.map]
    · simp only [invalidData, if_false]
      by_cases invalidCodec : ¬ codec.Valid
      · simp only [if_pos invalidCodec, Option.map_some, encodeResult, Except.map]
      · simp only [invalidCodec, if_false]
        by_cases empty : position = length
        · simp only [empty, if_true, Option.map_some, encodeResult, Except.map]
        · simp only [empty, if_false]
          cases data with
          | none => rfl
          | some base =>
            simp only [bind, Option.bind_some,
              ByteViews.byte_cell_correspondence source target related]
            cases read : ByteViews.sourceAt source (byteAddress base position) with
            | none => rfl
            | some header =>
              simp only [Option.bind_some]
              by_cases inline : header.toNat ≤ codec.inlineMax
              · simp only [inline, if_true, Option.map_some, encodeResult, Except.map]
              · simp only [inline, if_false]
                by_cases invalidHeader : codec.payloadMax < header.toNat - codec.inlineMax
                · simp only [invalidHeader, if_true, Option.map_some, encodeResult, Except.map]
                · simp only [invalidHeader, if_false]
                  by_cases truncated : length - (position + 1) < header.toNat - codec.inlineMax
                  · simp only [truncated, if_true, Option.map_some, encodeResult, Except.map]
                  · simp only [truncated, if_false,
                      ByteViews.block_correspondence source target related]
                    cases payload : ByteViews.sourceBlock source (byteAddress base (position + 1))
                        (header.toNat - codec.inlineMax) with
                    | none => rfl
                    | some bytes =>
                      simp only [Option.bind_some, nonShortest, Bool.false_and,
                        Bool.false_eq_true, if_false, Option.map_some, encodeResult, Except.map,
                        NativeBinaryPayload.native_loop_correct]

theorem position_past_end_refuses_before_any_byte_read (codec : WordCodec)
    (memory : SourceMemory) (data : Option Address) (length position : Nat)
    (outside : length < position) :
    sourceRun codec memory data length position = some (.error .invalidRequest) := by
  simp only [sourceRun, outside, if_true]

theorem null_nonempty_data_refuses_before_any_byte_read (codec : WordCodec)
    (memory : SourceMemory) (length : Nat) (nonempty : length ≠ 0) :
    sourceRun codec memory none length 0 = some (.error .invalidRequest) := by
  rw [sourceRun, if_neg (Nat.not_lt_zero length), if_pos ⟨rfl, nonempty⟩]

end Mettapedia.GSLT.Parsing.NativeBinaryMemoryWord
