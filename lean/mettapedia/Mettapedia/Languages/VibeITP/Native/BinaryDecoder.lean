import Mettapedia.GSLT.Parsing.BinaryRecordCodec
import Mettapedia.Languages.VibeITP.Spec.Instr
import Mettapedia.Languages.VibeITP.Native.GeneratedBinarySource

/-!
# Independent Vibe certificate decoder correspondence

The generic reader interprets declared record layouts and splits payloads in
bulk. The independent Vibe specification recursively reads its payload bytes
and constructs instructions directly. Correspondence retains both decoded
values and exact unconsumed suffixes, including malformed and non-shortest
word spellings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.BinaryDecoder

open Mettapedia.GSLT.Parsing

def embedError : Spec.DecodeError → BinaryRecordCodec.Error
  | .truncatedInteger => .truncatedWord
  | .truncatedBytes => .truncatedBytes
  | .unknownOpcode opcode => .unknownOpcode opcode

def lift {α : Type} (reader : Spec.Parser α) : BinaryRecordCodec.Reader α := fun bytes =>
  match reader bytes with
  | .error error => .error (embedError error)
  | .ok result => .ok result

@[simp] theorem lift_pure {α : Type} (value : α) :
    lift (Spec.Parser.pure value) = BinaryRecordCodec.pure value := rfl

@[simp] theorem lift_bind {α β : Type} (reader : Spec.Parser α) (next : α → Spec.Parser β) :
    lift (Spec.Parser.bind reader next) = BinaryRecordCodec.bind (lift reader) (fun value => lift (next value)) := by
  funext bytes
  cases decoded : reader bytes <;>
    simp [lift, Spec.Parser.bind, BinaryRecordCodec.bind, decoded]

theorem payload_correct (count : Nat) : BinaryRecordCodec.payload count = lift (Spec.Parser.le count) := by
  induction count with
  | zero =>
    funext bytes
    simp [BinaryRecordCodec.payload_zero, Spec.Parser.le, lift, Spec.Parser.pure]
  | succ count ih =>
    funext bytes
    cases bytes with
    | nil => simp [BinaryRecordCodec.payload_succ_empty, lift, Spec.Parser.le, embedError]
    | cons byte bytes =>
      rw [BinaryRecordCodec.payload_succ, ih]
      change BinaryRecordCodec.bind (lift (Spec.Parser.le count))
        (fun high => lift (Spec.Parser.pure (byte.toNat + 256 * high))) bytes = _
      rw [← lift_bind]
      rfl

theorem word_codec_exact : GeneratedBinarySource.grammar.codec = ⟨247, 8, false⟩ := rfl

theorem word_correct :
    BinaryRecordCodec.word GeneratedBinarySource.grammar.codec = lift Spec.Parser.word := by
  rw [word_codec_exact]
  funext bytes
  cases bytes with
  | nil => rfl
  | cons header bytes =>
    have header_bound : header.toNat < 256 := header.toNat_lt
    by_cases inline : header.toNat ≤ 247
    · simp [BinaryRecordCodec.word, Spec.Parser.word, lift, inline]
    · have payload_bound : ¬ header.toNat - 247 > 8 := by omega
      simp only [BinaryRecordCodec.word, inline, if_false, payload_bound]
      rw [payload_correct]
      cases decoded : Spec.Parser.le (header.toNat - 247) bytes <;>
        simp [BinaryRecordCodec.bind, lift, decoded, Spec.Parser.word, inline]

theorem word_pinned_correct :
    BinaryRecordCodec.word ⟨247, 8, false⟩ = lift Spec.Parser.word := by
  simpa only [word_codec_exact] using word_correct

theorem words_correct (count : Nat) :
    BinaryRecordCodec.words GeneratedBinarySource.grammar.codec count = lift (Spec.Parser.words count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [BinaryRecordCodec.words, Spec.Parser.words, lift_bind, lift_pure, word_correct, ih]

theorem words_pinned_correct (count : Nat) :
    BinaryRecordCodec.words ⟨247, 8, false⟩ count = lift (Spec.Parser.words count) := by
  simpa only [word_codec_exact] using words_correct count

theorem raw_correct (count : Nat) : BinaryRecordCodec.raw count = lift (Spec.Parser.raw count) := by
  funext bytes
  simp only [BinaryRecordCodec.raw, Spec.Parser.raw, lift]
  split <;> rfl

theorem counted_words_correct :
    BinaryRecordCodec.bind (BinaryRecordCodec.word GeneratedBinarySource.grammar.codec)
      (BinaryRecordCodec.words GeneratedBinarySource.grammar.codec) = lift Spec.Parser.counted := by
  rw [word_correct]
  have following : BinaryRecordCodec.words GeneratedBinarySource.grammar.codec =
      (fun count => lift (Spec.Parser.words count)) := by
    funext count
    exact words_correct count
  rw [following]
  exact (lift_bind Spec.Parser.word Spec.Parser.words).symm

theorem word_consumes : BinaryRecordCodec.Consumes (BinaryRecordCodec.word GeneratedBinarySource.grammar.codec) := by
  rw [word_correct]
  intro bytes value rest accepted
  cases decoded : Spec.Parser.word bytes with
  | error error => simp [lift, decoded] at accepted
  | ok result =>
    simp only [lift, decoded, Except.ok.injEq] at accepted
    cases accepted
    exact Spec.Parser.word_consumes bytes value rest decoded

theorem word_value_bound {bytes rest : List UInt8} {value : Nat}
    (accepted : BinaryRecordCodec.word GeneratedBinarySource.grammar.codec bytes = .ok (value, rest)) :
    value < 2 ^ 64 := by
  rw [word_codec_exact] at accepted
  cases bytes with
  | nil => simp [BinaryRecordCodec.word] at accepted
  | cons header bytes =>
    have header_bound : header.toNat < 256 := header.toNat_lt
    by_cases inline : header.toNat ≤ 247
    · simp only [BinaryRecordCodec.word, inline, if_true, Except.ok.injEq,
        Prod.mk.injEq] at accepted
      rw [← accepted.1]
      exact header_bound.trans_le (by decide)
    · have count_bound : header.toNat - 247 ≤ 8 := by omega
      simp only [BinaryRecordCodec.word, inline, if_false,
        show ¬ header.toNat - 247 > 8 by omega] at accepted
      cases decoded : BinaryRecordCodec.payload (header.toNat - 247) bytes with
      | error error => simp [BinaryRecordCodec.bind, decoded] at accepted
      | ok result =>
        rcases result with ⟨decodedValue, decodedRest⟩
        simp only [BinaryRecordCodec.bind, decoded, Bool.false_and, Bool.false_eq_true, if_false,
          Except.ok.injEq, Prod.mk.injEq] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        have bound := BinaryRecordCodec.payload_value_bound decoded
        have power_bound : 256 ^ (header.toNat - 247) ≤ 256 ^ 8 :=
          Nat.pow_le_pow_right (by decide) count_bound
        have power_exact : 256 ^ 8 = 2 ^ 64 := by decide
        omega

end Mettapedia.Languages.VibeITP.Native.BinaryDecoder
