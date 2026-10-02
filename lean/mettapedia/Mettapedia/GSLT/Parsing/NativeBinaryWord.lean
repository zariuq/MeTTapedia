import Mettapedia.GSLT.Parsing.NativeBinaryPayload

/-!
The decoding portion of a native binary word, after cursor and codec
validation. Header selection and payload-length refusal precede the unsigned
payload loop. The correspondence theorem covers every valid codec with the
declared non-shortest policy used by the pinned guest; it does not impose a
new canonical spelling. Cursor validation and caller writes are separate
whole-call steps. This profile does not assert compiler or CPU refinement.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.NativeBinaryWord

open BinaryRecordCodec (WordCodec Error)

def decode (codec : WordCodec) : List UInt8 → Except Error (BitVec 64 × List UInt8)
  | [] => .error .truncatedWord
  | header :: bytes =>
    if header.toNat ≤ codec.inlineMax then .ok (BitVec.ofNat 64 header.toNat, bytes)
    else
      let count := header.toNat - codec.inlineMax
      if codec.payloadMax < count then .error .invalidHeader
      else if bytes.length < count then .error .truncatedWord
      else
        let value := NativeBinaryPayload.nativeLoop (bytes.take count) 0 (BitVec.ofNat 64 0)
        if codec.requireShortest &&
            (value.ule (BitVec.ofNat 64 codec.inlineMax) ||
              (1 < count && (value >>> (8 * (count - 1))) == (BitVec.ofNat 64 0))) then
          .error .noncanonicalWord
        else .ok (value, bytes.drop count)

def encodedResult : Nat × List UInt8 → BitVec 64 × List UInt8
  | (value, rest) => (BitVec.ofNat 64 value, rest)

theorem decoder_correspondence (codec : WordCodec) (nonShortest : codec.requireShortest = false)
    (bytes : List UInt8) :
    decode codec bytes = (BinaryRecordCodec.word codec bytes).map encodedResult := by
  cases bytes with
  | nil => rfl
  | cons header bytes =>
    by_cases inline : header.toNat ≤ codec.inlineMax
    · simp only [decode, BinaryRecordCodec.word, inline, if_true, Except.map, encodedResult]
    · by_cases invalid : codec.payloadMax < header.toNat - codec.inlineMax
      · simp only [decode, BinaryRecordCodec.word, inline, invalid, if_false, if_true, Except.map]
      · by_cases truncated : bytes.length < header.toNat - codec.inlineMax
        · simp only [decode, BinaryRecordCodec.word, BinaryRecordCodec.payload,
            BinaryRecordCodec.bind, inline, invalid, truncated, if_false, if_true, Except.map]
        · simp only [decode, BinaryRecordCodec.word, BinaryRecordCodec.payload,
            BinaryRecordCodec.bind, inline, invalid, truncated, if_false, Except.map,
            nonShortest, Bool.false_and, Bool.false_eq_true, encodedResult,
            NativeBinaryPayload.native_loop_correct]

theorem successful_reference_word_bound (codec : WordCodec) (valid : codec.Valid)
    (nonShortest : codec.requireShortest = false) (bytes rest : List UInt8) (value : Nat)
    (accepted : BinaryRecordCodec.word codec bytes = .ok (value, rest)) : value < 2 ^ 64 := by
  cases bytes with
  | nil => cases accepted
  | cons header bytes =>
    by_cases inline : header.toNat ≤ codec.inlineMax
    · simp only [BinaryRecordCodec.word, inline, if_true, Except.ok.injEq, Prod.mk.injEq] at accepted
      rw [← accepted.1]
      exact Nat.lt_of_lt_of_le header.toNat_lt (by decide +kernel)
    · by_cases invalid : codec.payloadMax < header.toNat - codec.inlineMax
      · simp only [BinaryRecordCodec.word, inline, invalid, if_false, if_true] at accepted
        cases accepted
      · have countBound : header.toNat - codec.inlineMax ≤ 8 := by
          have maximum := valid.2.2.1
          omega
        by_cases truncated : bytes.length < header.toNat - codec.inlineMax
        · simp only [BinaryRecordCodec.word, BinaryRecordCodec.bind, BinaryRecordCodec.payload,
            inline, invalid, truncated, if_false, if_true] at accepted
          cases accepted
        · simp only [BinaryRecordCodec.word, BinaryRecordCodec.bind, BinaryRecordCodec.payload,
            inline, invalid, truncated, if_false, nonShortest,
            Bool.false_and, Bool.false_eq_true, Except.ok.injEq, Prod.mk.injEq] at accepted
          rw [← accepted.1]
          apply NativeBinaryPayload.little_endian_word_bound
          exact Nat.le_trans (List.length_take_le _ _) countBound

theorem native_success_reflects_exact_word (codec : WordCodec) (valid : codec.Valid)
    (nonShortest : codec.requireShortest = false) (bytes rest : List UInt8) (value : BitVec 64)
    (accepted : decode codec bytes = .ok (value, rest)) :
    ∃ word, BinaryRecordCodec.word codec bytes = .ok (word, rest) ∧
      value.toNat = word ∧ word < 2 ^ 64 := by
  rw [decoder_correspondence codec nonShortest bytes] at accepted
  cases parsed : BinaryRecordCodec.word codec bytes with
  | error error => simp only [parsed, Except.map] at accepted; cases accepted
  | ok result =>
    rcases result with ⟨word, remaining⟩
    simp only [parsed, Except.map, encodedResult, Except.ok.injEq, Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl, rfl⟩
    have bound := successful_reference_word_bound codec valid nonShortest bytes remaining word parsed
    exact ⟨word, rfl, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound], bound⟩

theorem accepts_a_non_shortest_zero : decode ⟨247, 8, false⟩ [248, 0] =
    .ok (BitVec.ofNat 64 0, []) := by decide +kernel

theorem rejects_a_truncated_eight_byte_payload : decode ⟨247, 8, false⟩ [255, 1] =
    .error .truncatedWord := by decide +kernel

theorem rejects_a_header_above_the_declared_payload_limit : decode ⟨247, 1, false⟩ [249, 0, 0] =
    .error .invalidHeader := by decide +kernel

end Mettapedia.GSLT.Parsing.NativeBinaryWord
