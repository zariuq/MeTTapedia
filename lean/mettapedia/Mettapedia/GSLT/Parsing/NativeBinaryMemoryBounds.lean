import Mettapedia.GSLT.Parsing.NativeBinaryMemoryWord

/-! Exact word and cursor bounds for successful native binary memory reads. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.NativeBinaryMemoryWord

open LanguageDef.NativeOps
open BinaryRecordCodec (WordCodec)

theorem source_success_bounds (codec : WordCodec) (memory : SourceMemory)
    (data : Option Address) (length position value next : Nat)
    (accepted : sourceRun codec memory data length position = some (.ok (value, next))) :
    value < 2 ^ 64 ∧ position < next ∧ next ≤ length := by
  unfold sourceRun at accepted
  split at accepted
  · cases accepted
  · rename_i inside
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · rename_i validCodec
        have valid : codec.Valid := Decidable.of_not_not validCodec
        split at accepted
        · cases accepted
        · rename_i nonempty
          cases data with
          | none => cases accepted
          | some base =>
            simp only [bind, Option.bind_some] at accepted
            cases headerRead : ByteViews.sourceAt memory (byteAddress base position) with
            | none => simp only [headerRead, Option.bind_none] at accepted; cases accepted
            | some header =>
              simp only [headerRead, Option.bind_some] at accepted
              split at accepted
              · have same := Except.ok.inj (Option.some.inj accepted)
                cases same
                exact ⟨Nat.lt_of_lt_of_le header.toNat_lt (by decide +kernel), by omega, by omega⟩
              · rename_i aboveInline
                split at accepted
                · cases accepted
                · rename_i withinPayload
                  split at accepted
                  · cases accepted
                  · rename_i available
                    cases payloadRead : ByteViews.sourceBlock memory (byteAddress base (position + 1))
                        (header.toNat - codec.inlineMax) with
                    | none => simp only [payloadRead, Option.bind_none] at accepted; cases accepted
                    | some payload =>
                      simp only [payloadRead, Option.bind_some] at accepted
                      split at accepted
                      · cases accepted
                      · have same := Except.ok.inj (Option.some.inj accepted)
                        cases same
                        have countBound : header.toNat - codec.inlineMax ≤ 8 := by
                          have maximum := valid.2.2.1
                          omega
                        have payloadLength := ByteViews.source_block_length memory
                          (header.toNat - codec.inlineMax) (byteAddress base (position + 1))
                          payload payloadRead
                        exact ⟨NativeBinaryPayload.little_endian_word_bound payload
                          (by omega), by omega, by omega⟩

theorem native_success_reflects_exact_result (codec : WordCodec)
    (nonShortest : codec.requireShortest = false) (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (data : Option Address) (length position next : Nat)
    (value : BitVec 64)
    (accepted : targetRun codec target data length position = some (.ok (value, next))) :
    ∃ word, sourceRun codec source data length position = some (.ok (word, next)) ∧
      value.toNat = word ∧ word < 2 ^ 64 ∧ position < next ∧ next ≤ length := by
  rw [memory_word_correspondence codec nonShortest source target related] at accepted
  cases parsed : sourceRun codec source data length position with
  | none => simp only [parsed, Option.map_none] at accepted; cases accepted
  | some result =>
    cases result with
    | error error =>
      simp only [parsed, Option.map_some, encodeResult, Except.map] at accepted
      cases accepted
    | ok pair =>
      rcases pair with ⟨word, remaining⟩
      simp only [parsed, Option.map_some, encodeResult, Except.map,
        Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      have bounds := source_success_bounds codec source data length position word remaining parsed
      exact ⟨word, rfl, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounds.1], bounds⟩

theorem source_success_has_exact_native_result (codec : WordCodec)
    (nonShortest : codec.requireShortest = false) (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (data : Option Address)
    (length position value next : Nat)
    (accepted : sourceRun codec source data length position = some (.ok (value, next))) :
    targetRun codec target data length position = some (.ok (BitVec.ofNat 64 value, next)) := by
  rw [memory_word_correspondence codec nonShortest source target related, accepted]
  rfl

theorem native_result_reflects (codec : WordCodec)
    (nonShortest : codec.requireShortest = false) (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (data : Option Address) (length position : Nat)
    (result : Except Failure (BitVec 64 × Nat))
    (decoded : targetRun codec target data length position = some result) :
    ∃ raw, sourceRun codec source data length position = some raw ∧ result = encodeResult raw := by
  rw [memory_word_correspondence codec nonShortest source target related] at decoded
  cases parsed : sourceRun codec source data length position with
  | none => simp only [parsed, Option.map_none] at decoded; cases decoded
  | some raw =>
    simp only [parsed, Option.map_some] at decoded
    exact ⟨raw, rfl, (Option.some.inj decoded).symm⟩

end Mettapedia.GSLT.Parsing.NativeBinaryMemoryWord
