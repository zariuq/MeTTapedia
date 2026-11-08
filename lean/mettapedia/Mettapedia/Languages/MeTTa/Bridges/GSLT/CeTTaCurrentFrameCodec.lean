import Mettapedia.GSLT.LanguageDef.LayoutBitVec
import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaVariableFreshening

/-!
# Current declared 64-bit frame identity codec

The three cases below reflect `FrameIdentity` in the runtime word declaration:
prefix 00 admits a low 32-bit handle and a 30-bit generation; prefixes 01 and
1 are reserved and retain the declaration's offset total readings. Encoding
and decoding use LayoutCodes, and generated accessor expressions use its
existing lowering and BitVec semantics. There is no independent packer.

The declaration admits the all-ones handle; native frame issuance and the
parts helper additionally exclude it. Both predicates are kept distinct.
The native variable carrier is the current pair of 64-bit words. Allocation,
ownership, concurrency and C source-text extraction remain separate layers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec

open Mettapedia.GSLT.LanguageDef.LayoutCodes
open Mettapedia.GSLT.LanguageDef.LayoutAlgebra
open Mettapedia.GSLT.LanguageDef
open CeTTaVariableFreshening (VariableId)

def liveCase : Case :=
  ⟨[⟨⟨0, 32⟩, 0, 1, 2 ^ 32 - 1⟩, ⟨⟨32, 30⟩, 0, 1, 2 ^ 30 - 1⟩], false⟩

def reserved01 : Case :=
  ⟨[⟨⟨0, 32⟩, 2 ^ 32, 2 ^ 32, 2 ^ 33 - 1⟩,
    ⟨⟨32, 30⟩, 0, 0, 2 ^ 30 - 1⟩], true⟩

def reserved1 : Case :=
  ⟨[⟨⟨0, 32⟩, 2 ^ 33, 2 ^ 33, 2 ^ 33 + 2 ^ 32 - 1⟩,
    ⟨⟨32, 31⟩, 0, 0, 2 ^ 31 - 1⟩], true⟩

def frameIdentity : Code :=
  ⟨64, .node (.node (.leaf liveCase) (.leaf reserved01)) (.leaf reserved1)⟩

theorem wellFormed : frameIdentity.wellFormed = true := by decide
theorem fits64 : LayoutLowering.allFit64 frameIdentity = true := by decide
theorem facts : frameIdentity.Facts := Code.facts_of_wellFormed wellFormed

structure Parts where
  handle : Nat
  generation : Nat
  deriving DecidableEq, Repr

def Valid (parts : Parts) : Prop :=
  1 ≤ parts.handle ∧ parts.handle < 2 ^ 32 ∧ 1 ≤ parts.generation ∧ parts.generation < 2 ^ 30

instance (parts : Parts) : Decidable (Valid parts) := by unfold Valid; infer_instance

def Issuable (parts : Parts) : Prop := Valid parts ∧ parts.handle < 2 ^ 32 - 1

instance (parts : Parts) : Decidable (Issuable parts) := by unfold Issuable; infer_instance

def encode? (parts : Parts) : Option (BitVec 64) :=
  (frameIdentity.encode [parts.handle, parts.generation]).map (BitVec.ofNat 64)

def decode? (word : BitVec 64) : Option Parts := do
  match ← frameIdentity.decode word.toNat with
  | [handle, generation] => some ⟨handle, generation⟩
  | _ => none

def nativeParts? (word : BitVec 64) : Option Parts := do
  let parts ← decode? word
  if parts.handle < 2 ^ 32 - 1 then some parts else none

theorem live_admits (parts : Parts) :
    liveCase.admits [parts.handle, parts.generation] = decide (Valid parts) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [liveCase, Case.admits, within, Bool.not_false, Bool.true_and, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq]
  unfold Valid
  omega

theorem leaves : frameIdentity.trie.leaves = [(liveCase, 0, 2), (reserved01, 1, 2), (reserved1, 1, 1)] := rfl

theorem choose_exact (parts : Parts) :
    frameIdentity.choose [parts.handle, parts.generation] =
      if Valid parts then some (liveCase, 0, 2) else none := by
  have firstReserved : reserved01.admits [parts.handle, parts.generation] = false := rfl
  have secondReserved : reserved1.admits [parts.handle, parts.generation] = false := rfl
  simp only [Code.choose, leaves, List.find?_cons, live_admits, firstReserved, secondReserved,
    List.find?_nil]
  by_cases valid : Valid parts <;> simp [valid]

theorem live_pack (parts : Parts) (valid : Valid parts) :
    pack (slotsOf liveCase.places) (storePlaces liveCase.places [parts.handle, parts.generation]) 0 =
      parts.handle + 2 ^ 32 * parts.generation := by
  have handleBound := valid.2.1
  have generationBound := valid.2.2.2
  simp only [liveCase, slotsOf, List.map, storePlaces, Nat.sub_zero, pack,
    Mettapedia.GSLT.LanguageDef.LayoutAlgebra.set]
  simp only [Nat.zero_add, Nat.zero_div, Nat.mul_zero, Nat.zero_mod, Nat.pow_zero,
    Nat.mod_eq_of_lt handleBound, Nat.mod_eq_of_lt generationBound, Nat.one_mul, Nat.add_zero]
  have small : parts.handle < 2 ^ 62 := by omega
  rw [Nat.div_eq_of_lt small]
  omega

theorem encode_nat_exact (parts : Parts) :
    frameIdentity.encode [parts.handle, parts.generation] =
      if Valid parts then some (parts.handle + 2 ^ 32 * parts.generation) else none := by
  unfold Code.encode
  rw [choose_exact]
  split
  next valid => simp only [Option.map_some, Nat.zero_mul, Nat.zero_add, live_pack parts valid]
  next _ => rfl

theorem encoding_bound (parts : Parts) (valid : Valid parts) :
    parts.handle + 2 ^ 32 * parts.generation < 2 ^ 62 := by
  unfold Valid at valid
  omega

theorem encode_exact (parts : Parts) :
    encode? parts = if Valid parts then some (BitVec.ofNat 64 (parts.handle + 2 ^ 32 * parts.generation)) else none := by
  simp only [encode?, encode_nat_exact]
  split <;> rfl

theorem encoded_toNat (parts : Parts) (word : BitVec 64) (encoded : encode? parts = some word) :
    Valid parts ∧ word.toNat = parts.handle + 2 ^ 32 * parts.generation ∧ word.toNat < 2 ^ 62 := by
  rw [encode_exact] at encoded
  split at encoded
  next valid =>
    cases Option.some.inj encoded
    have bound := encoding_bound parts valid
    have exactWord : (BitVec.ofNat 64 (parts.handle + 2 ^ 32 * parts.generation)).toNat =
        parts.handle + 2 ^ 32 * parts.generation := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨valid, exactWord, by rw [exactWord]; exact bound⟩
  next _ => contradiction

theorem decode_encode (parts : Parts) (word : BitVec 64) (encoded : encode? parts = some word) :
    decode? word = some parts := by
  have details := encoded_toNat parts word encoded
  have source : frameIdentity.encode [parts.handle, parts.generation] = some word.toNat := by
    rw [encode_nat_exact, if_pos details.1, details.2.1]
  have returned := Code.decode_encode facts source
  simp [decode?, returned]

theorem encode_injective {left right : Parts} {word : BitVec 64}
    (first : encode? left = some word) (second : encode? right = some word) : left = right := by
  have decodedFirst := decode_encode left word first
  have decodedSecond := decode_encode right word second
  exact Option.some.inj (decodedFirst.symm.trans decodedSecond)

theorem locate_live (word : Nat) (bound : word < 2 ^ 62) :
    frameIdentity.trie.locate 64 word = (liveCase, 0, 2) := by
  have high : word / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
  have low : word / 2 ^ 62 = 0 := Nat.div_eq_of_lt bound
  simp only [frameIdentity, Trie.locate, Nat.reduceSub, high, low, if_true,
    Nat.mod_eq_of_lt (show word < 2 ^ 63 by omega), Nat.zero_add, Nat.reduceAdd]

theorem parts_live (word : Nat) (bound : word < 2 ^ 62) :
    frameIdentity.parts word = [word % 2 ^ 32, word / 2 ^ 32] := by
  have generationBound : word / 2 ^ 32 < 2 ^ 30 := by omega
  simp only [Code.parts, show frameIdentity.width = 64 from rfl, locate_live word bound,
    liveCase, readPlaces, List.map_cons, List.map_nil, Nat.reduceSub,
    Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get, Nat.mod_eq_of_lt bound, Nat.pow_zero, Nat.div_one,
    Nat.add_zero, Nat.mod_eq_of_lt generationBound]

theorem reserved_case (word : Nat) (reserved : 2 ^ 62 ≤ word) :
    (frameIdentity.trie.locate 64 word).1.reserved = true := by
  by_cases bound : word < 2 ^ 63
  · have high : word / 2 ^ 63 = 0 := Nat.div_eq_of_lt bound
    have low : ¬word / 2 ^ 62 = 0 := by omega
    simp only [frameIdentity, Trie.locate, Nat.reduceSub, high, if_true,
      Nat.mod_eq_of_lt bound, low, if_false, reserved01]
  · have high : ¬word / 2 ^ 63 = 0 := by omega
    simp only [frameIdentity, Trie.locate, Nat.reduceSub, high, if_false, reserved1]

theorem decode_nat_exact (word : Nat) :
    frameIdentity.decode word =
      if word < 2 ^ 62 ∧ 0 < word % 2 ^ 32 ∧ 0 < word / 2 ^ 32
      then some [word % 2 ^ 32, word / 2 ^ 32] else none := by
  by_cases bound : word < 2 ^ 62
  · have wide : word < 2 ^ 64 := by omega
    have generationBound : word / 2 ^ 32 < 2 ^ 30 := by omega
    have handleBound := Nat.mod_lt word (by decide : 0 < 2 ^ 32)
    have test : Valid ⟨word % 2 ^ 32, word / 2 ^ 32⟩ ↔ 0 < word % 2 ^ 32 ∧ 0 < word / 2 ^ 32 := by
      change (1 ≤ word % 2 ^ 32 ∧ word % 2 ^ 32 < 2 ^ 32 ∧
        1 ≤ word / 2 ^ 32 ∧ word / 2 ^ 32 < 2 ^ 30) ↔ _
      omega
    simp only [Code.decode, show frameIdentity.width = 64 from rfl, wide, decide_true,
      Bool.true_and, locate_live word bound, parts_live word bound,
      live_admits ⟨word % 2 ^ 32, word / 2 ^ 32⟩, decide_eq_true_eq, test, bound, true_and]
  · have reserved := reserved_case word (by omega)
    simp only [Code.decode, show frameIdentity.width = 64 from rfl, Case.admits, reserved,
      Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false, bound, false_and]

theorem decode_exact (word : BitVec 64) :
    decode? word =
      if word.toNat < 2 ^ 62 ∧ 0 < word.toNat % 2 ^ 32 ∧ 0 < word.toNat / 2 ^ 32
      then some ⟨word.toNat % 2 ^ 32, word.toNat / 2 ^ 32⟩ else none := by
  simp only [decode?, decode_nat_exact]
  split <;> rfl

theorem encode_decode (word : BitVec 64) (parts : Parts) (decoded : decode? word = some parts) :
    encode? parts = some word := by
  rw [decode_exact] at decoded
  split at decoded
  next admitted =>
    cases Option.some.inj decoded
    have source : frameIdentity.decode word.toNat = some [word.toNat % 2 ^ 32, word.toNat / 2 ^ 32] := by
      rw [decode_nat_exact, if_pos admitted]
    have encoded := Code.encode_decode facts source
    change (frameIdentity.encode [word.toNat % 2 ^ 32, word.toNat / 2 ^ 32]).map (BitVec.ofNat 64) = some word
    rw [encoded]
    simp
  next _ => contradiction

theorem native_decode_encode (parts : Parts) (word : BitVec 64) (issued : Issuable parts)
    (encoded : encode? parts = some word) : nativeParts? word = some parts := by
  simp [nativeParts?, decode_encode parts word encoded]
  exact issued.2

theorem decoded_valid (word : BitVec 64) (parts : Parts) (decoded : decode? word = some parts) : Valid parts :=
  (encoded_toNat parts word (encode_decode word parts decoded)).1

theorem reserved_rejected (word : BitVec 64) (reserved : 2 ^ 62 ≤ word.toNat) : decode? word = none := by
  rw [decode_exact, if_neg (by omega)]

theorem zero_handle_rejected (word : BitVec 64) (zero : word.toNat % 2 ^ 32 = 0) : decode? word = none := by
  rw [decode_exact, if_neg (by omega)]

theorem zero_generation_rejected (word : BitVec 64) (zero : word.toNat / 2 ^ 32 = 0) : decode? word = none := by
  rw [decode_exact, if_neg (by omega)]

theorem invalid_not_wrapped (parts : Parts) (invalid : ¬Valid parts) : encode? parts = none := by
  rw [encode_exact, if_neg invalid]

theorem arity : ∀ leaf ∈ frameIdentity.trie.leaves, leaf.1.places.length = 2 := by
  intro leaf member
  rw [leaves] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rfl
  · rfl
  · rfl

/-- The existing generated unsigned accessor semantics, interpreted by
standard BitVec operations, computes the declared total field reading. -/
theorem generated_part (word : BitVec 64) (index : Nat) :
    (LayoutBitVec.evalBV [word] (LayoutLowering.partExpr 64 index frameIdentity.trie 0)).map BitVec.toNat =
      some ((frameIdentity.parts word.toNat).getD index 0) := by
  have interpreted := LayoutBitVec.eval_toNat [word] (LayoutLowering.partExpr 64 index frameIdentity.trie 0)
  have lowered := LayoutLowering.eval_parts facts fits64 index word.isLt
  exact interpreted.symm.trans lowered

theorem generated_validity (word : BitVec 64) :
    (LayoutBitVec.evalBV [word] (LayoutLowering.validExpr 64 frameIdentity.trie 0)).map BitVec.toNat =
      some (if (frameIdentity.decode word.toNat).isSome then 1 else 0) := by
  have interpreted := LayoutBitVec.eval_toNat [word] (LayoutLowering.validExpr 64 frameIdentity.trie 0)
  have lowered := LayoutLowering.eval_valid_code facts fits64 word.isLt
  exact interpreted.symm.trans lowered

theorem generated_encoder (handle generation : BitVec 64) :
    (LayoutBitVec.evalBV [handle, generation] (LayoutLowering.encodeExpr 64 frameIdentity.trie.leaves)).map BitVec.toNat =
      some ((frameIdentity.encode [handle.toNat, generation.toNat]).getD 0) ∧
    (LayoutBitVec.evalBV [handle, generation] (LayoutLowering.admitsAnyExpr frameIdentity.trie.leaves)).map BitVec.toNat =
      some (if (frameIdentity.encode [handle.toNat, generation.toNat]).isSome then 1 else 0) := by
  have operands : ∀ value ∈ [handle.toNat, generation.toNat], value < LayoutLowering.top := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact handle.isLt
    · exact generation.isLt
  have lowered := LayoutLowering.eval_encode facts fits64 operands (by simpa only [List.length_cons, List.length_nil] using arity)
  constructor
  · exact (LayoutBitVec.eval_toNat [handle, generation] _).symm.trans lowered.1
  · exact (LayoutBitVec.eval_toNat [handle, generation] _).symm.trans lowered.2

/-- For admitted words, the generated accessors agree with the native hot
readers: low 32 bits and the following 30 bits, without truncating an epoch. -/
theorem generated_admitted_parts (parts : Parts) (word : BitVec 64) (encoded : encode? parts = some word) :
    (LayoutBitVec.evalBV [word] (LayoutLowering.partExpr 64 0 frameIdentity.trie 0)).map BitVec.toNat = some parts.handle ∧
    (LayoutBitVec.evalBV [word] (LayoutLowering.partExpr 64 1 frameIdentity.trie 0)).map BitVec.toNat = some parts.generation := by
  have details := encoded_toNat parts word encoded
  have source : frameIdentity.encode [parts.handle, parts.generation] = some word.toNat := by
    rw [encode_nat_exact, if_pos details.1, details.2.1]
  have read := Code.decode_parts (Code.decode_encode facts source)
  constructor
  · simpa only [read, List.getD_cons_zero] using generated_part word 0
  · simpa only [read, List.getD_cons_succ, List.getD_cons_zero] using generated_part word 1

theorem native_hot_fields (parts : Parts) (word : BitVec 64) (encoded : encode? parts = some word) :
    Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get word.toNat 0 32 = parts.handle ∧
    Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get word.toNat 32 30 = parts.generation := by
  have details := encoded_toNat parts word encoded
  have source : frameIdentity.encode [parts.handle, parts.generation] = some word.toNat := by
    rw [encode_nat_exact, if_pos details.1, details.2.1]
  have read := Code.decode_parts (Code.decode_encode facts source)
  rw [parts_live word.toNat details.2.2] at read
  simp only [List.cons.injEq, and_true] at read
  constructor
  · simpa only [Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get, Nat.pow_zero, Nat.div_one] using read.1
  · simp only [Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get, read.2, Nat.mod_eq_of_lt details.1.2.2.2]

def encodeVariable (base : BitVec 64) (frame : Parts) : Option VariableId :=
  (encode? frame).map fun epoch => ⟨base, epoch⟩

theorem variable_components (base : BitVec 64) (frame : Parts) (value : VariableId)
    (encoded : encodeVariable base frame = some value) :
    value.base = base ∧ decode? value.epoch = some frame := by
  obtain ⟨epoch, encodedFrame, same⟩ := Option.map_eq_some_iff.mp encoded
  cases same
  exact ⟨rfl, decode_encode frame epoch encodedFrame⟩

theorem variable_encoding_injective (leftBase rightBase : BitVec 64) (leftFrame rightFrame : Parts)
    (value : VariableId) (left : encodeVariable leftBase leftFrame = some value)
    (right : encodeVariable rightBase rightFrame = some value) :
    leftBase = rightBase ∧ leftFrame = rightFrame := by
  have first := variable_components leftBase leftFrame value left
  have second := variable_components rightBase rightFrame value right
  exact ⟨first.1.symm.trans second.1, Option.some.inj (first.2.symm.trans second.2)⟩

theorem distinct_frames_qualify_apart (leftFrame rightFrame : Parts) (leftWord rightWord : BitVec 64)
    (left : encode? leftFrame = some leftWord) (right : encode? rightFrame = some rightWord)
    (different : leftFrame ≠ rightFrame) (first second : VariableId) :
    CeTTaVariableFreshening.qualify leftWord first ≠ CeTTaVariableFreshening.qualify rightWord second := by
  intro equal
  have words := congrArg VariableId.epoch equal
  change leftWord = rightWord at words
  apply different (encode_injective left ?_)
  rw [words]
  exact right

namespace Controls

theorem first_identity_uses_high_word : encode? ⟨1, 1⟩ = some 4294967297 := by decide
theorem last_layout_identity_roundtrips :
    encode? ⟨2 ^ 32 - 1, 2 ^ 30 - 1⟩ = some (BitVec.ofNat 64 (2 ^ 62 - 1)) ∧
    decode? (BitVec.ofNat 64 (2 ^ 62 - 1)) = some ⟨2 ^ 32 - 1, 2 ^ 30 - 1⟩ := by decide
theorem last_handle_is_layout_valid_but_not_issued :
    decode? (BitVec.ofNat 64 (2 ^ 62 - 1)) = some ⟨2 ^ 32 - 1, 2 ^ 30 - 1⟩ ∧
    nativeParts? (BitVec.ofNat 64 (2 ^ 62 - 1)) = none := by decide
theorem last_issued_identity_roundtrips :
    nativeParts? (BitVec.ofNat 64 (2 ^ 62 - 2)) = some ⟨2 ^ 32 - 2, 2 ^ 30 - 1⟩ := by decide
theorem zero_and_reserved_rejected :
    decode? 0 = none ∧ decode? 4294967296 = none ∧ decode? 1 = none ∧
    decode? (BitVec.ofNat 64 (2 ^ 62 + 4294967297)) = none ∧
    decode? (BitVec.ofNat 64 (2 ^ 63 + 4294967297)) = none := by decide
theorem oversized_fields_do_not_wrap :
    encode? ⟨2 ^ 32 + 1, 1⟩ = none ∧ encode? ⟨1, 2 ^ 30 + 1⟩ = none := by decide
theorem variable_base_keeps_all_64_bits :
    encodeVariable 1 ⟨1, 1⟩ ≠ encodeVariable (BitVec.ofNat 64 (2 ^ 32 + 1)) ⟨1, 1⟩ := by decide

end Controls

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec
