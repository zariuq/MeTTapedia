import Mathlib.Tactic

/-!
# Strict UTF-16 scalar arithmetic and explicit byte order

The unit encoder and decoder are independent algorithms. `Represents` states
the positional specification, rather than defining correctness by execution.
The laws cover supplementary-plane arithmetic, invalid input and byte order.
They do not assert native pointer safety or the correctness of a C lowering.
NUL and U+FEFF are data; stream BOM policy is deliberately not part of a codec.
-/

set_option autoImplicit false

namespace Mettapedia.Data.String.Utf16

abbrev IsScalar (value : Nat) : Prop :=
  value < 1114112 ∧ (value < 55296 ∨ 57343 < value)

def encode (scalar : Nat) : Option (List Nat) :=
  if IsScalar scalar then
    if scalar < 65536 then some [scalar]
    else some [55296 + (scalar - 65536) / 1024, 56320 + (scalar - 65536) % 1024]
  else none

/-- Decode one scalar from available code units; the width is in units. -/
def decode (first second available : Nat) : Option (Nat × Nat) :=
  if available = 0 ∨ 65535 < first then none
  else if first < 55296 ∨ 57343 < first then some (first, 1)
  else if available < 2 ∨ 56319 < first ∨ second < 56320 ∨ 57343 < second then none
  else some (65536 + (first - 55296) * 1024 + (second - 56320), 2)

/-- The positional meaning of a UTF-16 sequence of one or two code units. -/
inductive Represents : Nat → List Nat → Prop
  | bmp {scalar : Nat} (valid : IsScalar scalar) (small : scalar < 65536) :
      Represents scalar [scalar]
  | pair {scalar high low : Nat}
      (highLower : 55296 ≤ high) (highUpper : high < 56320)
      (lowLower : 56320 ≤ low) (lowUpper : low < 57344)
      (position : scalar = 65536 + (high - 55296) * 1024 + (low - 56320)) :
      Represents scalar [high, low]

theorem Represents.scalar {scalar : Nat} {units : List Nat}
    (represented : Represents scalar units) : IsScalar scalar := by
  cases represented with
  | bmp valid _ => exact valid
  | pair highLower highUpper lowLower lowUpper position =>
    subst scalar
    constructor <;> omega

theorem Represents.units_bounded {scalar : Nat} {units : List Nat}
    (represented : Represents scalar units) : ∀ unit ∈ units, unit < 65536 := by
  cases represented with
  | bmp _ small => simpa using small
  | pair _ highUpper _ lowUpper _ => simp; omega

theorem encode_represents {scalar : Nat} {units : List Nat}
    (encoded : encode scalar = some units) : Represents scalar units := by
  unfold encode at encoded
  split_ifs at encoded with valid small
  · cases encoded
    exact .bmp valid small
  · cases encoded
    have lower : 65536 ≤ scalar := by omega
    have quotient : (scalar - 65536) / 1024 < 1024 := by omega
    have remainder := Nat.mod_lt (scalar - 65536) (by decide : 0 < 1024)
    have positional := Nat.mod_add_div (scalar - 65536) 1024
    apply Represents.pair <;> omega

theorem decode_represents {first second available scalar width : Nat}
    (decoded : decode first second available = some (scalar, width)) :
    (width = 1 ∧ Represents scalar [first]) ∨
      (width = 2 ∧ Represents scalar [first, second]) := by
  unfold decode at decoded
  by_cases invalid : available = 0 ∨ 65535 < first
  · simp only [if_pos invalid] at decoded
    cases decoded
  simp only [if_neg invalid] at decoded
  by_cases single : first < 55296 ∨ 57343 < first
  · simp only [if_pos single, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    have valid : IsScalar first := ⟨by omega, single⟩
    exact Or.inl ⟨rfl, Represents.bmp valid (by omega)⟩
  simp only [if_neg single] at decoded
  by_cases invalidPair : available < 2 ∨ 56319 < first ∨ second < 56320 ∨ 57343 < second
  · simp only [if_pos invalidPair] at decoded
    cases decoded
  simp only [if_neg invalidPair, Option.some.injEq, Prod.mk.injEq] at decoded
  obtain ⟨rfl, rfl⟩ := decoded
  exact Or.inr ⟨rfl, Represents.pair (by omega) (by omega) (by omega) (by omega) rfl⟩

theorem decode_scalar {first second available scalar width : Nat}
    (decoded : decode first second available = some (scalar, width)) : IsScalar scalar := by
  rcases decode_represents decoded with ⟨_, represented⟩ | ⟨_, represented⟩ <;>
    exact represented.scalar

theorem Represents.decode_units {scalar first second : Nat}
    (represented : Represents scalar [first, second]) :
    decode first second 2 = some (scalar, 2) := by
  cases represented with
  | pair highLower highUpper lowLower lowUpper position =>
    subst scalar
    have available : ¬(2 = 0 ∨ 65535 < first) := by omega
    have single : ¬(first < 55296 ∨ 57343 < first) := by omega
    have pair : ¬(2 < 2 ∨ 56319 < first ∨ second < 56320 ∨ 57343 < second) := by omega
    simp only [decode, if_neg available, if_neg single, if_neg pair]

theorem encode_decode_bmp {scalar : Nat} (valid : IsScalar scalar) (small : scalar < 65536)
    (second : Nat) :
    encode scalar = some [scalar] ∧ decode scalar second 1 = some (scalar, 1) := by
  constructor
  · simp [encode, valid, small]
  · simp [decode, show ¬(65535 < scalar) by omega, valid.2]

theorem encode_decode_pair {scalar : Nat} (valid : IsScalar scalar) (large : 65536 ≤ scalar) :
    decode (55296 + (scalar - 65536) / 1024)
      (56320 + (scalar - 65536) % 1024) 2 = some (scalar, 2) := by
  apply Represents.decode_units
  apply encode_represents
  simp [encode, valid, show ¬(scalar < 65536) by omega]

theorem encode_exists_iff (scalar : Nat) : (∃ units, encode scalar = some units) ↔ IsScalar scalar := by
  constructor
  · rintro ⟨units, encoded⟩
    exact (encode_represents encoded).scalar
  · intro valid
    by_cases small : scalar < 65536
    · exact ⟨[scalar], by simp [encode, valid, small]⟩
    · exact ⟨[55296 + (scalar - 65536) / 1024, 56320 + (scalar - 65536) % 1024],
        by simp [encode, valid, small]⟩

theorem encode_injective {left right : Nat} {units : List Nat}
    (hl : encode left = some units) (hr : encode right = some units) : left = right := by
  have l := encode_represents hl
  have r := encode_represents hr
  cases l <;> cases r <;> omega

theorem empty_rejected (first second : Nat) : decode first second 0 = none := by
  simp [decode]

theorem lone_surrogate_rejected (first second : Nat)
    (lower : 55296 ≤ first) (upper : first < 57344) : decode first second 1 = none := by
  simp [decode, show ¬(65535 < first) by omega,
    show ¬(first < 55296 ∨ 57343 < first) by omega]

theorem reversed_pair_rejected (low high available : Nat)
    (lower : 56320 ≤ low) (upper : low < 57344) : decode low high available = none := by
  unfold decode
  split_ifs <;> first | omega | rfl

/-- Explicitly ordered bytes of a 16-bit unit. -/
def encodeLE (unit : Nat) : Nat × Nat := (unit % 256, unit / 256)
def encodeBE (unit : Nat) : Nat × Nat := (unit / 256, unit % 256)
def decodeLE (bytes : Nat × Nat) : Nat := bytes.1 + 256 * bytes.2
def decodeBE (bytes : Nat × Nat) : Nat := 256 * bytes.1 + bytes.2

theorem decodeLE_encodeLE (unit : Nat) : decodeLE (encodeLE unit) = unit := by
  simpa [decodeLE, encodeLE, Nat.mul_comm] using Nat.mod_add_div unit 256

theorem decodeBE_encodeBE (unit : Nat) : decodeBE (encodeBE unit) = unit := by
  have decomposition := Nat.mod_add_div unit 256
  simp only [decodeBE, encodeBE]
  omega

theorem encoded_bytes_bounded (unit : Nat) (bounded : unit < 65536) :
    (encodeLE unit).1 < 256 ∧ (encodeLE unit).2 < 256 ∧
      (encodeBE unit).1 < 256 ∧ (encodeBE unit).2 < 256 := by
  have low := Nat.mod_lt unit (by decide : 0 < 256)
  simp only [encodeLE, encodeBE]
  omega

theorem endian_swap (unit : Nat) : encodeBE unit = (encodeLE unit).swap := rfl

example : encode 0 = some [0] := by decide +kernel
example : decode 0 65 1 = some (0, 1) := by decide +kernel
example : encode 65279 = some [65279] := by decide +kernel
example : decode 65279 65 1 = some (65279, 1) := by decide +kernel
example : encode 128512 = some [55357, 56832] := by decide +kernel
example : decode 55357 56832 2 = some (128512, 2) := by decide +kernel
example : decode 55357 56832 1 = none := by decide +kernel
example : decode 56832 55357 2 = none := by decide +kernel
example : decode 55357 65 2 = none := by decide +kernel
example : encode 55296 = none := by decide +kernel
example : encode 1114112 = none := by decide +kernel
example : encodeLE 55357 = (61, 216) := by decide +kernel
example : encodeBE 55357 = (216, 61) := by decide +kernel

#print axioms Represents.scalar
#print axioms Represents.units_bounded
#print axioms encode_represents
#print axioms decode_represents
#print axioms decode_scalar
#print axioms Represents.decode_units
#print axioms encode_decode_bmp
#print axioms encode_decode_pair
#print axioms encode_exists_iff
#print axioms encode_injective
#print axioms empty_rejected
#print axioms lone_surrogate_rejected
#print axioms reversed_pair_rejected
#print axioms decodeLE_encodeLE
#print axioms decodeBE_encodeBE
#print axioms encoded_bytes_bounded
#print axioms endian_swap

end Mettapedia.Data.String.Utf16
