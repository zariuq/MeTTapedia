import Mettapedia.GSLT.Parsing.BinaryRecordCodec
import Mettapedia.GSLT.LanguageDef.NativeWord64

/-!
The unsigned native little-endian payload loop and its arithmetic meaning.
The target accumulates bytes with shifted bitwise OR in their actual order;
the reference decoder uses multiplication and addition. The proof covers an
arbitrary accumulator whose lower byte positions are already populated.
Native word decoding admits at most eight payload bytes, making every shift
defined and the result exactly representable without modular truncation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.NativeBinaryPayload

def arithmeticLoop : List UInt8 → Nat → Nat → Nat
  | [], _, accumulator => accumulator
  | byte :: rest, index, accumulator =>
    arithmeticLoop rest (index + 1) (accumulator ||| (byte.toNat <<< (8 * index)))

def nativeLoop : List UInt8 → Nat → BitVec 64 → BitVec 64
  | [], _, accumulator => accumulator
  | byte :: rest, index, accumulator =>
    nativeLoop rest (index + 1) (accumulator ||| (BitVec.ofNat 64 byte.toNat <<< (8 * index)))

theorem arithmetic_loop_correct (bytes : List UInt8) (index accumulator : Nat)
    (lower : accumulator < 2 ^ (8 * index)) :
    arithmeticLoop bytes index accumulator =
      accumulator + 2 ^ (8 * index) * BinaryRecordCodec.littleEndian bytes := by
  induction bytes generalizing index accumulator with
  | nil => simp only [arithmeticLoop, BinaryRecordCodec.littleEndian, Nat.mul_zero, Nat.add_zero]
  | cons byte rest ih =>
    have nextPower : 2 ^ (8 * (index + 1)) = 2 ^ (8 * index) * 256 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have byteBound : byte.toNat < 256 := byte.toNat_lt
    have assembled : accumulator ||| (byte.toNat <<< (8 * index)) =
        accumulator + 2 ^ (8 * index) * byte.toNat := by
      rw [Nat.or_comm, Nat.shiftLeft_eq, Nat.mul_comm byte.toNat]
      exact (Nat.two_pow_add_eq_or_of_lt lower byte.toNat).symm.trans (Nat.add_comm _ _)
    have nextLower : accumulator + 2 ^ (8 * index) * byte.toNat <
        2 ^ (8 * (index + 1)) := by
      rw [nextPower]
      have byteUpper : byte.toNat ≤ 255 := Nat.le_of_lt_succ byteBound
      calc
        accumulator + 2 ^ (8 * index) * byte.toNat <
            2 ^ (8 * index) + 2 ^ (8 * index) * byte.toNat := Nat.add_lt_add_right lower _
        _ ≤ 2 ^ (8 * index) + 2 ^ (8 * index) * 255 :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ byteUpper) _
        _ = 2 ^ (8 * index) * 256 := by
          rw [show 256 = 255 + 1 by rfl, Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rw [arithmeticLoop, assembled, ih (index + 1) _ nextLower,
      BinaryRecordCodec.littleEndian, nextPower]
    ring

private theorem encode_shift (value shift : Nat) :
    (BitVec.ofNat 64 value <<< shift) = BitVec.ofNat 64 (value <<< shift) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_two_pow_shiftLeft_mod_two_pow]

theorem native_loop_arithmetic (bytes : List UInt8) (index accumulator : Nat) :
    nativeLoop bytes index (BitVec.ofNat 64 accumulator) =
      BitVec.ofNat 64 (arithmeticLoop bytes index accumulator) := by
  induction bytes generalizing index accumulator with
  | nil => rfl
  | cons byte rest ih =>
    simp only [nativeLoop, arithmeticLoop, encode_shift, ← BitVec.ofNat_or]
    exact ih (index + 1) _

theorem native_loop_correct (bytes : List UInt8) :
    nativeLoop bytes 0 (BitVec.ofNat 64 0) = BitVec.ofNat 64 (BinaryRecordCodec.littleEndian bytes) := by
  have agreement := native_loop_arithmetic bytes 0 0
  rw [arithmetic_loop_correct bytes 0 0 (by decide)] at agreement
  simpa only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] using agreement

private theorem little_endian_length_bound (bytes : List UInt8) :
    BinaryRecordCodec.littleEndian bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => exact Nat.zero_lt_succ 0
  | cons byte bytes ih =>
    have byteBound : byte.toNat < 256 := byte.toNat_lt
    simp only [BinaryRecordCodec.littleEndian, List.length_cons, Nat.pow_succ]
    omega

theorem little_endian_word_bound (bytes : List UInt8) (bounded : bytes.length ≤ 8) :
    BinaryRecordCodec.littleEndian bytes < 2 ^ 64 := by
  have upper : 256 ^ bytes.length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) bounded
  have samePower : (256 : Nat) ^ 8 = 2 ^ 64 := by decide +kernel
  rw [samePower] at upper
  exact Nat.lt_of_lt_of_le (little_endian_length_bound bytes) upper

theorem native_loop_exact_value (bytes : List UInt8) (bounded : bytes.length ≤ 8) :
    (nativeLoop bytes 0 (BitVec.ofNat 64 0)).toNat = BinaryRecordCodec.littleEndian bytes := by
  rw [native_loop_correct, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (little_endian_word_bound bytes bounded)]

theorem every_native_shift_is_defined (count index : Nat) (bounded : count ≤ 8)
    (inside : index < count) : 8 * index < 64 := by omega

theorem eight_maximal_bytes_produce_the_maximal_word :
    nativeLoop [255, 255, 255, 255, 255, 255, 255, 255] 0 (BitVec.ofNat 64 0) =
      (18446744073709551615 : BitVec 64) := by decide +kernel

theorem byte_order_is_little_endian :
    nativeLoop [1, 2] 0 (BitVec.ofNat 64 0) = (513 : BitVec 64) := by decide +kernel

theorem reversed_bytes_do_not_have_the_same_value :
    nativeLoop [2, 1] 0 (BitVec.ofNat 64 0) ≠ (513 : BitVec 64) := by decide +kernel

theorem a_zero_high_byte_is_preserved :
    nativeLoop [247, 0] 0 (BitVec.ofNat 64 0) = (247 : BitVec 64) := by decide +kernel

end Mettapedia.GSLT.Parsing.NativeBinaryPayload
