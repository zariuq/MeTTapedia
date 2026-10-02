import Mettapedia.GSLT.LanguageDef.NativeWord64
import Mettapedia.Languages.VibeITP.Native.Word64Bridge
import Mettapedia.Languages.VibeITP.Spec.Execution
import Init.Data.BitVec.Bitblast

/-!
Unsigned OR/shift accumulation in the authored JIT length guard versus the
independent natural decoder. Scope-owned execution observations, term-record
reads and the complete function-call bridge are separate interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.JITGuards

open Spec
open Mettapedia.GSLT.LanguageDef

def byteWord (byte : UInt8) : BitVec 64 := NativeWord64.targetToWord byte.toBitVec

theorem byte_word_value (byte : UInt8) : (byteWord byte).toNat = byte.toNat := by
  simp only [byteWord, NativeWord64.targetToWord, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans byte.toNat_lt (by decide +kernel))

def bytePrefix : List UInt8 → BitVec 64
  | [] => 0
  | byte :: rest => byteWord byte ||| (bytePrefix rest <<< (8 : Nat))

def loop : Nat → BitVec 64 → List UInt8 → BitVec 64
  | _, accumulator, [] => accumulator
  | index, accumulator, byte :: rest =>
      loop (index + 1) (accumulator ||| (byteWord byte <<< (index * 8))) rest

theorem loop_as_bytePrefix (bytes : List UInt8) (index : Nat) (accumulator : BitVec 64) :
    loop index accumulator bytes = accumulator ||| (bytePrefix bytes <<< (index * 8)) := by
  induction bytes generalizing index accumulator with
  | nil => simp [loop, bytePrefix]
  | cons byte rest ih =>
    rw [loop, ih, bytePrefix, BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, BitVec.or_assoc]
    rw [show 8 + index * 8 = (index + 1) * 8 by omega]

theorem byte_or_shift (byte : UInt8) (value : Nat) :
    byte.toNat ||| (value <<< 8) = byte.toNat + 256 * value := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt byte.toNat_lt value, Nat.shiftLeft_eq]
  change value * 256 + byte.toNat = byte.toNat + 256 * value
  omega

theorem bytePrefix_value_mod (bytes : List UInt8) :
    (bytePrefix bytes).toNat = executionLittleEndian bytes % wordBound := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [bytePrefix, BitVec.toNat_or, BitVec.toNat_shiftLeft, byte_word_value, ih]
    have byteBound : byte.toNat < 2 ^ 64 := Nat.lt_trans byte.toNat_lt (by decide +kernel)
    change byte.toNat ||| (((executionLittleEndian rest % 2 ^ 64) <<< 8) % 2 ^ 64) =
      (byte.toNat + 256 * executionLittleEndian rest) % 2 ^ 64
    calc
      _ = (byte.toNat % 2 ^ 64) |||
          (((executionLittleEndian rest % 2 ^ 64) <<< 8) % 2 ^ 64) := by
        rw [Nat.mod_eq_of_lt byteBound]
      _ = (byte.toNat ||| ((executionLittleEndian rest % 2 ^ 64) <<< 8)) % 2 ^ 64 :=
        Nat.or_mod_two_pow.symm
      _ = (byte.toNat ||| (executionLittleEndian rest <<< 8)) % 2 ^ 64 := by
        rw [Nat.or_mod_two_pow, Nat.mod_two_pow_shiftLeft_mod_two_pow, ← Nat.or_mod_two_pow]
      _ = _ := by rw [byte_or_shift]

theorem little_endian_bound (bytes : List UInt8) :
    executionLittleEndian bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => exact Nat.zero_lt_one
  | cons byte rest ih =>
    have bounded := byte.toNat_lt
    simp only [executionLittleEndian, List.length_cons, Nat.pow_succ]
    omega

theorem eight_or_fewer_bound (bytes : List UInt8) (length : bytes.length ≤ 8) :
    executionLittleEndian bytes < wordBound := by
  have exponent : 256 ^ bytes.length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide +kernel) length
  exact Nat.lt_of_lt_of_le (little_endian_bound bytes) exponent

theorem loop_value (bytes : List UInt8) (length : bytes.length ≤ 8) :
    (loop 0 0 bytes).toNat = executionLittleEndian bytes := by
  rw [loop_as_bytePrefix]
  simp only [Nat.zero_mul, BitVec.shiftLeft_zero]
  change (0#64 ||| bytePrefix bytes).toNat = executionLittleEndian bytes
  rw [BitVec.zero_or, bytePrefix_value_mod, Nat.mod_eq_of_lt (eight_or_fewer_bound bytes length)]

theorem authored_shift_bound (index : Nat) (inside : index < 8) : index * 8 < 64 := by omega

theorem authored_shift_defined (byte : UInt8) (index : Nat) (inside : index < 8) :
    NativeWord64.targetBinary .shl (byteWord byte) (BitVec.ofNat 64 (index * 8)) =
      .ok (byteWord byte <<< (index * 8)) := by
  have shift := authored_shift_bound index inside
  have word : index * 8 < 2 ^ 64 := Nat.lt_trans shift (by decide +kernel)
  simp only [NativeWord64.targetBinary, BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt word]
  simp only [show (64 : BitVec 64).toNat = 64 from rfl, Nat.not_le.mpr shift, if_false]

def outputLength? (bytes : List UInt8) : Option (BitVec 64) :=
  if bytes.length = 1 then some (byteWord (bytes.getD 0 0))
  else if bytes.length = 8 then
    let value := loop 0 0 bytes
    if value < (256 : BitVec 64) then some value else none
  else none

theorem output_length_correspondence (bytes : List UInt8) :
    (outputLength? bytes).map BitVec.toNat = executionOutputLength? bytes := by
  by_cases one : bytes.length = 1
  · obtain ⟨byte, equal⟩ := List.length_eq_one_iff.mp one
    subst bytes
    simp only [outputLength?, List.length_singleton, if_true, List.getD_cons_zero,
      Option.map_some, byte_word_value, executionOutputLength_one]
  · by_cases eight : bytes.length = 8
    · unfold outputLength?
      rw [if_neg one, if_pos eight]
      rw [executionOutputLength_eight bytes eight]
      have decoded := loop_value bytes (Nat.le_of_eq eight)
      simp only [BitVec.lt_def, show (256 : BitVec 64).toNat = 256 from rfl, decoded]
      split
      · simp only [Option.map_some, decoded]
      · rfl
    · unfold outputLength?
      rw [if_neg one, if_neg eight]
      cases bytes with
      | nil => rfl
      | cons byte rest =>
        cases rest with
        | nil => simp at one
        | cons next rest =>
          change none = if (byte :: next :: rest).length = 8 then
            (if executionLittleEndian (byte :: next :: rest) < 256 then
              some (executionLittleEndian (byte :: next :: rest)) else none) else none
          rw [if_neg eight]

theorem accepted_length_value_bound (bytes : List UInt8) (value : BitVec 64)
    (accepted : outputLength? bytes = some value) : value.toNat < 256 := by
  have decoded : executionOutputLength? bytes = some value.toNat := by
    rw [← output_length_correspondence, accepted]
    rfl
  exact executionOutputLength_bound decoded

theorem accepted_length_shape (bytes : List UInt8) (value : BitVec 64)
    (accepted : outputLength? bytes = some value) : bytes.length = 1 ∨ bytes.length = 8 := by
  have decoded : executionOutputLength? bytes = some value.toNat := by
    rw [← output_length_correspondence, accepted]
    rfl
  exact executionOutputLength_shape decoded

theorem accepted_allocation_guard (bytes : List UInt8) (value : BitVec 64)
    (accepted : outputLength? bytes = some value) : ¬ value + 8 < value := by
  have bounded := accepted_length_value_bound bytes value accepted
  have noWrap : value.toNat + 8 < 2 ^ 64 := by omega
  rw [BitVec.lt_def, BitVec.toNat_add]
  simp only [show (8 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt noWrap]
  omega

theorem output_length_refusal_iff (bytes : List UInt8) :
    outputLength? bytes = none ↔ executionOutputLength? bytes = none := by
  rw [← output_length_correspondence]
  cases outputLength? bytes <;> simp

theorem one_byte_accepts_255 : (outputLength? [255]).map BitVec.toNat = some 255 := by
  rw [output_length_correspondence]
  rfl

theorem eight_byte_nonshortest_accepts :
    (outputLength? [7, 0, 0, 0, 0, 0, 0, 0]).map BitVec.toNat = some 7 := by
  rw [output_length_correspondence]
  rfl

theorem eight_byte_value_256_refuses : outputLength? [0, 1, 0, 0, 0, 0, 0, 0] = none := by
  rw [output_length_refusal_iff]
  rfl

theorem maximal_eight_byte_word_refuses : outputLength? [255, 255, 255, 255, 255, 255, 255, 255] = none := by
  rw [output_length_refusal_iff]
  rfl

theorem wrong_width_refuses : outputLength? [1, 0] = none := rfl

theorem empty_width_refuses : outputLength? [] = none := rfl

end Mettapedia.Languages.VibeITP.Native.JITGuards
