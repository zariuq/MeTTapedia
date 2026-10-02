import Mettapedia.GSLT.LanguageDef.NativeWord64
import Mettapedia.Languages.VibeITP.Spec.Kernel

/-!
# Native unsigned primitives and Vibe-ITP's literal specification

The byte loop below uses a narrowing cast and an unsigned shift by eight,
independently of the natural-number little-endian encoder.  Its theorem
identifies the bytes at both number-literal lengths.  Literal arithmetic
statements use independently evaluated bit-vector results, including wrapping
addition and multiplication and refusal of zero-divisor division.

The checked-add lemma identifies the native carry comparison with the exact
natural-word guard used for binder offsets, bound-variable depth, and literal
allocation length.  Storage allocation and complete source-function execution
are not established here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.Word64Bridge

open Mettapedia.GSLT.LanguageDef.NativeWord64
open Mettapedia.Languages.VibeITP.Spec

def nativeLittleEndian : Nat → BitVec 64 → List UInt8
  | 0, _ => []
  | count + 1, value => UInt8.ofBitVec (targetToByte value) ::
      nativeLittleEndian count (value >>> (8 : Nat))

def nativeNatLiteral (value : BitVec 64) : List UInt8 :=
  if value < (256 : BitVec 64) then [UInt8.ofBitVec (targetToByte value)]
  else nativeLittleEndian 8 value

theorem native_shift8_value (value : BitVec 64) :
    (value >>> (8 : Nat)).toNat = value.toNat / 256 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem native_shift8_not_faulting (value : BitVec 64) :
    targetBinary .shr value 8 = .ok (value >>> (8 : Nat)) := by
  simp [targetBinary, BitVec.le_def]

theorem native_byte_cast_value (value : BitVec 64) :
    (UInt8.ofBitVec (targetToByte value)).toNat = value.toNat % 256 := by
  simp [targetToByte]

theorem native_little_endian_correspondence (count : Nat) (value : BitVec 64) :
    nativeLittleEndian count value = leBytes count value.toNat := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih =>
      simp only [nativeLittleEndian, leBytes, List.cons.injEq]
      constructor
      · apply UInt8.toNat_inj.mp
        simp [targetToByte]
      · rw [ih, native_shift8_value]

/-- Includes the one-byte/eight-byte boundary and every unsigned word. -/
theorem native_number_literal_correspondence (value : BitVec 64) :
    nativeNatLiteral value = natLiteral value.toNat := by
  have hg : value < (256 : BitVec 64) ↔ value.toNat < 256 := by
    rw [BitVec.lt_def]
    simp
  simp only [nativeNatLiteral, natLiteral, hg]
  split_ifs
  · congr 1
  · exact native_little_endian_correspondence 8 value

def nativeAddStatement (a b : BitVec 64) : Term :=
  .eq (.app (.builtin .litAdd) [.lit (nativeNatLiteral a), .lit (nativeNatLiteral b)])
    (.lit (nativeNatLiteral (a + b)))

def nativeMulStatement (a b : BitVec 64) : Term :=
  .eq (.app (.builtin .litMul) [.lit (nativeNatLiteral a), .lit (nativeNatLiteral b)])
    (.lit (nativeNatLiteral (a * b)))

def nativeDivStatement (a b : BitVec 64) : Option Term :=
  if b = 0 then none else some <|
    .eq (.app (.builtin .litDiv) [.lit (nativeNatLiteral a), .lit (nativeNatLiteral b)])
      (.lit (nativeNatLiteral (a / b)))

theorem native_add_statement_correspondence (a b : Word) :
    nativeAddStatement (encode a) (encode b) = litAddStatement a.val b.val := by
  simp [nativeAddStatement, litAddStatement, Term.natLit,
    native_number_literal_correspondence, wordBound]

theorem native_mul_statement_correspondence (a b : Word) :
    nativeMulStatement (encode a) (encode b) = litMulStatement a.val b.val := by
  simp [nativeMulStatement, litMulStatement, Term.natLit,
    native_number_literal_correspondence, wordBound]

theorem native_div_statement_correspondence (a b : Word) :
    nativeDivStatement (encode a) (encode b) =
      if b.val = 0 then none else some (litDivStatement a.val b.val) := by
  simp only [nativeDivStatement, litDivStatement, Term.natLit, encode_eq_zero,
    native_number_literal_correspondence, encode_toNat, BitVec.toNat_udiv]

theorem native_div_statement_refusal_iff (a b : Word) :
    nativeDivStatement (encode a) (encode b) = none ↔ b.val = 0 := by
  rw [native_div_statement_correspondence]
  split_ifs <;> simp_all

def nativeCheckedAdd (a b : BitVec 64) : Option (BitVec 64) :=
  let result := a + b
  if result < a then none else some result

/-- The source-authored carry guard accepts exactly the nonwrapping natural sum. -/
theorem native_checked_add_correspondence (a b : Word) :
    (nativeCheckedAdd (encode a) (encode b)).map BitVec.toNat =
      if a.val + b.val < wordBound then some (a.val + b.val) else none := by
  simp only [nativeCheckedAdd, BitVec.lt_def, encode_toNat, add_carry_iff]
  by_cases h : a.val + b.val < wordBound
  · have hn : ¬2 ^ 64 ≤ a.val + b.val := by simpa [wordBound] using h
    simp only [hn, ite_false, h, ite_true, Option.map_some]
    exact congrArg some (add_no_carry_value a b (by simpa [wordBound] using h))
  · have hn : 2 ^ 64 ≤ a.val + b.val := by simpa [wordBound] using h
    simp only [hn, ite_true, h, ite_false, Option.map_none]

theorem native_bound_variable_depth_guard (index : Word) :
    (nativeCheckedAdd (encode index) 1).map BitVec.toNat =
      if index.val + 1 < wordBound then some (index.val + 1) else none := by
  exact native_checked_add_correspondence index (bounded 64 1)

theorem native_literal_length_guard (length : Word) :
    (nativeCheckedAdd (encode length) 8).map BitVec.toNat =
      if length.val + 8 < wordBound then some (length.val + 8) else none := by
  exact native_checked_add_correspondence length (bounded 64 8)

namespace Controls

theorem one_byte_boundary : nativeNatLiteral 255 = [255] := by decide +kernel

theorem eight_byte_boundary : nativeNatLiteral 256 = [0, 1, 0, 0, 0, 0, 0, 0] := by decide +kernel

theorem maximal_literal :
    nativeNatLiteral 18446744073709551615 = [255, 255, 255, 255, 255, 255, 255, 255] := by decide +kernel

theorem division_refused : nativeDivStatement 5 0 = none := by decide +kernel

theorem checked_add_last_word_accepts :
    nativeCheckedAdd 18446744073709551614 1 = some 18446744073709551615 := by decide +kernel

theorem checked_add_wrap_refuses :
    nativeCheckedAdd 18446744073709551615 1 = none := by decide +kernel

theorem last_bound_variable_depth_refuses (sig : Sig) :
    WellFormed sig (.bvar 18446744073709551615) = false ∧
      nativeCheckedAdd 18446744073709551615 1 = none := by
  constructor
  · change decide (18446744073709551615 + 1 < wordBound) = false
    decide +kernel
  · decide +kernel

theorem literal_allocation_last_length_accepts :
    nativeCheckedAdd 18446744073709551607 8 = some 18446744073709551615 := by decide +kernel

theorem literal_allocation_overflow_refuses :
    nativeCheckedAdd 18446744073709551608 8 = none := by decide +kernel

end Controls

end Mettapedia.Languages.VibeITP.Native.Word64Bridge
