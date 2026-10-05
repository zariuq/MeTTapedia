import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
import Mathlib.Data.List.Nodup

/-!
# Injective generated dispatcher names

The compiler encodes each UTF-8 byte as two hexadecimal characters. Decoding
those pairs recovers the original bytes, so no guest-specific name catalogue
or checking result is needed for loading generated programs.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

private def byteHex (byte : UInt8) : String :=
  let digits := String.ofList (Nat.toDigits 16 byte.toNat)
  if byte.toNat < 16 then "0" ++ digits else digits

private def digitValue (digit : Char) : Nat :=
  if digit.toNat < 58 then digit.toNat - 48 else digit.toNat - 87

private def pairByte (first second : Char) : UInt8 :=
  UInt8.ofNat (16 * digitValue first + digitValue second)

private def readByte (characters : List Char) : Option UInt8 :=
  match characters with
  | [first, second] => some (pairByte first second)
  | _ => none

private theorem byteHex_roundtrip (byte : UInt8) :
    (byteHex byte).toList.length = 2 ∧ readByte (byteHex byte).toList = some byte := by
  have finite : ∀ index : Fin 256,
      (byteHex (UInt8.ofNat index.val)).toList.length = 2 ∧
        readByte (byteHex (UInt8.ofNat index.val)).toList = some (UInt8.ofNat index.val) := by
    decide +kernel
  simpa only [UInt8.ofNat_toNat] using finite ⟨byte.toNat, byte.toNat_lt_size⟩

private def decodeHex : List Char → List UInt8
  | first :: second :: rest => pairByte first second :: decodeHex rest
  | _ => []

private theorem decodeHex_byte (byte : UInt8) (rest : List Char) :
    decodeHex ((byteHex byte).toList ++ rest) = byte :: decodeHex rest := by
  obtain ⟨length, decoded⟩ := byteHex_roundtrip byte
  generalize characters : (byteHex byte).toList = chars at length decoded ⊢
  cases chars with
  | nil => simp at length
  | cons first chars =>
    cases chars with
    | nil => simp at length
    | cons second chars =>
      have empty : chars = [] := by simpa using length
      subst chars
      simp only [readByte, Option.some.injEq] at decoded
      simp only [List.cons_append, List.nil_append, decodeHex, decoded]

private theorem decodeHex_all (bytes : List UInt8) :
    decodeHex ((bytes.map byteHex).flatMap String.toList) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [List.map_cons, List.flatMap_cons, decodeHex_byte, ih]

/-- The actual generated symbol encoding is injective for every source name. -/
theorem dispatchName_injective : Function.Injective dispatchName := by
  intro left right equal
  have characters := congrArg String.toList equal
  simp only [dispatchName, String.toList_append, List.append_cancel_left_eq,
    String.toList_join] at characters
  change ((left.toUTF8.data.toList.map byteHex).flatMap String.toList) =
    ((right.toUTF8.data.toList.map byteHex).flatMap String.toList) at characters
  have bytes := congrArg decodeHex characters
  rw [decodeHex_all, decodeHex_all] at bytes
  apply String.toByteArray_inj.mp
  apply ByteArray.ext_iff.mpr
  exact Array.toList_inj.mp bytes

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
