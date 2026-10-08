import Mathlib.Data.List.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.String.Basic

/-!
# ASCII bytes are their own UTF-8 encoding

A byte below 128, read as a character, encodes back to that one byte.  A reader
that works on bytes can therefore name an ASCII token by a string without
changing its bytes.  The bound is necessary: every byte from 128 up encodes to
two bytes.
-/

set_option autoImplicit false

namespace Mettapedia.Data.String.Ascii

/-- The string whose characters are the given bytes. -/
def text (bytes : List UInt8) : String := String.ofList (bytes.map Char.ofUInt8)

theorem utf8Encode_singleton (byte : UInt8) (ascii : byte.toNat < 128) :
    [Char.ofUInt8 byte].utf8Encode = [byte].toByteArray := by
  have single : (Char.ofUInt8 byte).utf8Size = 1 := by
    apply Char.utf8Size_eq_one_iff.mpr
    simp only [Char.ofUInt8, UInt32.le_iff_toNat_le, UInt8.toNat_toUInt32]
    change byte.toNat ≤ 127
    omega
  rw [List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton single]
  simp [Char.ofUInt8]

theorem utf8Encode_map (bytes : List UInt8) (ascii : ∀ byte ∈ bytes, byte.toNat < 128) :
    (bytes.map Char.ofUInt8).utf8Encode = bytes.toByteArray := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      rw [List.map_cons, List.utf8Encode_cons, utf8Encode_singleton byte (ascii byte (by simp)),
        ih (fun value member => ascii value (by simp [member])), ← List.toByteArray_append]
      rfl

/-- The UTF-8 bytes of an ASCII text are the bytes it was built from. -/
theorem text_toUTF8 (bytes : List UInt8) (ascii : ∀ byte ∈ bytes, byte.toNat < 128) :
    (text bytes).toUTF8.data.toList = bytes := by
  simpa [text, String.toUTF8_eq_toByteArray] using
    congrArg (fun encoded : ByteArray => encoded.data.toList) (utf8Encode_map bytes ascii)

/-- ASCII texts are equal only when their bytes are. -/
theorem text_injective {first second : List UInt8}
    (firstAscii : ∀ byte ∈ first, byte.toNat < 128)
    (secondAscii : ∀ byte ∈ second, byte.toNat < 128)
    (same : text first = text second) : first = second := by
  rw [← text_toUTF8 first firstAscii, ← text_toUTF8 second secondAscii, same]

/-! Controls: an ASCII token keeps its bytes; the first non-ASCII byte does not. -/

example : (text [0x28, 0x61, 0x29]).toUTF8.data.toList = [0x28, 0x61, 0x29] :=
  text_toUTF8 _ (by decide)

example : (text [0x80]).toUTF8.data.toList = [0xc2, 0x80] := by decide +kernel

example : (text [0x80]).toUTF8.data.toList ≠ [0x80] := by decide +kernel

end Mettapedia.Data.String.Ascii
