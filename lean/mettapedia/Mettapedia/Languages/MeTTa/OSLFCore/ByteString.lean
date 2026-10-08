import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.Data.String.Utf8

/-!
# Canonical byte-string images in the existing Atom datatype

Valid UTF-8 has its ordinary grounded String image. Other byte sequences use
a reserved custom tag with one Latin-1 scalar per byte. The decoder checks
the payload range and rejects custom images of valid UTF-8. No input bytes
are replaced or discarded, including NUL and malformed UTF-8.

This is a wire image for native strings, separate from reader execution and
filesystem effects. It adds no Atom constructor or evaluation rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.OSLFCore.ByteString

open Mettapedia.Data.String

/-- Reserved for byte sequences which have no ordinary UTF-8 String image. -/
def tag : String := "NativeStringBytesV1"

private def payload (bytes : List UInt8) : String :=
  String.ofList (bytes.map Char.ofUInt8)

private def readPayloadChars : List Char → Option (List UInt8)
  | [] => some []
  | character :: rest =>
      if character.toNat < 256 then do
        let bytes ← readPayloadChars rest
        pure (UInt8.ofNat character.toNat :: bytes)
      else none

private def readPayload (value : String) : Option (List UInt8) :=
  readPayloadChars value.toList

private theorem byte_character (byte : UInt8) :
    (Char.ofUInt8 byte).toNat = byte.toNat := by
  simp [Char.ofUInt8, Char.toNat]

private theorem character_byte (character : Char) (bounded : character.toNat < 256) :
    Char.ofUInt8 (UInt8.ofNat character.toNat) = character := by
  apply Char.toNat_inj.mp
  rw [byte_character]
  simp [Nat.mod_eq_of_lt bounded]

private theorem readPayloadChars_map (bytes : List UInt8) :
    readPayloadChars (bytes.map Char.ofUInt8) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      simp [readPayloadChars, byte_character, byte.toNat_lt_size, ih]

private theorem readPayloadChars_reflects (characters : List Char) (bytes : List UInt8)
    (decoded : readPayloadChars characters = some bytes) :
    bytes.map Char.ofUInt8 = characters := by
  induction characters generalizing bytes with
  | nil => simpa [readPayloadChars] using decoded.symm
  | cons character characters ih =>
      by_cases bounded : character.toNat < 256
      · cases tail : readPayloadChars characters with
        | none => simp [readPayloadChars, bounded, tail] at decoded
        | some remaining =>
            have same : UInt8.ofNat character.toNat :: remaining = bytes := by
              simpa [readPayloadChars, bounded, tail] using decoded
            subst bytes
            simp only [List.map_cons, character_byte character bounded, ih remaining tail]
      · simp [readPayloadChars, bounded] at decoded

private theorem readPayload_payload (bytes : List UInt8) :
    readPayload (payload bytes) = some bytes := by
  simp [readPayload, payload, readPayloadChars_map]

private theorem payload_readPayload (value : String) (bytes : List UInt8)
    (decoded : readPayload value = some bytes) : payload bytes = value := by
  apply String.toList_inj.mp
  simp only [payload, String.toList_ofList]
  exact readPayloadChars_reflects value.toList bytes decoded

/-- The unique image of a native string's complete explicit-length byte buffer. -/
def encode (bytes : List UInt8) : Atom :=
  match Utf8.decode ⟨bytes.toArray⟩ with
  | .ok characters => .grounded (.string (String.ofList characters.toList))
  | .error _ => .grounded (.custom tag (payload bytes))

/-- Decode native String images only; custom payloads must be canonical. -/
def decode : Atom → Option (List UInt8)
  | .grounded (.string value) => some value.toUTF8.data.toList
  | .grounded (.custom name value) =>
      if name = tag then do
        let bytes ← readPayload value
        match Utf8.decode ⟨bytes.toArray⟩ with
        | .ok _ => none
        | .error _ => some bytes
      else none
  | _ => none

/-- Native text arguments also accept a symbol's exact UTF-8 spelling. -/
def text (atom : Atom) : Option (List UInt8) :=
  match atom with
  | .symbol name => some name.toUTF8.data.toList
  | _ => decode atom

@[simp] theorem decode_string (value : String) :
    decode (.grounded (.string value)) = some value.toUTF8.data.toList := rfl

@[simp] theorem text_symbol (name : String) :
    text (.symbol name) = some name.toUTF8.data.toList := rfl

@[simp] theorem encode_utf8 (value : String) :
    encode value.toUTF8.data.toList = .grounded (.string value) := by
  have decoded : Utf8.decode value.toUTF8 = .ok value.toList.toArray := by
    simpa [String.toUTF8_eq_toByteArray] using Utf8.decode_encoded value.toList
  simp only [encode, Array.toArray_toList, decoded, String.ofList_toList]

@[simp] theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = some bytes := by
  cases decoded : Utf8.decode ⟨bytes.toArray⟩ with
  | ok characters =>
      have exactBytes := Utf8.encode_decoded decoded
      have exactList : (String.ofList characters.toList).toUTF8.data.toList = bytes := by
        simpa [String.toUTF8_eq_toByteArray] using
          congrArg (fun array : ByteArray => array.data.toList) exactBytes
      simp only [encode, decoded, decode, exactList]
  | error offset =>
      simp [encode, decoded, decode, readPayload_payload]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using decoded

/-- Successful decoding reflects the exact canonical constructor image. -/
theorem encode_decoded (atom : Atom) (bytes : List UInt8)
    (decoded : decode atom = some bytes) : encode bytes = atom := by
  cases atom with
  | symbol _ | var _ | expression _ => simp [decode] at decoded
  | grounded value =>
      cases value with
      | int _ | bool _ => simp [decode] at decoded
      | string value =>
          have same : value.toUTF8.data.toList = bytes := Option.some.inj decoded
          rw [← same, encode_utf8]
      | custom name value =>
          by_cases named : name = tag
          · subst name
            cases read : readPayload value with
            | none => simp [decode, read] at decoded
            | some remaining =>
                cases valid : Utf8.decode ⟨remaining.toArray⟩ with
                | ok _ => simp [decode, read, valid] at decoded
                | error _ =>
                    have same : remaining = bytes := by
                      simpa [decode, read, valid] using decoded
                    subst bytes
                    simp [encode, valid, payload_readPayload value remaining read]
          · simp [decode, named] at decoded

theorem decode_iff (atom : Atom) (bytes : List UInt8) :
    decode atom = some bytes ↔ encode bytes = atom :=
  ⟨encode_decoded atom bytes, fun same => same ▸ decode_encode bytes⟩

@[simp] theorem text_encode (bytes : List UInt8) : text (encode bytes) = some bytes := by
  unfold text
  cases decoded : Utf8.decode ⟨bytes.toArray⟩ <;>
    simpa only [encode, decoded] using decode_encode bytes

/-! ## Byte-preserving and refusal controls -/

theorem embedded_nul_preserved :
    encode [0x61, 0, 0x62] = .grounded (.string "a\x00b") ∧
      decode (encode [0x61, 0, 0x62]) = some [0x61, 0, 0x62] := by
  constructor
  · decide +kernel
  · exact decode_encode _

theorem invalid_utf8_preserved :
    encode [0xff, 0, 0x80] =
      .grounded (.custom tag (String.ofList [Char.ofUInt8 0xff, '\x00', Char.ofUInt8 0x80])) ∧
      decode (encode [0xff, 0, 0x80]) = some [0xff, 0, 0x80] := by
  constructor
  · decide +kernel
  · exact decode_encode _

theorem multibyte_string_image :
    encode [0xce, 0xbb] = .grounded (.string "λ") := by decide +kernel

theorem partial_scalar_preserved :
    decode (encode [0xce]) = some [0xce] ∧
      encode [0xce] ≠ .grounded (.string "λ") := by
  constructor
  · exact decode_encode _
  · decide +kernel

theorem malformed_payload_refused :
    decode (.grounded (.custom tag "λ")) = none := by decide +kernel

theorem noncanonical_ascii_refused :
    decode (.grounded (.custom tag "a")) = none := by decide +kernel

theorem noncanonical_multibyte_refused :
    decode (.grounded (.custom tag (String.ofList [Char.ofUInt8 0xce, Char.ofUInt8 0xbb]))) =
      none := by decide +kernel

theorem unrelated_custom_refused :
    decode (.grounded (.custom "Other" (String.ofList [Char.ofUInt8 0xff]))) = none := by
  decide +kernel

theorem symbol_is_text_but_not_string :
    text (.symbol "a") = some [0x61] ∧ decode (.symbol "a") = none := by decide +kernel

theorem nontext_refused :
    text (.grounded (.int 255)) = none ∧ text (.var "x") = none ∧
      text (.expression []) = none := by decide +kernel

end Mettapedia.Languages.MeTTa.OSLFCore.ByteString
