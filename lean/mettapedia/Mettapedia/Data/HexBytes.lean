import Mathlib.Data.List.Basic

/-! Flat hexadecimal transport for counted binary evidence. Decoding walks
pairs with a reversed accumulator, so byte count does not become parser
nesting depth. Uppercase and lowercase hexadecimal digits are accepted. -/

set_option autoImplicit false

namespace Mettapedia.Data.HexBytes

def digit? (character : Char) : Option Nat :=
  let n := character.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else none

def pair? (first second : Char) : Option UInt8 := do
  let high ← digit? first
  let low ← digit? second
  pure (UInt8.ofNat (16 * high + low))

def decodeChars : List Char → List UInt8 → Option (List UInt8)
  | [], bytes => some bytes.reverse
  | first :: second :: rest, bytes => do
    let byte ← pair? first second
    decodeChars rest (byte :: bytes)
  | _, _ => none

def decode? (text : String) : Option (List UInt8) := decodeChars text.toList []

def digit (number : Nat) : Char :=
  Char.ofNat (if number < 10 then 48 + number else 87 + number)

def byteChars (byte : UInt8) : List Char :=
  [digit (byte.toNat / 16), digit (byte.toNat % 16)]

def encode (bytes : List UInt8) : String := String.ofList (bytes.flatMap byteChars)

private theorem pair_fin : ∀ byte : Fin 256,
    pair? (digit (byte.val / 16)) (digit (byte.val % 16)) = some (UInt8.ofNat byte.val) := by
  decide +kernel

private theorem pair_byte (byte : UInt8) :
    pair? (digit (byte.toNat / 16)) (digit (byte.toNat % 16)) = some byte := by
  simpa using pair_fin ⟨byte.toNat, byte.toNat_lt⟩

theorem decodeChars_encoded (bytes accumulated : List UInt8) :
    decodeChars (bytes.flatMap byteChars) accumulated = some (accumulated.reverse ++ bytes) := by
  induction bytes generalizing accumulated with
  | nil => simp [decodeChars]
  | cons byte rest ih =>
    simp only [List.flatMap_cons, byteChars, List.cons_append, List.nil_append, decodeChars, pair_byte]
    simpa [List.reverse_cons, List.append_assoc] using ih (byte :: accumulated)

theorem decode_encode (bytes : List UInt8) : decode? (encode bytes) = some bytes := by
  simpa [decode?, encode] using decodeChars_encoded bytes []

example : decode? "00fF80" = some [0,255,128] := by decide +kernel
example : decode? "0" = none := by decide +kernel
example : decode? "gg" = none := by decide +kernel
example : decode? "１２" = none := by decide +kernel

end Mettapedia.Data.HexBytes
