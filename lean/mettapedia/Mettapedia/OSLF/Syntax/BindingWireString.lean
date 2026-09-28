import Mettapedia.OSLF.Syntax.BindingWireData

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.WireCodec

namespace Utf8

/-- Decode a byte sequence into candidate scalar values. Re-encoding below
checks the entire sequence, including canonical UTF-8 and scalar validity. -/
def decode : List UInt8 → Option (List Char)
  | [] => some []
  | a :: tail =>
      if a.toNat < 128 then (decode tail).map (Char.ofNat a.toNat :: ·)
      else match tail with
        | [] => none
        | b :: tail =>
            if a.toNat < 224 then
              (decode tail).map (Char.ofNat ((a.toNat - 192) * 64 + b.toNat - 128) :: ·)
            else match tail with
              | [] => none
              | c :: tail =>
                  if a.toNat < 240 then
                    (decode tail).map (Char.ofNat
                      ((a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + c.toNat - 128) :: ·)
                  else match tail with
                    | [] => none
                    | d :: tail =>
                        (decode tail).map (Char.ofNat
                          ((a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
                            (c.toNat - 128) * 64 + d.toNat - 128) :: ·)

theorem decode_char (c : Char) (tail : List UInt8) :
    decode (String.utf8EncodeChar c ++ tail) = (decode tail).map (c :: ·) := by
  have scalar := c.valid
  simp only [UInt32.isValidChar] at scalar
  by_cases first : c.val.toNat ≤ 127
  · simp only [String.utf8EncodeChar, first, ite_true, List.cons_append,
      List.nil_append]
    rw [decode.eq_def]
    simp only [UInt8.toNat_ofNat']
    have bound : c.val.toNat % 256 < 128 := by omega
    have value : c.val.toNat % 256 = c.toNat := by change _ = c.val.toNat; omega
    rw [if_pos bound, value, Char.ofNat_toNat]
  · by_cases second : c.val.toNat ≤ 2047
    · simp only [String.utf8EncodeChar, first, ite_false, second, ite_true,
        List.cons_append, List.nil_append]
      rw [decode.eq_def]
      simp only [UInt8.toNat_ofNat']
      have notFirst : ¬ (c.val.toNat / 64 % 32 + 192) % 256 < 128 := by omega
      have isSecond : (c.val.toNat / 64 % 32 + 192) % 256 < 224 := by omega
      rw [if_neg notFirst, if_pos isSecond]
      have value : ((c.val.toNat / 64 % 32 + 192) % 256 - 192) * 64 +
          (c.val.toNat % 64 + 128) % 256 - 128 = c.toNat := by
        change _ = c.val.toNat
        omega
      rw [value, Char.ofNat_toNat]
    · by_cases third : c.val.toNat ≤ 65535
      · simp only [String.utf8EncodeChar, first, ite_false, second, third, ite_true,
          List.cons_append, List.nil_append]
        rw [decode.eq_def]
        simp only [UInt8.toNat_ofNat']
        have notFirst : ¬ (c.val.toNat / 4096 % 16 + 224) % 256 < 128 := by omega
        have notSecond : ¬ (c.val.toNat / 4096 % 16 + 224) % 256 < 224 := by omega
        have isThird : (c.val.toNat / 4096 % 16 + 224) % 256 < 240 := by omega
        rw [if_neg notFirst, if_neg notSecond, if_pos isThird]
        have value : ((c.val.toNat / 4096 % 16 + 224) % 256 - 224) * 4096 +
            ((c.val.toNat / 64 % 64 + 128) % 256 - 128) * 64 +
            (c.val.toNat % 64 + 128) % 256 - 128 = c.toNat := by
          change _ = c.val.toNat
          omega
        rw [value, Char.ofNat_toNat]
      · simp only [String.utf8EncodeChar, first, ite_false, second, third,
          List.cons_append, List.nil_append, decode, UInt8.toNat_ofNat']
        have notFirst : ¬ (c.val.toNat / 262144 % 8 + 240) % 256 < 128 := by omega
        have notSecond : ¬ (c.val.toNat / 262144 % 8 + 240) % 256 < 224 := by omega
        have notThird : ¬ (c.val.toNat / 262144 % 8 + 240) % 256 < 240 := by omega
        rw [if_neg notFirst, if_neg notSecond, if_neg notThird]
        have value : ((c.val.toNat / 262144 % 8 + 240) % 256 - 240) * 262144 +
            ((c.val.toNat / 4096 % 64 + 128) % 256 - 128) * 4096 +
            ((c.val.toNat / 64 % 64 + 128) % 256 - 128) * 64 +
            (c.val.toNat % 64 + 128) % 256 - 128 = c.toNat := by
          change _ = c.val.toNat
          omega
        rw [value, Char.ofNat_toNat]

theorem decode_encode (chars : List Char) :
    decode (chars.flatMap String.utf8EncodeChar) = some chars := by
  induction chars with
  | nil => rfl
  | cons c chars ih => rw [List.flatMap_cons, decode_char, ih]; rfl

def bytes (text : String) : List UInt8 := text.toByteArray.data.toList

def read (input : List UInt8) : Option String := do
  let chars ← decode input
  let text := String.ofList chars
  if bytes text = input then some text else none

theorem read_bytes (text : String) : read (bytes text) = some text := by
  obtain ⟨chars, rfl⟩ := text.exists_eq_ofList
  simp only [bytes, String.toByteArray_ofList, List.utf8Encode,
    List.toList_data_toByteArray, read, decode_encode]
  simp only [Bind.bind, Option.bind, ite_true]

end Utf8

namespace Codec

def byte : Codec UInt8 :=
  nat.mapped UInt8.toNat
    (fun n => if n < 256 then some (UInt8.ofNat n) else none)
    (fun b => by simp only [UInt8.toNat_lt_size, ite_true, UInt8.ofNat_toNat])

def string : Codec String := (list byte).mapped Utf8.bytes Utf8.read Utf8.read_bytes

end Codec
end Mettapedia.OSLF.Binding.WireCodec
