import Mettapedia.Languages.Datalog.NumericSpelling
import Std.Data.String.ToInt
import Init.Omega

/-! Canonical decimal printing is an inverse of the positional source reader. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.NumericSpelling

theorem digit_of_decimal {character : Char} (decimal : character.isDigit = true) :
    digit character = character.toNat - '0'.toNat := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at decimal
  have bounds : '0' ≤ character ∧ character ≤ '9' := decimal
  rw [digit, if_pos bounds]

theorem digit_lt_ten {character : Char} (decimal : character.isDigit = true) :
    digit character < 10 := by
  rw [digit_of_decimal decimal]
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at decimal
  have low : 48 ≤ character.toNat := UInt32.le_iff_toNat_le.mp decimal.1
  have high : character.toNat ≤ 57 := UInt32.le_iff_toNat_le.mp decimal.2
  change character.toNat - 48 < 10
  omega

theorem accumulate_decimal (characters : List Char) (value : Nat)
    (decimal : ∀ character ∈ characters, character.isDigit = true) :
    accumulate 10 value characters = Nat.ofDigitChars 10 characters value := by
  induction characters generalizing value with
  | nil => simp [accumulate]
  | cons character rest ih =>
      rw [accumulate, Nat.ofDigitChars_cons, digit_of_decimal (decimal _ (by simp))]
      simpa only [Nat.mul_comm] using ih (value * 10 + (character.toNat - '0'.toNat))
        (fun c member => decimal c (by simp [member]))

theorem decimal_repr (value : Nat) : readDigits? 10 value.repr.toList = some value := by
  have decimal : ∀ c ∈ value.repr.toList, c.isDigit = true := by
    simpa only [Nat.toList_repr] using
      fun c member => Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) member
  have valid : value.repr.toList.all (fun c => decide (digit c < 10)) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact fun c member => digit_lt_ten (decimal c member)
  unfold readDigits?
  rw [valid]
  have nonempty : value.repr.toList.isEmpty = false := by simp
  rw [nonempty]
  simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [accumulate_decimal _ _ decimal, Nat.toList_repr, Nat.ofDigitChars_ten_toDigits]

theorem unsignedParts_decimal (characters : List Char)
    (decimal : ∀ character ∈ characters, character.isDigit = true) :
    unsignedParts characters = (10, characters) := by
  unfold unsignedParts
  split
  · have := decimal 'b' (by simp_all)
    contradiction
  · have := decimal 'x' (by simp_all)
    contradiction
  · rfl

theorem magnitude_repr (value : Nat) : readMagnitude? value.repr.toList = some value := by
  have decimal : ∀ c ∈ value.repr.toList, c.isDigit = true := by
    simpa only [Nat.toList_repr] using
      fun c member => Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) member
  simpa only [readMagnitude?, unsignedParts_decimal _ decimal] using decimal_repr value

theorem integer_nat_repr (value : Nat) : readInteger? value.repr = some (Int.ofNat value) := by
  unfold readInteger?
  split
  · rename_i rest found
    have digit : '-'.isDigit = true := Nat.isDigit_of_mem_toDigits
      (by decide : 0 < 10) (by decide : 10 ≤ 10) (by rw [← Nat.toList_repr, found]; simp)
    contradiction
  · rw [magnitude_repr]
    rfl

theorem integer_negative_repr (value : Nat) :
    readInteger? ("-" ++ value.repr) = some (-Int.ofNat value) := by
  simp only [readInteger?, String.toList_append, String.reduceToList, List.cons_append,
    List.nil_append, magnitude_repr, Option.map_some]

theorem integer_repr (value : Int) : readInteger? value.repr = some value := by
  rw [Int.repr_eq_if]
  split
  · rw [integer_nat_repr]
    congr 1
    exact Int.toNat_of_nonneg (by assumption)
  · rw [integer_negative_repr]
    congr 1
    change -(((-value).toNat : Nat) : Int) = value
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ -value), neg_neg]

theorem unsigned_repr (value : Nat) : readUnsigned? (value.repr ++ "u") = some value := by
  simp only [readUnsigned?, String.toList_append, String.reduceToList,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, ↓reduceIte,
    List.dropLast_concat, magnitude_repr]

end Mettapedia.Languages.Datalog.NumericSpelling
