import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-! Positional integer spellings used by the source frontend. The relation
specifies digit values independently of the executable left fold. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.NumericSpelling

def digit (character : Char) : Nat :=
  if '0' ≤ character ∧ character ≤ '9' then character.toNat - '0'.toNat
  else if 'a' ≤ character ∧ character ≤ 'f' then character.toNat - 'a'.toNat + 10
  else if 'A' ≤ character ∧ character ≤ 'F' then character.toNat - 'A'.toNat + 10
  else 16

def magnitude (base : Nat) : List Char → Nat
  | [] => 0
  | character :: rest => digit character * base ^ rest.length + magnitude base rest

def Digits (base : Nat) (characters : List Char) (value : Nat) : Prop :=
  characters ≠ [] ∧ (∀ character ∈ characters, digit character < base) ∧
    magnitude base characters = value

def accumulate (base : Nat) : Nat → List Char → Nat
  | value, [] => value
  | value, character :: rest => accumulate base (value * base + digit character) rest

def readDigits? (base : Nat) (characters : List Char) : Option Nat :=
  if characters.isEmpty || !(characters.all fun character => decide (digit character < base))
  then none else some (accumulate base 0 characters)

theorem accumulate_exact (base value : Nat) (characters : List Char) :
    accumulate base value characters = value * base ^ characters.length + magnitude base characters := by
  induction characters generalizing value with
  | nil => simp [accumulate, magnitude]
  | cons character rest ih =>
      rw [accumulate, ih]
      simp only [List.length_cons, magnitude, pow_succ]
      ring

theorem readDigits_exact (base : Nat) (characters : List Char) (value : Nat) :
    readDigits? base characters = some value ↔ Digits base characters value := by
  simp [readDigits?, Digits, accumulate_exact, List.isEmpty_iff, List.all_eq_true,
    Bool.eq_false_iff, and_assoc]

def unsignedParts : List Char → Nat × List Char
  | '0' :: 'b' :: rest => (2, rest)
  | '0' :: 'x' :: rest => (16, rest)
  | rest => (10, rest)

def readMagnitude? (characters : List Char) : Option Nat :=
  let (base, digits) := unsignedParts characters
  readDigits? base digits

def readInteger? (text : String) : Option Int :=
  match text.toList with
  | '-' :: rest => (readMagnitude? rest).map fun value => -(Int.ofNat value)
  | rest => (readMagnitude? rest).map Int.ofNat

def Integer (text : String) (value : Int) : Prop :=
  match text.toList with
  | '-' :: rest => ∃ magnitude, Digits (unsignedParts rest).1 (unsignedParts rest).2 magnitude ∧
      value = -(Int.ofNat magnitude)
  | rest => ∃ magnitude, Digits (unsignedParts rest).1 (unsignedParts rest).2 magnitude ∧
      value = Int.ofNat magnitude

theorem readInteger_exact (text : String) (value : Int) :
    readInteger? text = some value ↔ Integer text value := by
  unfold readInteger? Integer
  split <;> simp only [Option.map_eq_some_iff, readMagnitude?, readDigits_exact]
  all_goals constructor <;> rintro ⟨number, digits, same⟩ <;> exact ⟨number, digits, same.symm⟩

def readUnsigned? (text : String) : Option Nat :=
  if text.toList.getLast? = some 'u' then readMagnitude? text.toList.dropLast else none

def Unsigned (text : String) (value : Nat) : Prop :=
  text.toList.getLast? = some 'u' ∧
    Digits (unsignedParts text.toList.dropLast).1 (unsignedParts text.toList.dropLast).2 value

theorem readUnsigned_exact (text : String) (value : Nat) :
    readUnsigned? text = some value ↔ Unsigned text value := by
  simp [readUnsigned?, Unsigned, readMagnitude?, readDigits_exact]

theorem alternate_spellings :
    readInteger? "00012" = some 12 ∧ readInteger? "-00012" = some (-12) ∧
    readInteger? "-0" = some 0 ∧ readInteger? "0b1010" = some 10 ∧
    readInteger? "-0xAf" = some (-175) ∧ readUnsigned? "0xAFu" = some 175 := by
  decide +kernel

theorem malformed_spellings :
    readInteger? "" = none ∧ readInteger? "-" = none ∧ readInteger? "0b2" = none ∧
    readInteger? "0xg" = none ∧ readInteger? "12u" = none ∧ readUnsigned? "12" = none := by
  decide +kernel

end Mettapedia.Languages.Datalog.NumericSpelling
