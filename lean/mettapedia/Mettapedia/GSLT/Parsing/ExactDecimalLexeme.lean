/-!
# Exact decimal integer and rational lexemes

These validated values are a generic lexical boundary for grammar-derived
readers.  The accepted integer syntax is an optional `+` or `-` followed by a
canonical unsigned decimal magnitude.  Rationals contain one such numerator,
one `/`, and a strictly positive canonical denominator.  Leading zeroes are
rejected except for the single spelling `0`.

The structures retain both source text and mathematical value.  A later
policy may discard spelling while occurrence metadata retains it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ExactDecimalLexeme

def decimalDigit? : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

def parseDigits? : List Char → Nat → Option Nat
  | [], value => some value
  | character :: rest, value => do
      let digit ← decimalDigit? character
      parseDigits? rest (value * 10 + digit)

/-- Canonical unsigned decimal text.  Parsing the character list directly
keeps the exact grammar boundary transparent to the kernel and avoids
delegating admissibility to an opaque host string conversion. -/
def parseUnsignedChars? : List Char → Option Nat
  | [] => none
  | ['0'] => some 0
  | '0' :: _ => none
  | characters => parseDigits? characters 0

def parseUnsigned? (text : String) : Option Nat :=
  parseUnsignedChars? text.toList

def parseIntegerChars? : List Char → Option Int
  | '+' :: rest => (parseUnsignedChars? rest).map Int.ofNat
  | '-' :: rest => (parseUnsignedChars? rest).map fun value => -(Int.ofNat value)
  | characters => (parseUnsignedChars? characters).map Int.ofNat

def parseInteger? (text : String) : Option Int :=
  parseIntegerChars? text.toList

/-- Split at exactly one rational separator. -/
def splitSlash? : List Char → Option (List Char × List Char)
  | [] => none
  | '/' :: rest =>
      if rest.contains '/' then none else some ([], rest)
  | character :: rest => do
      let (numerator, denominator) ← splitSlash? rest
      some (character :: numerator, denominator)

def parseRational? (text : String) : Option (Int × Int) :=
  match splitSlash? text.toList with
  | some (numeratorText, denominatorText) => do
      let numerator ← parseIntegerChars? numeratorText
      let denominatorNat ← parseUnsignedChars? denominatorText
      if denominatorNat = 0 then none
      else some (numerator, Int.ofNat denominatorNat)
  | none => none

structure Integer where
  text : String
  value : Int
  decoded : parseInteger? text = some value

structure Rational where
  text : String
  numerator : Int
  denominator : Int
  decoded : parseRational? text = some (numerator, denominator)

def decodeInteger? (text : String) : Option Integer :=
  match parsed : parseInteger? text with
  | none => none
  | some value => some ⟨text, value, parsed⟩

def decodeRational? (text : String) : Option Rational :=
  match parsed : parseRational? text with
  | none => none
  | some (numerator, denominator) =>
      some ⟨text, numerator, denominator, parsed⟩

theorem decodeInteger?_isSome_iff (text : String) :
    (decodeInteger? text).isSome = (parseInteger? text).isSome := by
  unfold decodeInteger?
  split <;> simp_all

theorem decodeRational?_isSome_iff (text : String) :
    (decodeRational? text).isSome = (parseRational? text).isSome := by
  unfold decodeRational?
  split <;> simp_all

theorem Integer.text_injective {left right : Integer}
    (same : left.text = right.text) : left = right := by
  cases left with
  | mk leftText leftValue leftDecoded =>
    cases right with
    | mk rightText rightValue rightDecoded =>
      simp only at same
      subst rightText
      have values : leftValue = rightValue := by
        simpa [leftDecoded] using rightDecoded
      subst rightValue
      rfl

theorem Rational.text_injective {left right : Rational}
    (same : left.text = right.text) : left = right := by
  cases left with
  | mk leftText leftNumerator leftDenominator leftDecoded =>
    cases right with
    | mk rightText rightNumerator rightDenominator rightDecoded =>
      simp only at same
      subst rightText
      have values :
          (leftNumerator, leftDenominator) =
            (rightNumerator, rightDenominator) := by
        simpa [leftDecoded] using rightDecoded
      cases values
      rfl

@[simp] theorem decodeInteger?_text (value : Integer) :
    decodeInteger? value.text = some value := by
  cases value with
  | mk text expected accepted =>
    unfold decodeInteger?
    split
    · rename_i rejected
      rw [accepted] at rejected
      contradiction
    · rename_i actual parsed
      have same : actual = expected := by
        rw [accepted] at parsed
        exact Option.some.inj parsed.symm
      subst actual
      apply congrArg some
      exact Integer.text_injective rfl

@[simp] theorem decodeRational?_text (value : Rational) :
    decodeRational? value.text = some value := by
  cases value with
  | mk text expectedNumerator expectedDenominator accepted =>
    unfold decodeRational?
    split
    · rename_i rejected
      rw [accepted] at rejected
      contradiction
    · rename_i numerator denominator parsed
      have same : (numerator, denominator) =
          (expectedNumerator, expectedDenominator) := by
        rw [accepted] at parsed
        exact Option.some.inj parsed.symm
      cases same
      apply congrArg some
      exact Rational.text_injective rfl

/-! ## Positive and negative controls -/

example : parseInteger? "0" = some 0 := by decide +kernel
example : parseInteger? "+7" = some 7 := by decide +kernel
example : parseInteger? "-7" = some (-7) := by decide +kernel
example : parseInteger? "+0" = some 0 := by decide +kernel
example : parseInteger? "-0" = some 0 := by decide +kernel
example : parseInteger? "07" = none := by decide +kernel
example : parseInteger? "+07" = none := by decide +kernel
example : parseInteger? "" = none := by decide +kernel

example : parseRational? "1/2" = some (1, 2) := by decide +kernel
example : parseRational? "-1/2" = some (-1, 2) := by decide +kernel
example : parseRational? "+1/2" = some (1, 2) := by decide +kernel
example : parseRational? "1/0" = none := by decide +kernel
example : parseRational? "01/2" = none := by decide +kernel
example : parseRational? "1/02" = none := by decide +kernel
example : parseRational? "1/2/3" = none := by decide +kernel

#print axioms decodeInteger?_isSome_iff
#print axioms decodeRational?_isSome_iff
#print axioms decodeInteger?_text
#print axioms decodeRational?_text
#print axioms Integer.text_injective
#print axioms Rational.text_injective

end Mettapedia.GSLT.Parsing.ExactDecimalLexeme
