import Mathlib.Data.List.Basic
import Mettapedia.GSLT.Parsing.ExactDecimalLexeme

/-!
# Complete consumption by the exact decimal parser

These laws apply to the existing exact integer/rational lexical parser.  They
do not claim a floating-point conversion law or native C correspondence.
Successful parsing accounts for every input character, including characters
after an otherwise valid numeric prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Data.String.DecimalConsumption

open Mettapedia.GSLT.Parsing.ExactDecimalLexeme

/-- The accumulator parser has the value of the full left-to-right decimal
fold, after validating every character. -/
theorem parseDigits?_fold (chars : List Char) (initial : Nat) :
    parseDigits? chars initial =
      (chars.mapM decimalDigit?).map (fun digits =>
        digits.foldl (fun value digit => value * 10 + digit) initial) := by
  induction chars generalizing initial with
  | nil => rfl
  | cons c cs ih =>
    cases headResult : decimalDigit? c with
    | none => simp [parseDigits?, headResult]
    | some d =>
      cases tailResult : cs.mapM decimalDigit? with
      | none => simp [parseDigits?, headResult, ih, tailResult]
      | some ds => simp [parseDigits?, headResult, ih, tailResult]

/-- Splitting the input does not silently discard the second part. -/
theorem parseDigits?_append (left right : List Char) (initial : Nat) :
    parseDigits? (left ++ right) initial =
      (parseDigits? left initial).bind (parseDigits? right) := by
  induction left generalizing initial with
  | nil => rfl
  | cons c cs ih =>
    cases headResult : decimalDigit? c <;> simp [parseDigits?, headResult, ih]

theorem parseDigits?_all_digits {chars : List Char} {initial value : Nat}
    (parsed : parseDigits? chars initial = some value) :
    ∀ c ∈ chars, ∃ digit, decimalDigit? c = some digit := by
  induction chars generalizing initial with
  | nil => simp
  | cons c cs ih =>
    cases headResult : decimalDigit? c with
    | none => simp [parseDigits?, headResult] at parsed
    | some d =>
      simp [parseDigits?, headResult] at parsed
      intro ch member
      rcases List.mem_cons.1 member with rfl | inTail
      · exact ⟨d, headResult⟩
      · exact ih parsed ch inTail

theorem parseDigits?_reject_non_digit {chars : List Char} {c : Char}
    (member : c ∈ chars) (invalid : decimalDigit? c = none) (initial : Nat) :
    parseDigits? chars initial = none := by
  cases result : parseDigits? chars initial with
  | none => rfl
  | some value =>
    obtain ⟨digit, parsed⟩ := parseDigits?_all_digits result c member
    simp [invalid] at parsed

/-- A malformed suffix cannot be ignored even after a valid numeric prefix. -/
theorem parseDigits?_reject_suffix (left right : List Char) (c : Char)
    (invalid : decimalDigit? c = none) (initial : Nat) :
    parseDigits? (left ++ c :: right) initial = none :=
  parseDigits?_reject_non_digit (by simp) invalid initial

theorem parseUnsignedChars?_all_digits {chars : List Char} {value : Nat}
    (parsed : parseUnsignedChars? chars = some value) :
    ∀ c ∈ chars, ∃ digit, decimalDigit? c = some digit := by
  unfold parseUnsignedChars? at parsed
  split at parsed
  · cases parsed
  ·
    intro c hc
    have same : c = '0' := by simpa using hc
    subst c
    exact ⟨0, rfl⟩
  · cases parsed
  · exact parseDigits?_all_digits parsed

theorem parseUnsignedChars?_reject_non_digit {chars : List Char} {c : Char}
    (member : c ∈ chars) (invalid : decimalDigit? c = none) :
    parseUnsignedChars? chars = none := by
  cases result : parseUnsignedChars? chars with
  | none => rfl
  | some value =>
    obtain ⟨digit, parsed⟩ := parseUnsignedChars?_all_digits result c member
    simp [invalid] at parsed

/-- The only non-digit that a successful integer can contain is one leading
sign.  The unsigned magnitude is nonempty and consumes the remaining input. -/
theorem parseIntegerChars?_consumed {chars : List Char} {value : Int}
    (parsed : parseIntegerChars? chars = some value) :
    ∃ magnitude,
      (chars = magnitude ∨ chars = '+' :: magnitude ∨ chars = '-' :: magnitude) ∧
      magnitude ≠ [] ∧
      (∀ c ∈ magnitude, ∃ digit, decimalDigit? c = some digit) := by
  have unsigned : ∀ {cs : List Char} {n : Nat},
      parseUnsignedChars? cs = some n → cs ≠ [] ∧
        (∀ c ∈ cs, ∃ digit, decimalDigit? c = some digit) := by
    intro cs n accepted
    refine ⟨?_, parseUnsignedChars?_all_digits accepted⟩
    intro empty
    simp [empty, parseUnsignedChars?] at accepted
  unfold parseIntegerChars? at parsed
  split at parsed
  ·
    obtain ⟨n, accepted, _⟩ := Option.map_eq_some_iff.1 parsed
    exact ⟨_, Or.inr (Or.inl rfl), unsigned accepted⟩
  ·
    obtain ⟨n, accepted, _⟩ := Option.map_eq_some_iff.1 parsed
    exact ⟨_, Or.inr (Or.inr rfl), unsigned accepted⟩
  ·
    obtain ⟨n, accepted, _⟩ := Option.map_eq_some_iff.1 parsed
    exact ⟨_, Or.inl rfl, unsigned accepted⟩

/-- Any character that is neither a digit nor a sign forces rejection,
wherever it occurs, rather than a successful prefix parse. -/
theorem parseIntegerChars?_reject_junk {chars : List Char} {c : Char}
    (member : c ∈ chars) (invalid : decimalDigit? c = none)
    (notPlus : c ≠ '+') (notMinus : c ≠ '-') :
    parseIntegerChars? chars = none := by
  cases result : parseIntegerChars? chars with
  | none => rfl
  | some value =>
    obtain ⟨magnitude, shape, _, allDigits⟩ := parseIntegerChars?_consumed result
    have inMagnitude : c ∈ magnitude := by
      rcases shape with rfl | rfl | rfl
      · exact member
      · simpa [notPlus] using member
      · simpa [notMinus] using member
    obtain ⟨d, accepted⟩ := allDigits c inMagnitude
    simp [invalid] at accepted

theorem splitSlash?_reconstruct {chars numerator denominator : List Char}
    (split : splitSlash? chars = some (numerator, denominator)) :
    chars = numerator ++ '/' :: denominator := by
  induction chars generalizing numerator denominator with
  | nil => cases split
  | cons c rest ih =>
    by_cases separator : c = '/'
    · subst c
      simp only [splitSlash?] at split
      split at split
      · cases split
      · have same : ([], rest) = (numerator, denominator) := Option.some.inj split
        cases same
        rfl
    · simp only [splitSlash?] at split
      cases restSplit : splitSlash? rest with
      | none => simp [restSplit] at split
      | some pair =>
        rcases pair with ⟨n, d⟩
        have same : (c :: n, d) = (numerator, denominator) := by
          simpa [restSplit] using split
        cases same
        simp [ih restSplit]

/-- Rational splitting covers the complete source, and both components pass
the exact parsers.  The denominator is strictly positive. -/
theorem parseRational?_consumed {text : String} {numerator denominator : Int}
    (parsed : parseRational? text = some (numerator, denominator)) :
    ∃ numeratorChars denominatorChars denominatorNat,
      text.toList = numeratorChars ++ '/' :: denominatorChars ∧
      parseIntegerChars? numeratorChars = some numerator ∧
      parseUnsignedChars? denominatorChars = some denominatorNat ∧
      denominatorNat > 0 ∧ denominator = Int.ofNat denominatorNat := by
  unfold parseRational? at parsed
  cases split : splitSlash? text.toList with
  | none => simp [split] at parsed
  | some pair =>
    rcases pair with ⟨nc, dc⟩
    simp only [split] at parsed
    cases numeratorResult : parseIntegerChars? nc with
    | none => simp [numeratorResult] at parsed
    | some n =>
      cases denominatorResult : parseUnsignedChars? dc with
      | none => simp [numeratorResult, denominatorResult] at parsed
      | some d =>
        by_cases zero : d = 0
        · simp [numeratorResult, denominatorResult, zero] at parsed
        · have same : (n, Int.ofNat d) = (numerator, denominator) := by
            simpa [numeratorResult, denominatorResult, zero] using parsed
          cases same
          exact ⟨nc, dc, d, splitSlash?_reconstruct split,
            numeratorResult, denominatorResult, Nat.pos_of_ne_zero zero, rfl⟩

/-! Full-consumption controls; trailing junk, embedded NUL and extra separators
are not valid number suffixes. -/

example : parseInteger? "+17" = some 17 := by decide +kernel
example : parseInteger? "17x" = none := by decide +kernel
example : parseInteger? "17\x00" = none := by decide +kernel
example : parseInteger? "17  " = none := by decide +kernel
example : parseInteger? "17+" = none := by decide +kernel
example : parseRational? "-17/23" = some (-17, 23) := by decide +kernel
example : parseRational? "17/23x" = none := by decide +kernel
example : parseRational? "17/23/29" = none := by decide +kernel

#print axioms parseDigits?_fold
#print axioms parseDigits?_append
#print axioms parseDigits?_reject_suffix
#print axioms parseIntegerChars?_consumed
#print axioms parseIntegerChars?_reject_junk
#print axioms parseRational?_consumed

end Mettapedia.Data.String.DecimalConsumption
