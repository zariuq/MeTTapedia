import Mathlib.Tactic
import Mettapedia.Data.String.DecimalConsumption

/-!
# Decimal values across character sets and bounded accumulation

Character recognition is supplied by a versioned decimal-value provider.
After recognition, digits from different sets are ordinary values 0–9.
The positional specification below is independent of the left-to-right
accumulator. The bounded algorithm uses the division guard of the native
decimal reader; its overflow flag is absorbing and never wraps the value.

These are arithmetic and lexical transport laws. They do not assume a
particular Unicode table is correct, or prove native pointer safety.
-/

set_option autoImplicit false

namespace Mettapedia.Data.String.UnicodeDecimal

open Mettapedia.GSLT.Parsing.ExactDecimalLexeme

abbrev Digit := Fin 10

/-- Positional decimal notation, independent of the accumulator algorithm. -/
def positionalValue : List Digit → Nat
  | [] => 0
  | digit :: rest => digit.val * 10 ^ rest.length + positionalValue rest

def accumulate (digits : List Digit) (initial : Nat := 0) : Nat :=
  digits.foldl (fun value digit => value * 10 + digit.val) initial

theorem accumulate_positional (digits : List Digit) (initial : Nat) :
    accumulate digits initial = initial * 10 ^ digits.length + positionalValue digits := by
  induction digits generalizing initial with
  | nil => simp [accumulate, positionalValue]
  | cons digit rest ih =>
    change accumulate rest (initial * 10 + digit.val) = _
    rw [ih]
    simp only [List.length_cons, positionalValue, pow_succ]
    ring

theorem accumulate_append (left right : List Digit) (initial : Nat) :
    accumulate (left ++ right) initial = accumulate right (accumulate left initial) := by
  simp [accumulate, List.foldl_append]

/-- Complete character consumption; there is no script-homogeneity test. -/
def recognize {α : Type} (decimal : α → Option Digit) (chars : List α) : Option (List Digit) :=
  chars.mapM decimal

def parse {α : Type} (decimal : α → Option Digit) (chars : List α) : Option Nat :=
  if chars = [] then none else (recognize decimal chars).map (fun ds => accumulate ds 0)

theorem recognize_all {α : Type} (decimal : α → Option Digit)
    {chars : List α} {digits : List Digit} (accepted : recognize decimal chars = some digits) :
    ∀ c ∈ chars, ∃ d, decimal c = some d := by
  induction chars generalizing digits with
  | nil => simp
  | cons c cs ih =>
    cases headResult : decimal c with
    | none => simp [recognize, headResult] at accepted
    | some d =>
      cases tailResult : cs.mapM decimal with
      | none => simp [recognize, headResult, tailResult] at accepted
      | some ds =>
        intro ch member
        rcases List.mem_cons.1 member with rfl | inTail
        · exact ⟨d, headResult⟩
        · exact ih tailResult ch inTail

theorem parse_rejects_junk {α : Type} (decimal : α → Option Digit)
    {chars : List α} {c : α} (member : c ∈ chars) (invalid : decimal c = none) :
    parse decimal chars = none := by
  unfold parse
  split_ifs
  · rfl
  · cases decoded : recognize decimal chars with
    | none => rfl
    | some ds =>
      obtain ⟨d, found⟩ := recognize_all decimal decoded c member
      simp [invalid] at found

def asciiDigit (digit : Digit) : Char := Char.ofNat (48 + digit.val)

theorem asciiDigit_value (digit : Digit) : decimalDigit? (asciiDigit digit) = some digit.val := by
  fin_cases digit <;> decide +kernel

/-- Translating recognized digits to ASCII preserves the existing exact
parser's whole-input value, including leading zeros. -/
theorem ascii_transport (digits : List Digit) (initial : Nat) :
    parseDigits? (digits.map asciiDigit) initial = some (accumulate digits initial) := by
  induction digits generalizing initial with
  | nil => rfl
  | cons digit rest ih =>
    simp only [List.map_cons, parseDigits?, asciiDigit_value]
    exact ih (initial * 10 + digit.val)

structure BoundedState where
  value : Nat
  overflow : Bool
  deriving DecidableEq, Repr

def boundedStep (maximum : Nat) (state : BoundedState) (digit : Digit) : BoundedState :=
  if state.overflow then state else
  if state.value > (maximum - digit.val) / 10 then { state with overflow := true }
  else ⟨state.value * 10 + digit.val, false⟩

def boundedAccumulate (maximum : Nat) (digits : List Digit) : BoundedState :=
  digits.foldl (boundedStep maximum) ⟨0, false⟩

def Describes (maximum : Nat) (state : BoundedState) (exact : Nat) : Prop :=
  state.value ≤ maximum ∧
    (state.overflow = true → maximum < exact) ∧
    (state.overflow = false → state.value = exact)

/-- The guard detects overflow before multiplication or addition. -/
theorem overflow_guard (maximum value : Nat) (digit : Digit) (enough : 9 ≤ maximum) :
    value > (maximum - digit.val) / 10 ↔ maximum < value * 10 + digit.val := by
  have within : digit.val ≤ maximum := by omega
  have guard : value ≤ (maximum - digit.val) / 10 ↔ value * 10 + digit.val ≤ maximum := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 10)]
    omega
  omega

theorem boundedStep_describes (maximum : Nat) (enough : 9 ≤ maximum)
    (state : BoundedState) (exact : Nat) (digit : Digit)
    (current : Describes maximum state exact) :
    Describes maximum (boundedStep maximum state digit) (exact * 10 + digit.val) := by
  rcases state with ⟨value, flag⟩
  cases flag with
  | false =>
    have same : value = exact := current.2.2 rfl
    subst value
    simp only [boundedStep, Bool.false_eq_true, ↓reduceIte]
    split_ifs with overflow
    · refine ⟨current.1, fun _ => (overflow_guard maximum exact digit enough).1 overflow, ?_⟩
      simp
    · refine ⟨?_, ?_, fun _ => rfl⟩
      · have safe := mt (overflow_guard maximum exact digit enough).2 overflow
        change exact * 10 + digit.val ≤ maximum
        omega
      · simp
  | true =>
    simp only [boundedStep, ↓reduceIte]
    refine ⟨current.1, ?_, ?_⟩
    · have earlier := current.2.1 rfl
      intro _
      omega
    · simp

theorem boundedFold_describes (maximum : Nat) (enough : 9 ≤ maximum)
    (digits : List Digit) (initial : BoundedState) (exact : Nat)
    (current : Describes maximum initial exact) :
    Describes maximum (digits.foldl (boundedStep maximum) initial) (accumulate digits exact) := by
  induction digits generalizing initial exact with
  | nil => exact current
  | cons digit rest ih =>
    exact ih (boundedStep maximum initial digit) (exact * 10 + digit.val)
      (boundedStep_describes maximum enough initial exact digit current)

theorem boundedAccumulate_describes (maximum : Nat) (enough : 9 ≤ maximum)
    (digits : List Digit) :
    Describes maximum (boundedAccumulate maximum digits) (positionalValue digits) := by
  simpa [boundedAccumulate, accumulate_positional] using
    boundedFold_describes maximum enough digits ⟨0, false⟩ 0 (by simp [Describes])

theorem boundedAccumulate_overflow_iff (maximum : Nat) (enough : 9 ≤ maximum)
    (digits : List Digit) :
    (boundedAccumulate maximum digits).overflow = true ↔ maximum < positionalValue digits := by
  have checked := boundedAccumulate_describes maximum enough digits
  constructor
  · exact checked.2.1
  · intro overflow
    cases flag : (boundedAccumulate maximum digits).overflow with
    | true => rfl
    | false =>
      have exactValue := checked.2.2 flag
      have bound := checked.1
      rw [exactValue] at bound
      omega

theorem boundedAccumulate_exact (maximum : Nat) (enough : 9 ≤ maximum)
    (digits : List Digit) (within : positionalValue digits ≤ maximum) :
    (boundedAccumulate maximum digits).value = positionalValue digits := by
  have checked := boundedAccumulate_describes maximum enough digits
  cases flag : (boundedAccumulate maximum digits).overflow with
  | false => exact checked.2.2 flag
  | true => have tooLarge := checked.2.1 flag; omega

def signedValue (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude

theorem signed_minimum (bits : Nat) :
    signedValue true (2 ^ bits) = -(2 ^ bits : Int) := by simp [signedValue]

/-! A small independent character provider exercises mixed scripts without
claiming to reproduce the complete Unicode database. -/

def exampleDecimal : Char → Option Digit
  | '1' => some ⟨1, by decide⟩
  | '٣' => some ⟨3, by decide⟩
  | '０' => some ⟨0, by decide⟩
  | _ => none

example : parse exampleDecimal ['1', '٣'] = some 13 := by decide +kernel
example : parse exampleDecimal ['０', '1', '٣'] = some 13 := by decide +kernel
example : parse exampleDecimal ['1', '³'] = none := by decide +kernel
example : parse exampleDecimal ['1', '٣', 'x'] = none := by decide +kernel
example : parse exampleDecimal [] = none := by decide +kernel
example : (boundedAccumulate 99 [⟨9, by decide⟩, ⟨9, by decide⟩]).overflow = false := by decide +kernel
example : (boundedAccumulate 99 [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]).overflow = true := by decide +kernel
example : (boundedAccumulate 99 [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]).value = 10 := by decide +kernel

#print axioms accumulate_positional
#print axioms ascii_transport
#print axioms overflow_guard
#print axioms boundedAccumulate_overflow_iff
#print axioms boundedAccumulate_exact

end Mettapedia.Data.String.UnicodeDecimal
