import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuleCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16

/-! Exact unbounded integer and occurrence-ID readings for the compiled
CHR data. The existing radix nibble codec is reused. Noncanonical spellings,
including leading zero digits and negative zero, receive no reading. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.ScalarReading

open Mettapedia.OSLF.MeTTaIL Syntax

def digit? (source : Pattern) : Option Nat := (Radix16Codec.readNibble? source).map Fin.val

private theorem digit_roundTrip (digit : Nat) (bounded : digit < 16) :
    digit? (.apply ("R16Nibble" ++ toString digit) []) = some digit := by
  change (Radix16Codec.readNibble? (Radix16Codec.nibble ⟨digit, bounded⟩)).map Fin.val = some digit
  rw [Radix16Codec.readNibble?_nibble]
  rfl

private theorem digits_list_roundTrip (values : List Nat) (bounded : ∀ value ∈ values, value < 16) :
    (values.map (fun digit => Pattern.apply ("R16Nibble" ++ toString digit) [])).mapM digit? = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    have firstRead := digit_roundTrip first (bounded first (by simp))
    have tailRead := ih (fun value member => bounded value (List.mem_cons_of_mem first member))
    simp only [List.map_cons, List.mapM_cons, firstRead, tailRead]
    rfl

def rawDigits? : Pattern → Option Nat
  | .collection .vec values none => Nat.ofDigits 16 <$> values.mapM digit?
  | _ => none

theorem rawDigits_roundTrip (value : Nat) : rawDigits? (digits value) = some value := by
  change (Nat.ofDigits 16 <$>
    ((Nat.digits 16 value).map (fun digit => Pattern.apply ("R16Nibble" ++ toString digit) [])).mapM digit?) = some value
  rw [digits_list_roundTrip]
  · simp [Nat.ofDigits_digits]
  · intro digit member
    exact Nat.digits_lt_base (by decide) member

def digits? (source : Pattern) : Option Nat := do
  let value ← rawDigits? source
  if digits value = source then some value else none

theorem digits_roundTrip (value : Nat) : digits? (digits value) = some value := by
  simp [digits?, rawDigits_roundTrip]

theorem digits_exact {source : Pattern} {value : Nat} (read : digits? source = some value) :
    digits value = source := by
  unfold digits? at read
  cases found : rawDigits? source with
  | none => simp [found] at read
  | some actual =>
    by_cases canonical : digits actual = source
    · have same : actual = value := by simpa [found, canonical] using read
      exact same ▸ canonical
    · simp [found, canonical] at read

def integer? : Pattern → Option Int
  | .apply "ChrIntegerDigits" [.apply "ChrNonnegative" [], magnitude] => Int.ofNat <$> digits? magnitude
  | .apply "ChrIntegerDigits" [.apply "ChrNegative" [], magnitude] => do
      let value ← digits? magnitude
      if value = 0 then none else some (-Int.ofNat value)
  | _ => none

theorem integer_roundTrip (value : Int) : integer? (integer value) = some value := by
  cases value with
  | ofNat value =>
      have positive : ¬ (Int.ofNat value < 0) := by
        change ¬ ((value : Int) < 0)
        exact not_lt_of_ge (Int.natCast_nonneg _)
      rw [integer, if_neg positive]
      change (Int.ofNat <$> digits? (digits value)) = some (Int.ofNat value)
      rw [digits_roundTrip]
      rfl
  | negSucc value =>
      simp [integer, integer?, digits_roundTrip]
      omega

def occurrence? : Pattern → Option Nat
  | .apply "ChrOccurrenceNumber" [magnitude] => digits? magnitude
  | _ => none

theorem occurrence_roundTrip (value : Nat) : occurrence? (occurrenceRef value) = some value := by
  simp [occurrence?, occurrenceRef, digits_roundTrip]

theorem occurrence_injective : Function.Injective occurrenceRef := by
  intro first second same
  have read := congrArg occurrence? same
  simpa only [occurrence_roundTrip, Option.some.injEq] using read

theorem integer_injective : Function.Injective integer := by
  intro first second same
  have read := congrArg integer? same
  simpa only [integer_roundTrip, Option.some.injEq] using read

theorem malformed_encodings :
    digits? (.collection .vec [.apply "R16Nibble0" []] none) = none ∧
    rawDigits? (.collection .vec [.apply "R16Nibble16" []] none) = none ∧
    integer? (.apply "ChrIntegerDigits" [.apply "ChrNegative" [], digits 0]) = none ∧
    occurrence? (.apply "ChrIntegerDigits" [.apply "ChrNonnegative" [], digits 1]) = none := by
  decide +kernel

#print axioms integer_roundTrip
#print axioms occurrence_injective

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.ScalarReading
