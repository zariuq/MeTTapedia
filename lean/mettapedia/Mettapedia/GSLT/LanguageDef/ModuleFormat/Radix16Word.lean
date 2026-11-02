import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16
import Mathlib.Data.Nat.Digits.Defs

/-! Unbounded natural-number words reuse the authored radix-nibble codec.
The exact reader rejects noncanonical digit sequences while the raw reader
supplies the round-trip and injectivity proofs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Word

open Mettapedia.OSLF.MeTTaIL Syntax

def encode (number : Nat) : Pattern := .collection .vec
  ((Nat.digits 16 number).map fun digit => .apply ("R16Nibble" ++ toString digit) []) none

def digit? (source : Pattern) : Option Nat := (Radix16Codec.readNibble? source).map Fin.val

theorem digit_roundTrip (digit : Nat) (bounded : digit < 16) :
    digit? (.apply ("R16Nibble" ++ toString digit) []) = some digit := by
  change (Radix16Codec.readNibble? (Radix16Codec.nibble ⟨digit, bounded⟩)).map Fin.val = some digit
  rw [Radix16Codec.readNibble?_nibble]
  rfl

theorem list_roundTrip (numbers : List Nat) (bounded : ∀ number ∈ numbers, number < 16) :
    (numbers.map (fun digit => Pattern.apply ("R16Nibble" ++ toString digit) [])).mapM digit? = some numbers := by
  induction numbers with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, List.mapM_cons, digit_roundTrip first (bounded first List.mem_cons_self),
      ih (fun number member => bounded number (List.mem_cons_of_mem first member))]
    rfl

def rawDecode? : Pattern → Option Nat
  | .collection .vec numbers none => Nat.ofDigits 16 <$> numbers.mapM digit?
  | _ => none

theorem raw_roundTrip (number : Nat) : rawDecode? (encode number) = some number := by
  change (Nat.ofDigits 16 <$>
    ((Nat.digits 16 number).map (fun digit => Pattern.apply ("R16Nibble" ++ toString digit) [])).mapM digit?) = some number
  rw [list_roundTrip]
  · simp [Nat.ofDigits_digits]
  · intro digit member
    exact Nat.digits_lt_base (by decide) member

def decode? (source : Pattern) : Option Nat := do
  let number ← rawDecode? source
  if encode number = source then some number else none

theorem roundTrip (number : Nat) : decode? (encode number) = some number := by
  simp [decode?, raw_roundTrip]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have read := congrArg rawDecode? same
  simpa only [raw_roundTrip, Option.some.injEq] using read

theorem decode_exact {source : Pattern} {number : Nat} (accepted : decode? source = some number) :
    encode number = source := by
  unfold decode? at accepted
  cases found : rawDecode? source with
  | none => simp [found] at accepted
  | some actual =>
    by_cases canonical : encode actual = source
    · have same : actual = number := by simpa [found, canonical] using accepted
      exact same ▸ canonical
    · simp [found, canonical] at accepted

example : decode? (.collection .vec [.apply "R16Nibble0" []] none) = none := by decide_cbv
example : rawDecode? (.collection .vec [.apply "R16Nibble16" []] none) = none := by decide_cbv

#print axioms encode_injective

end Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Word
