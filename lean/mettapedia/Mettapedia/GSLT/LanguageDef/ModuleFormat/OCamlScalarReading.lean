import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProgramCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Word

/-! Exact readings for the compiler's existing literals and code/tag
references. Distinct source literals and constructor identities cannot
collide in compiled pattern matching.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem digits_word (number : Nat) : digits number = Radix16Word.encode number := rfl

theorem digits_injective : Function.Injective digits := by
  intro first second same
  exact Radix16Word.encode_injective same

def byteCode (byte : UInt8) : Pattern := node "MlByteValue"
  [node ("R16Nibble" ++ toString (byte.toNat / 16)), node ("R16Nibble" ++ toString (byte.toNat % 16))]

def readByte? : Pattern → Option UInt8
  | .apply "MlByteValue" [high, low] => do
      let first ← Radix16Word.digit? high
      let second ← Radix16Word.digit? low
      let number := 16 * first + second
      if number < 256 then some (UInt8.ofNat number) else none
  | _ => none

theorem byte_roundTrip (byte : UInt8) : readByte? (byteCode byte) = some byte := by
  have bounded : byte.toNat < 256 := byte.toNat_lt_size
  have high : byte.toNat / 16 < 16 := by omega
  have low : byte.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have combine : 16 * (byte.toNat / 16) + byte.toNat % 16 = byte.toNat := by omega
  simp only [byteCode, node, readByte?, Radix16Word.digit_roundTrip _ high,
    Radix16Word.digit_roundTrip _ low, Option.bind_eq_bind, Option.bind_some, combine, bounded, if_true]
  simp

theorem bytes_roundTrip (bytes : List UInt8) : (bytes.map byteCode).mapM readByte? = some bytes := by
  induction bytes with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, List.mapM_cons, byte_roundTrip, ih]
    rfl

def readLiteral? : Pattern → Option OCaml.Literal
  | .apply "MlInteger" [.apply "MlNonnegative" [], magnitude] =>
      (fun number => .integer (Int.ofNat number)) <$> Radix16Word.decode? magnitude
  | .apply "MlInteger" [.apply "MlNegative" [], magnitude] => do
      let number ← Radix16Word.decode? magnitude
      if number = 0 then none else some (.integer (-Int.ofNat number))
  | .apply "MlTrue" [] => some (.boolean true)
  | .apply "MlFalse" [] => some (.boolean false)
  | .apply "MlUnit" [] => some .unit
  | .apply "MlNil" [] => some .nil
  | .apply "MlString" [.collection .vec bytes none] => OCaml.Literal.string <$> bytes.mapM readByte?
  | _ => none

theorem literal_roundTrip (datum : OCaml.Literal) : readLiteral? (literal datum) = some datum := by
  cases datum with
  | integer number =>
    cases number with
    | ofNat number =>
      have nonnegative : ¬ (Int.ofNat number < 0) := not_lt_of_ge (Int.natCast_nonneg number)
      rw [literal, if_neg nonnegative]
      change (fun number => OCaml.Literal.integer (Int.ofNat number)) <$>
        Radix16Word.decode? (Radix16Word.encode number) = some (.integer (Int.ofNat number))
      rw [Radix16Word.roundTrip]
      rfl
    | negSucc number =>
      have negative : Int.negSucc number < 0 := by omega
      rw [literal, if_pos negative]
      change ((Radix16Word.decode? (Radix16Word.encode (number + 1))).bind fun magnitude =>
        if magnitude = 0 then none else some (OCaml.Literal.integer (-Int.ofNat magnitude))) =
          some (.integer (Int.negSucc number))
      rw [Radix16Word.roundTrip]
      simp [Int.negSucc_eq]
  | boolean value => cases value <;> simp [literal, node, readLiteral?]
  | unit => simp only [literal, node, readLiteral?]
  | nil => simp only [literal, node, readLiteral?]
  | string bytes =>
    change OCaml.Literal.string <$> (bytes.map byteCode).mapM readByte? = some (.string bytes)
    rw [bytes_roundTrip]
    rfl

theorem literal_injective : Function.Injective literal := by
  intro first second same
  have read := congrArg readLiteral? same
  simpa only [literal_roundTrip, Option.some.injEq] using read

def readCode? : Pattern → Option Nat
  | .apply "MlCodeNumber" [word] => Radix16Word.decode? word
  | _ => none

theorem code_roundTrip (reference : Nat) : readCode? (code reference) = some reference :=
  Radix16Word.roundTrip reference

theorem code_injective : Function.Injective code := by
  intro first second same
  have read := congrArg readCode? same
  simpa only [code_roundTrip, Option.some.injEq] using read

theorem tag_injective {firstType firstConstructor secondType secondConstructor : Nat}
    (same : tag firstType firstConstructor = tag secondType secondConstructor) :
    firstType = secondType ∧ firstConstructor = secondConstructor := by
  have arguments := (Pattern.apply.inj same).2
  have both := List.cons.inj arguments
  exact ⟨digits_injective both.1, digits_injective (List.cons.inj both.2).1⟩

example : readLiteral? (node "MlInteger" [node "MlNegative", digits 0]) = none := by decide_cbv
example : literal (.integer 7) ≠ literal (.integer (-7)) := by decide_cbv
example : tag 0 1 ≠ tag 0 2 := by decide_cbv

#print axioms literal_injective
#print axioms code_injective
#print axioms tag_injective

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
