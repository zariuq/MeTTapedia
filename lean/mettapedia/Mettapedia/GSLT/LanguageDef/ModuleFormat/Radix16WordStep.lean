import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Word

/-! The existing canonical radix representation follows division by
sixteen, with zero represented by the empty digit sequence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Word

open Mettapedia.OSLF.MeTTaIL Syntax

theorem digits_zero : Nat.digits 16 0 = [] := Nat.digits_zero 16

theorem digits_step (number : Nat) (positive : 0 < number) :
    Nat.digits 16 number = number % 16 :: Nat.digits 16 (number / 16) :=
  Nat.digits_of_two_le_of_pos (by decide) positive

theorem encoding_step (number : Nat) (positive : 0 < number) :
    encode number = .collection .vec
      (.apply ("R16Nibble" ++ toString (number % 16)) [] ::
        (Nat.digits 16 (number / 16)).map (fun digit => .apply ("R16Nibble" ++ toString digit) [])) none := by
  simp only [encode, digits_step number positive, List.map_cons]

theorem quotient_smaller (number : Nat) (positive : 0 < number) : number / 16 < number :=
  Nat.div_lt_self positive (by decide)

example : Nat.digits 16 16 = [0, 1] := by decide +kernel
example : Nat.digits 16 16 ≠ [1, 0] := by decide +kernel

#print axioms encoding_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Word
