import Mettapedia.Machines.TIsa.Scalar

/-!
# Explicit 32-bit operation width and 64-bit carrier extension

Operation width and output extension are independent. Signed comparisons and
arithmetic shifts inspect bit 31 for a 32-bit operation, including when the
result carrier is zero-extended. Boolean inputs are never repaired by masking.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa

def low32 (value : Word) : BitVec 32 := value.extractLsb' 0 32

def extend32 (signed : Bool) (value : BitVec 32) : Word :=
  if signed then value.signExtend 64 else value.zeroExtend 64

theorem low32_extend32 (signed : Bool) (value : BitVec 32) : low32 (extend32 signed value) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have within : index < 64 := by omega
  cases signed <;> simp [low32, extend32, bound, within, BitVec.getElem_signExtend]

theorem extend32_idempotent (signed : Bool) (value : Word) :
    extend32 signed (low32 (extend32 signed (low32 value))) = extend32 signed (low32 value) := by
  rw [low32_extend32]

def Scalar.evaluate32 (signedOutput : Bool) : Scalar → List Word → Option Word
  | .immediate value, [] =>
      if value = extend32 signedOutput (low32 value) then some value else none
  | .copy, [value] => some (extend32 signedOutput (low32 value))
  | .binary operation, [left, right] =>
      some (extend32 signedOutput (operation.evaluate (low32 left) (low32 right)))
  | .shift operation amount, [value] =>
      if amount < 32 then some (extend32 signedOutput (operation.evaluate (low32 value) amount)) else none
  | .compare condition, [left, right] =>
      some (booleanWord (condition.evaluate (low32 left) (low32 right)))
  | .isZero, [value] => some (booleanWord (low32 value == 0))
  | .isNonZero, [value] => some (booleanWord (low32 value != 0))
  | .select, [condition, yes, no] =>
      if condition = 0 then some (extend32 signedOutput (low32 no))
      else if condition = 1 then some (extend32 signedOutput (low32 yes)) else none
  | .extract low width, [value] =>
      ((Scalar.extract low width).evaluate [value]).map fun result => extend32 signedOutput (low32 result)
  | _, _ => none

theorem Scalar.evaluate32_compare_boolean (signedOutput : Bool) (condition : Comparison)
    (left right : Word) :
    ∃ result, (Scalar.compare condition).evaluate32 signedOutput [left, right] = some result ∧
      ScalarType.boolean.ValidWord result :=
  ⟨_, rfl, booleanWord_valid _⟩

theorem Scalar.evaluate32_shift_outside (signedOutput : Bool) (operation : Shift)
    (amount : Nat) (value : Word) (outside : 32 ≤ amount) :
    (Scalar.shift operation amount).evaluate32 signedOutput [value] = none := by
  simp [evaluate32, show ¬amount < 32 from Nat.not_lt.mpr outside]

namespace WidthControls

example : (Scalar.binary .add).evaluate32 false [4294967295, 1] = some 0 := by decide

example : (Scalar.binary .sub).evaluate32 false [0, 1] = some 4294967295 := by decide

example : (Scalar.binary .sub).evaluate32 true [0, 1] = some 18446744073709551615 := by decide

example : (Scalar.shift .rightSigned 1).evaluate32 false [4294967295] = some 4294967295 := by decide

example : (Scalar.shift .rightUnsigned 1).evaluate32 false [4294967295] = some 2147483647 := by decide

example : (Scalar.compare .lessSigned).evaluate32 false [4294967295, 0] = some 1 := by decide

example : (Scalar.compare .lessUnsigned).evaluate32 false [4294967295, 0] = some 0 := by decide

example : Scalar.select.evaluate32 false [2, 7, 9] = none := by decide

end WidthControls

end Mettapedia.Machines.TIsa
