import Mathlib.Data.Finset.Basic

/-!
# Scalar interface for the transform-native machine profile

Scalar operations act on explicit word inputs. Registers, memory, control and
publication remain transform resources and effects. This module introduces no
machine interpreter or second state space.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa

abbrev Word := BitVec 64

inductive ScalarType where
  | u64
  | u32z
  | i32s
  | boolean
  | pointer (region : Nat)
  deriving DecidableEq, Repr

/-- Pointer ownership is a separate region/capability obligation. -/
def ScalarType.ValidWord : ScalarType → Word → Prop
  | .u64, _ => True
  | .u32z, value => value.toNat < 2 ^ 32
  | .i32s, value => (value.extractLsb' 0 32).signExtend 64 = value
  | .boolean, value => value = 0 ∨ value = 1
  | .pointer _, _ => True

def booleanWord (value : Bool) : Word := if value then 1 else 0

theorem booleanWord_valid (value : Bool) :
    ScalarType.boolean.ValidWord (booleanWord value) := by
  cases value <;> simp [ScalarType.ValidWord, booleanWord]

inductive Binary where
  | add | sub | band | bor | bxor | mulLo
  deriving DecidableEq, Repr

def Binary.evaluate {width : Nat} : Binary → BitVec width → BitVec width → BitVec width
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .band, left, right => left &&& right
  | .bor, left, right => left ||| right
  | .bxor, left, right => left ^^^ right
  | .mulLo, left, right => left * right

inductive Shift where
  | left | rightUnsigned | rightSigned
  deriving DecidableEq, Repr

def Shift.evaluate {width : Nat} : Shift → BitVec width → Nat → BitVec width
  | .left, value, amount => value <<< amount
  | .rightUnsigned, value, amount => value >>> amount
  | .rightSigned, value, amount => value.sshiftRight amount

inductive Comparison where
  | equal | notEqual | lessUnsigned | lessEqualUnsigned | lessSigned | lessEqualSigned
  deriving DecidableEq, Repr

def Comparison.evaluate {width : Nat} : Comparison → BitVec width → BitVec width → Bool
  | .equal, left, right => left == right
  | .notEqual, left, right => left != right
  | .lessUnsigned, left, right => decide (left < right)
  | .lessEqualUnsigned, left, right => decide (left ≤ right)
  | .lessSigned, left, right => left.slt right
  | .lessEqualSigned, left, right => left.sle right

/-- A scalar operation is the extra executable algebra used by transform rules.
Loads/stores are resource operations, not hidden scalar callbacks. -/
inductive Scalar where
  | immediate (value : Word)
  | copy
  | binary (operation : Binary)
  | shift (operation : Shift) (amount : Nat)
  | extract (low width : Nat)
  | address (scaleLog2 : Nat) (displacement : Word)
  | compare (condition : Comparison)
  | isZero
  | isNonZero
  | select
  deriving DecidableEq, Repr

def Scalar.arity : Scalar → Nat
  | .immediate _ => 0
  | .copy | .shift .. | .extract .. | .isZero | .isNonZero => 1
  | .binary _ | .address .. | .compare _ => 2
  | .select => 3

def Scalar.evaluate : Scalar → List Word → Option Word
  | .immediate value, [] => some value
  | .copy, [value] => some value
  | .binary operation, [left, right] => some (operation.evaluate left right)
  | .shift operation amount, [value] =>
      if amount < 64 then some (operation.evaluate value amount) else none
  | .extract low width, [value] =>
      if 0 < width ∧ low + width ≤ 64 then
        some (BitVec.ofNat 64 ((value.toNat / 2 ^ low) % 2 ^ width))
      else none
  | .address scaleLog2 displacement, [base, index] =>
      if scaleLog2 ≤ 3 then some (base + (index <<< scaleLog2) + displacement) else none
  | .compare condition, [left, right] => some (booleanWord (condition.evaluate left right))
  | .isZero, [value] => some (booleanWord (value == 0))
  | .isNonZero, [value] => some (booleanWord (value != 0))
  | .select, [condition, yes, no] =>
      if condition = 0 then some no else if condition = 1 then some yes else none
  | _, _ => none

theorem Scalar.compare_boolean (condition : Comparison) (left right : Word) :
    ∃ result, (Scalar.compare condition).evaluate [left, right] = some result ∧
      ScalarType.boolean.ValidWord result :=
  ⟨_, rfl, booleanWord_valid _⟩

theorem Scalar.invalid_shift (operation : Shift) (amount : Nat) (value : Word)
    (outside : 64 ≤ amount) : (.shift operation amount : Scalar).evaluate [value] = none := by
  simp [evaluate, show ¬amount < 64 from Nat.not_lt.mpr outside]

theorem Scalar.non_boolean_selection (condition yes no : Word)
    (notZero : condition ≠ 0) (notOne : condition ≠ 1) :
    Scalar.select.evaluate [condition, yes, no] = none := by
  change (if condition = 0 then some no else if condition = 1 then some yes else none) = none
  rw [if_neg notZero, if_neg notOne]

theorem Scalar.selection_zero (yes no : Word) :
    Scalar.select.evaluate [0, yes, no] = some no := by
  simp [evaluate]

theorem Scalar.selection_one (yes no : Word) :
    Scalar.select.evaluate [1, yes, no] = some yes := by
  simp [evaluate]

namespace ScalarControls

example : (Scalar.binary .add).evaluate [18446744073709551615, 1] = some 0 := by decide

example : (Scalar.binary .sub).evaluate [0, 1] = some 18446744073709551615 := by decide

example : (Scalar.shift .rightSigned 1).evaluate [18446744073709551615] =
    some 18446744073709551615 := by decide

example : (Scalar.shift .rightUnsigned 1).evaluate [18446744073709551615] =
    some 9223372036854775807 := by decide

example : (Scalar.compare .lessSigned).evaluate [18446744073709551615, 0] = some 1 := by decide

example : (Scalar.compare .lessUnsigned).evaluate [18446744073709551615, 0] = some 0 := by decide

example : Scalar.select.evaluate [2, 7, 9] = none := by decide

example : (Scalar.extract 63 2).evaluate [0] = none := by decide

example : (Scalar.binary .add).evaluate [1] = none := by decide

end ScalarControls

end Mettapedia.Machines.TIsa
