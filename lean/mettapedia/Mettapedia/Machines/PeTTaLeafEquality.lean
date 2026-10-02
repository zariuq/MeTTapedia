import Mathlib.Data.Rat.Defs
import Mathlib.Order.Basic

/-!
# PeTTa's equality of numeric leaves

PeTTa's `==` compares numbers by exact value, whatever their representation:
`1` equals `1.0`, `0.0` equals `-0.0`. A NaN equals every NaN, whatever its
bits, and nothing else; IEEE equality would make a NaN unequal even to
itself.

A number is modelled as the runtime holds it: a machine integer, or a float
that is finite (by its exact value, since every finite float is a rational),
infinite, or a NaN with some payload. `valueEq` is the runtime's decision
(`atom_value_eq` in PeTTa, where every representation compares by value):
two floats are IEEE-equal or both NaN, an integer and a float are equal when
the float's exact value is the integer, and two integers when they are equal.

* `valueEq_iff`: the decision is equality of value classes (`cls`), so it is
  an equivalence (`valueEq_refl`, `valueEq_symm`, `valueEq_trans`).
* `hash_compatible`: a hash that is a function of the value class gives
  equal numbers equal hashes; `nan_hash` states the one condition the
  runtime's value hash must meet for that, beside folding the two zeros.
* The value class is the label a term graph's leaves carry for PeTTa's `==`
  (`RationalTermGraph`, whose bisimulation compares labels by equality).

Controls: a NaN equals a NaN of another payload, and neither equals a finite
number; `1` equals `1.0` as a finite float of value 1.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PeTTaLeafEquality

/-- A number as the runtime holds it. -/
inductive Num
  | int (n : ℤ)
  | fin (q : ℚ)
  | posInf
  | negInf
  | nan (payload : ℕ)
  deriving DecidableEq

/-- The value class PeTTa's `==` compares. -/
inductive Cls
  | val (q : ℚ)
  | posInf
  | negInf
  | nan
  deriving DecidableEq

/-- The value class of a number. -/
def cls : Num → Cls
  | .int n => .val n
  | .fin q => .val q
  | .posInf => .posInf
  | .negInf => .negInf
  | .nan _ => .nan

/-- IEEE equality of two floats: equal finite values or the same infinity;
a NaN equals nothing. -/
def ieeeEq : Num → Num → Bool
  | .fin p, .fin q => decide (p = q)
  | .posInf, .posInf => true
  | .negInf, .negInf => true
  | _, _ => false

/-- The runtime's PeTTa equality of two numbers. -/
def valueEq : Num → Num → Bool
  | .int m, .int n => decide (m = n)
  | .int m, .fin q => decide ((m : ℚ) = q)
  | .fin q, .int n => decide (q = (n : ℚ))
  | .int _, _ => false
  | _, .int _ => false
  | .nan _, .nan _ => true
  | x, y => ieeeEq x y

/-- The decision is equality of value classes. -/
theorem valueEq_iff (x y : Num) : valueEq x y = true ↔ cls x = cls y := by
  cases x <;> cases y <;> simp [valueEq, ieeeEq, cls, eq_comm]

theorem valueEq_refl (x : Num) : valueEq x x = true :=
  (valueEq_iff x x).mpr rfl

theorem valueEq_symm {x y : Num} (h : valueEq x y = true) : valueEq y x = true :=
  (valueEq_iff y x).mpr ((valueEq_iff x y).mp h).symm

theorem valueEq_trans {x y z : Num} (hxy : valueEq x y = true)
    (hyz : valueEq y z = true) : valueEq x z = true :=
  (valueEq_iff x z).mpr (((valueEq_iff x y).mp hxy).trans ((valueEq_iff y z).mp hyz))

/-- A hash that is a function of the value class gives equal numbers equal
hashes. -/
theorem hash_compatible {H : Type} (hash : Num → H) (f : Cls → H)
    (hf : ∀ x, hash x = f (cls x)) {x y : Num} (h : valueEq x y = true) :
    hash x = hash y := by
  rw [hf x, hf y, (valueEq_iff x y).mp h]

/-- The condition on NaNs a value hash must meet to be compatible: every NaN
hashes alike, whatever its payload. -/
theorem nan_hash {H : Type} (hash : Num → H)
    (compatible : ∀ x y, valueEq x y = true → hash x = hash y) (p q : ℕ) :
    hash (.nan p) = hash (.nan q) :=
  compatible _ _ (by simp [valueEq])

namespace Controls

/-- NaNs of different payloads are equal. -/
theorem nan_payloads : valueEq (.nan 1) (.nan 2) = true := by decide

/-- A NaN is not a finite number, nor an infinity. -/
theorem nan_not_finite : valueEq (.nan 0) (.fin 0) = false := by decide

theorem nan_not_inf : valueEq (.nan 0) .posInf = false := by decide

/-- IEEE equality alone would refuse a NaN itself. -/
theorem ieee_refuses_nan : ieeeEq (.nan 0) (.nan 0) = false := by decide

/-- An integer and a float of the same exact value are equal. -/
theorem int_float : valueEq (.int 1) (.fin 1) = true := by decide

/-- An integer and a float of a different value are not. -/
theorem int_float_ne : valueEq (.int 1) (.fin 2) = false := by decide

end Controls

end Mettapedia.Machines.PeTTaLeafEquality
