import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Rat.Defs

/-!
# A nilpotent is never an infinitesimal of an ordered ring

Two different things are called infinitesimal, and they are not the same thing.

* A *nilpotent* infinitesimal satisfies `ε * ε = 0` with `ε ≠ 0`.  The dual
  numbers `R[ε]` are the standard example, and they are what forward-mode
  automatic differentiation computes in.
* An *invertible* infinitesimal is a nonzero element smaller than every
  positive element of the base field, with a multiplicative inverse — which is
  then larger than every element of the base field.  These are what a
  non-Archimedean ordered field has.

The distinction is not a matter of emphasis: **no ring carrying a nonzero
nilpotent admits a compatible linear order at all.**  `sq_ne_zero_of_ne_zero`
is the one-line reason, and `dualNumber_rat_has_no_compatible_order` is the
instance.  So a development that wants ordered infinitesimals cannot use dual
numbers, and a development that wants automatic differentiation is not thereby
doing non-Archimedean arithmetic.

The invertible side is built in `LevelField.lean`, where `omInv * omInv ≠ 0`
is proved for the infinitesimal there — the exact negation of the dual-number
law.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

/-- **In a linearly ordered ring a nonzero element has nonzero square.**  Both
signs give a positive square, so nothing nonzero is nilpotent. -/
theorem sq_ne_zero_of_ne_zero {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] {x : R} (hx : x ≠ 0) : x * x ≠ 0 := by
  rcases lt_trichotomy x 0 with h | h | h
  · exact ne_of_gt (mul_pos_of_neg_of_neg h h)
  · exact absurd h hx
  · exact ne_of_gt (mul_pos h h)

/-- A ring with a nonzero nilpotent carries no compatible linear order. -/
theorem no_compatible_order_of_nilpotent {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] {x : R} (hx : x ≠ 0) (hnil : x * x = 0) : False :=
  sq_ne_zero_of_ne_zero hx hnil

/-! ## The dual numbers are the instance -/

open DualNumber TrivSqZeroExt

/-- The dual unit is not zero: its second component is `1`. -/
theorem dualNumber_eps_ne_zero : (eps : DualNumber ℚ) ≠ 0 := by
  intro h
  have hsnd := congrArg TrivSqZeroExt.snd h
  rw [snd_eps, snd_zero] at hsnd
  exact one_ne_zero hsnd

/-- And it is nilpotent. -/
theorem dualNumber_eps_mul_eps : (eps : DualNumber ℚ) * eps = 0 :=
  eps_mul_eps

/-- **The dual numbers over the rationals admit no compatible linear order.**
So the nilpotent infinitesimal of automatic differentiation is not an
infinitesimal of any ordered ring, and cannot be compared with the rationals
at all. -/
theorem dualNumber_rat_has_no_compatible_order
    [LinearOrder (DualNumber ℚ)] [IsStrictOrderedRing (DualNumber ℚ)] : False :=
  no_compatible_order_of_nilpotent dualNumber_eps_ne_zero dualNumber_eps_mul_eps

end Mettapedia.Algebra.Order.Infinitesimal

#print axioms Mettapedia.Algebra.Order.Infinitesimal.sq_ne_zero_of_ne_zero
#print axioms Mettapedia.Algebra.Order.Infinitesimal.dualNumber_eps_ne_zero
#print axioms Mettapedia.Algebra.Order.Infinitesimal.dualNumber_rat_has_no_compatible_order
