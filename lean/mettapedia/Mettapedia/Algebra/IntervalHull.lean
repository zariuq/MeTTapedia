import Mathlib.Algebra.Order.Ring.Basic

/-!
# Endpoint hulls for interval multiplication

Multiplication sends two closed intervals into the hull of their four endpoint
products. This common ordered-algebra lemma is used by executable rational
enclosures and real-valued interval certificates alike.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.IntervalHull

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem scalar_mem {lower upper value : R} (scalar : R)
    (membership : lower ≤ value ∧ value ≤ upper) :
    min (scalar * lower) (scalar * upper) ≤ scalar * value ∧
      scalar * value ≤ max (scalar * lower) (scalar * upper) := by
  by_cases nonnegative : 0 ≤ scalar
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left membership.1 nonnegative),
      (mul_le_mul_of_nonneg_left membership.2 nonnegative).trans (le_max_right _ _)⟩
  · have nonpositive : scalar ≤ 0 := le_of_not_ge nonnegative
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left membership.2 nonpositive),
      (mul_le_mul_of_nonpos_left membership.1 nonpositive).trans (le_max_left _ _)⟩

/-- The exact endpoint hull encloses every product of represented values. -/
theorem mul_mem {a b c d x y : R} (left : a ≤ x ∧ x ≤ b) (right : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have bounds : min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
    simpa only [mul_comm y] using scalar_mem y left
  have atLeft := scalar_mem a right
  have atRight := scalar_mem b right
  exact ⟨(le_min ((min_le_left _ _).trans atLeft.1)
      ((min_le_right _ _).trans atRight.1)).trans bounds.1,
    bounds.2.trans (max_le (atLeft.2.trans (le_max_left _ _))
      (atRight.2.trans (le_max_right _ _)))⟩

end Mettapedia.Algebra.IntervalHull
