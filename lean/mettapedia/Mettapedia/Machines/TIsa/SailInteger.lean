import Mathlib.Data.Int.DivMod

/-!
# Termination arithmetic for Sail integer helpers

The x86 model corrects truncating division using the remainder's sign. For a
positive divisor this is Euclidean division. Halving strictly decreases the
absolute value except at the two base cases used by its integer AND helper.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.SailInteger

def floorFromTrunc (left right : Int) : Int :=
  let quotient := left.tdiv right
  let remainder := left.tmod right
  if (decide (0 < right) && decide (0 ≤ remainder)) ||
      (decide (right < 0) && decide (remainder ≤ 0)) then quotient else quotient - 1

theorem floorFromTrunc_positive (left right : Int) (positive : 0 < right) :
    floorFromTrunc left right = left / right := by
  have nonzero : right ≠ 0 := by omega
  have notNegative : ¬right < 0 := by omega
  have remainderNonnegative := Int.emod_nonneg left nonzero
  have remainderBelow := Int.emod_lt_of_pos left positive
  have absoluteRight : (right.natAbs : Int) = right := by omega
  by_cases good : 0 ≤ left ∨ right ∣ left
  · simp [floorFromTrunc, Int.tdiv_eq_ediv, Int.tmod_eq_emod, good,
      positive, notNegative, remainderNonnegative]
  · have notBeyond : ¬right ≤ left % right := by omega
    simp [floorFromTrunc, Int.tdiv_eq_ediv, Int.tmod_eq_emod, good,
      positive, notNegative, absoluteRight, notBeyond, Int.sign_eq_one_of_pos positive]

theorem half_abs_decreases (value : Int) (nonzero : value ≠ 0) (notMinusOne : value ≠ -1) :
    (floorFromTrunc value 2).natAbs < value.natAbs := by
  rw [floorFromTrunc_positive value 2 (by decide)]
  have positiveAbs : 0 < value.natAbs := Int.natAbs_pos.mpr nonzero
  have quotient : (value / 2).natAbs = value.natAbs / 2 +
      if 0 ≤ value ∨ (2 : Int) ∣ value then 0 else 1 := by
    simpa using Int.natAbs_ediv value 2
  rw [quotient]
  by_cases good : 0 ≤ value ∨ (2 : Int) ∣ value
  · rw [if_pos good, Nat.add_zero]
    exact Nat.div_lt_self positiveAbs (by decide)
  · rw [if_neg good]
    have large : 2 < value.natAbs := by
      cases value with
      | ofNat number => exact False.elim (good (Or.inl (Int.natCast_nonneg _)))
      | negSucc number =>
          change 2 < number + 1
          by_cases large : 2 < number + 1
          · exact large
          · have alternatives : number = 0 ∨ number = 1 := by omega
            rcases alternatives with rfl | rfl
            · exact False.elim (notMinusOne rfl)
            · exact False.elim (good (Or.inr (by decide)))
    omega

namespace Controls

example : floorFromTrunc (-3) 2 = -2 := by decide
example : floorFromTrunc (-2) 2 = -1 := by decide
example : floorFromTrunc 3 2 = 1 := by decide
example : (floorFromTrunc (-1) 2).natAbs = (-1 : Int).natAbs := by decide
example : ¬(floorFromTrunc 0 2).natAbs < (0 : Int).natAbs := by decide

end Controls

end Mettapedia.Machines.TIsa.SailInteger
