import Mettapedia.GSLT.Causality.Responsibility
import Mettapedia.GSLT.Distinction.Constructive.Scale

/-!
# Blame's ratio on the integer scale

`Responsibility.Ratio` is a numerator and a denominator. `Scale.integers` is
the integers with a positive unit: the integer `k` is the rational `k / unit`,
and the discount is the identity. A ratio with positive denominator is that
reading, with the denominator as the unit and the numerator as the value.
The arithmetic stays in `ℕ` and `ℤ`.

`RatReading` is not used. It lands in `ℚ`, and the field and order laws of
that carrier depend on `Classical.choice`. A ratio whose denominator is zero
is not a point of any integer scale, because a scale unit is positive.
`expect []` is such a ratio. Every `responsibilityRatio`, and `blame` of the
uncertain preemption example, has a positive denominator, and the weighted
singleton of `expect` denotes the same point as the ratio it weights.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.BlameScale

open Mettapedia.GSLT.Causality.Responsibility
open Mettapedia.GSLT.Distinction.Constructive

/-- A positive denominator, used as the unit of `Scale.integers`, and a
numerator. -/
structure OnIntegers where
  unit : ℤ
  positive : 0 < unit
  value : ℤ

/-- The integer scale whose unit is this denominator. -/
def OnIntegers.scale (point : OnIntegers) : Scale ℤ :=
  Scale.integers point.unit point.positive

/-- A positive-denominator ratio, read on that scale. -/
def ofRatio (ratio : Ratio) (positive : 0 < ratio.den) : OnIntegers where
  unit := ratio.den
  positive := Int.ofNat_lt.mpr positive
  value := ratio.num

/-- The same rational, stated by cross-multiplication, with no division in `ℚ`. -/
def SamePoint (left right : OnIntegers) : Prop :=
  left.value * right.unit = right.value * left.unit

theorem responsibilityRatio_den_pos (degree : Nat) : 0 < (responsibilityRatio degree).den := by
  unfold responsibilityRatio
  split
  · decide
  · rename_i notZero
    exact Nat.pos_of_ne_zero notZero

/-- **Degree `k` on the integer scale.** Degree 0 is the value 0 on the unit 1.
A positive degree `k` is the value 1 on the unit `k`. -/
theorem responsibility_on_integers (degree : Nat) :
    (ofRatio (responsibilityRatio degree) (responsibilityRatio_den_pos degree)).value =
      (if degree = 0 then 0 else 1 : ℤ) ∧
      (ofRatio (responsibilityRatio degree) (responsibilityRatio_den_pos degree)).unit =
        (if degree = 0 then 1 else degree : ℤ) := by
  cases degree with
  | zero =>
      unfold ofRatio responsibilityRatio
      exact ⟨rfl, rfl⟩
  | succ degree =>
      unfold ofRatio responsibilityRatio
      exact ⟨rfl, rfl⟩

/-- One weighted degree, brought to the common denominator `expect` uses. -/
theorem expect_singleton (weight degree : Nat) :
    expect [(weight, degree)] =
      ⟨weight * (responsibilityRatio degree).num,
        weight * (responsibilityRatio degree).den⟩ := by
  unfold expect
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, lcmAll,
    Nat.lcm_one_right, Nat.div_self (responsibilityRatio_den_pos degree),
    Nat.mul_one, Nat.zero_add]

/-- **A positive weight does not move the point.** `expect` of one weighted
degree denotes the same integer-scale point as that degree's ratio. -/
theorem weighted_singleton_same_point (weight degree : Nat) (weightPos : 0 < weight) :
    SamePoint
      (ofRatio (expect [(weight, degree)])
        (by
          rw [congrArg Ratio.den (expect_singleton weight degree)]
          exact Nat.mul_pos weightPos (responsibilityRatio_den_pos degree)))
      (ofRatio (responsibilityRatio degree) (responsibilityRatio_den_pos degree)) := by
  change ((expect [(weight, degree)]).num : ℤ) * ((responsibilityRatio degree).den : ℤ) =
    ((responsibilityRatio degree).num : ℤ) * ((expect [(weight, degree)]).den : ℤ)
  rw [expect_singleton]
  simp only [Int.natCast_mul]
  rw [Int.mul_assoc]
  rw [Int.mul_left_comm ((responsibilityRatio degree).num : ℤ) (weight : ℤ)
    ((responsibilityRatio degree).den : ℤ)]

/-- **The uncertain example on the scale.** Weight 2 on degree 1 and weight 1
on degree 0 is the value 2 on the unit 3, the ratio `2/3`. -/
theorem uncertain_on_integers :
    (ofRatio (blame ⟨uncertain, 0⟩)
        (by
          rw [congrArg Ratio.den uncertain_blame]
          decide)).value = 2 ∧
      (ofRatio (blame ⟨uncertain, 0⟩)
        (by
          rw [congrArg Ratio.den uncertain_blame]
          decide)).scale.one = 3 := by
  change ((blame ⟨uncertain, 0⟩).num : ℤ) = 2 ∧ ((blame ⟨uncertain, 0⟩).den : ℤ) = 3
  rw [congrArg Ratio.num uncertain_blame, congrArg Ratio.den uncertain_blame]
  exact ⟨rfl, rfl⟩

/-- Nothing to weight: numerator 0, denominator 0. -/
theorem expect_nil : expect [] = ⟨0, 0⟩ := rfl

/-- **A zero denominator is not a scale unit.** `Scale.integers` requires a
positive unit, and `expect []` has denominator 0. -/
theorem expect_nil_not_a_unit (unit : ℤ) (positive : 0 < unit) :
    (Scale.integers unit positive).one ≠ ((expect []).den : ℤ) := by
  rw [expect_nil]
  exact ne_of_gt positive

end Mettapedia.GSLT.Causality.BlameScale
