import Mettapedia.Algebra.IntervalHull
import Mettapedia.Algorithms.CertifiedLogarithm
import Mathlib.Tactic

/-!
# Executable real circuits with rational enclosures

Rational literals, addition, multiplication and positive rational logarithms
have exact real meanings and executable rational bounds. Disjoint bounds
certify ordering; equal point bounds certify equality. Overlapping bounds
leave the comparison unresolved. Raw circuit syntax is not asserted to be a
semiring: its real interpretation supplies the algebraic laws.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.CertifiedRealCircuit

structure Interval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq

namespace Interval

def Contains (interval : Interval) (value : ℝ) : Prop :=
  (interval.lower : ℝ) ≤ value ∧ value ≤ (interval.upper : ℝ)

def point (value : ℚ) : Interval := ⟨value, value⟩
def add (left right : Interval) : Interval :=
  ⟨left.lower + right.lower, left.upper + right.upper⟩

def multiply (left right : Interval) : Interval :=
  ⟨min (min (left.lower * right.lower) (left.lower * right.upper))
      (min (left.upper * right.lower) (left.upper * right.upper)),
    max (max (left.lower * right.lower) (left.lower * right.upper))
      (max (left.upper * right.lower) (left.upper * right.upper))⟩

theorem contains_point (value : ℚ) : (point value).Contains (value : ℝ) := ⟨le_rfl, le_rfl⟩

theorem contains_add {left right : Interval} {x y : ℝ}
    (leftBounds : left.Contains x) (rightBounds : right.Contains y) :
    (add left right).Contains (x + y) := by
  simpa only [Contains, add, Rat.cast_add] using
    And.intro (add_le_add leftBounds.1 rightBounds.1)
      (add_le_add leftBounds.2 rightBounds.2)

theorem contains_multiply {left right : Interval} {x y : ℝ}
    (leftBounds : left.Contains x) (rightBounds : right.Contains y) :
    (multiply left right).Contains (x * y) := by
  simpa only [Contains, multiply, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using
    Mettapedia.Algebra.IntervalHull.mul_mem leftBounds rightBounds

def compare (left right : Interval) : Option Ordering :=
  if left.upper < right.lower then some .lt
  else if right.upper < left.lower then some .gt
  else if left.lower = left.upper ∧ right.lower = right.upper ∧ left.lower = right.lower
    then some .eq
  else none

theorem compare_lt_sound {left right : Interval} {x y : ℝ}
    (leftBounds : left.Contains x) (rightBounds : right.Contains y)
    (compared : compare left right = some .lt) : x < y := by
  have separated : left.upper < right.lower := by
    unfold compare at compared
    split_ifs at compared <;> simp_all
  have realSeparated : (left.upper : ℝ) < (right.lower : ℝ) := by exact_mod_cast separated
  exact lt_of_le_of_lt leftBounds.2 (lt_of_lt_of_le realSeparated rightBounds.1)

theorem compare_gt_sound {left right : Interval} {x y : ℝ}
    (leftBounds : left.Contains x) (rightBounds : right.Contains y)
    (compared : compare left right = some .gt) : y < x := by
  have separated : right.upper < left.lower := by
    unfold compare at compared
    split_ifs at compared <;> simp_all
  have realSeparated : (right.upper : ℝ) < (left.lower : ℝ) := by exact_mod_cast separated
  exact lt_of_le_of_lt rightBounds.2 (lt_of_lt_of_le realSeparated leftBounds.1)

theorem compare_eq_sound {left right : Interval} {x y : ℝ}
    (leftBounds : left.Contains x) (rightBounds : right.Contains y)
    (compared : compare left right = some .eq) : x = y := by
  have points : left.lower = left.upper ∧ right.lower = right.upper ∧
      left.lower = right.lower := by
    unfold compare at compared
    split_ifs at compared with _ _ pointBounds
    · cases compared
    · cases compared
    · exact pointBounds
  have leftExact : x = (left.lower : ℝ) := by
    exact le_antisymm (points.1 ▸ leftBounds.2) leftBounds.1
  have rightExact : y = (right.lower : ℝ) := by
    exact le_antisymm (points.2.1 ▸ rightBounds.2) rightBounds.1
  rw [leftExact, rightExact, points.2.2]

theorem positive_separation : compare ⟨0, 1⟩ ⟨2, 3⟩ = some .lt := by decide +kernel
theorem overlapping_is_unresolved : compare ⟨0, 2⟩ ⟨1, 3⟩ = none := by decide +kernel
theorem equal_points : compare (point 2) (point 2) = some .eq := by decide +kernel
theorem same_wide_interval_is_unresolved : compare ⟨0, 1⟩ ⟨0, 1⟩ = none := by decide +kernel

theorem positive_width_is_unresolved (interval : Interval) (wide : interval.lower < interval.upper) :
    compare interval interval = none := by
  simp [compare, not_lt_of_ge wide.le, ne_of_lt wide]

end Interval

inductive Circuit where
  | rational : ℚ → Circuit
  | add : Circuit → Circuit → Circuit
  | multiply : Circuit → Circuit → Circuit
  | log : {input : ℚ // 0 < input} → Circuit
  deriving DecidableEq

namespace Circuit

noncomputable def denote : Circuit → ℝ
  | .rational value => value
  | .add left right => denote left + denote right
  | .multiply left right => denote left * denote right
  | .log input => Real.log (input.1 : ℝ)

/-- The circuit operations satisfy real-algebra laws after interpretation. -/
theorem denote_add_associative (first second third : Circuit) :
    denote (.add (.add first second) third) =
      denote (.add first (.add second third)) := add_assoc _ _ _

theorem denote_add_commutative (left right : Circuit) :
    denote (.add left right) = denote (.add right left) := add_comm _ _

theorem denote_add_zero (value : Circuit) :
    denote (.add (.rational 0) value) = denote value ∧
      denote (.add value (.rational 0)) = denote value := by
  simp [denote]

theorem denote_multiply_associative (first second third : Circuit) :
    denote (.multiply (.multiply first second) third) =
      denote (.multiply first (.multiply second third)) := mul_assoc _ _ _

theorem denote_multiply_commutative (left right : Circuit) :
    denote (.multiply left right) = denote (.multiply right left) := mul_comm _ _

theorem denote_multiply_one (value : Circuit) :
    denote (.multiply (.rational 1) value) = denote value ∧
      denote (.multiply value (.rational 1)) = denote value := by
  simp [denote]

theorem denote_multiply_zero (value : Circuit) :
    denote (.multiply (.rational 0) value) = 0 ∧
      denote (.multiply value (.rational 0)) = 0 := by
  simp [denote]

theorem denote_multiply_distributes_left (first second third : Circuit) :
    denote (.multiply first (.add second third)) =
      denote (.add (.multiply first second) (.multiply first third)) := mul_add _ _ _

theorem denote_multiply_distributes_right (first second third : Circuit) :
    denote (.multiply (.add first second) third) =
      denote (.add (.multiply first third) (.multiply second third)) := add_mul _ _ _

/-- Equal real meanings do not identify different circuit codes. -/
theorem rational_sum_code_is_distinct :
    Circuit.add (.rational 0) (.rational 1) ≠ .rational 1 ∧
      denote (.add (.rational 0) (.rational 1)) = denote (.rational 1) := by
  constructor
  · decide +kernel
  · simp [denote]

def enclose (terms : Nat) : Circuit → Interval
  | .rational value => Interval.point value
  | .add left right => Interval.add (enclose terms left) (enclose terms right)
  | .multiply left right => Interval.multiply (enclose terms left) (enclose terms right)
  | .log input =>
      ⟨CertifiedLogarithm.approximation input.1 terms - CertifiedLogarithm.radius input.1 terms,
        CertifiedLogarithm.approximation input.1 terms + CertifiedLogarithm.radius input.1 terms⟩

theorem enclosure_sound (terms : Nat) (circuit : Circuit) :
    (enclose terms circuit).Contains (denote circuit) := by
  induction circuit with
  | rational value => exact Interval.contains_point value
  | add left right leftIH rightIH => exact Interval.contains_add leftIH rightIH
  | multiply left right leftIH rightIH => exact Interval.contains_multiply leftIH rightIH
  | log input => exact ⟨CertifiedLogarithm.lower_bound input.1 input.2 terms,
      CertifiedLogarithm.upper_bound input.1 input.2 terms⟩

theorem comparison_lt_sound (terms : Nat) (left right : Circuit)
    (compared : Interval.compare (enclose terms left) (enclose terms right) = some .lt) :
    denote left < denote right :=
  Interval.compare_lt_sound (enclosure_sound terms left) (enclosure_sound terms right) compared

theorem comparison_gt_sound (terms : Nat) (left right : Circuit)
    (compared : Interval.compare (enclose terms left) (enclose terms right) = some .gt) :
    denote right < denote left :=
  Interval.compare_gt_sound (enclosure_sound terms left) (enclosure_sound terms right) compared

theorem comparison_eq_sound (terms : Nat) (left right : Circuit)
    (compared : Interval.compare (enclose terms left) (enclose terms right) = some .eq) :
    denote left = denote right :=
  Interval.compare_eq_sound (enclosure_sound terms left) (enclosure_sound terms right) compared

theorem endpoints_tendsto (circuit : Circuit) :
    Filter.Tendsto (fun n => ((enclose n circuit).lower : ℝ))
      Filter.atTop (nhds (denote circuit)) ∧
    Filter.Tendsto (fun n => ((enclose n circuit).upper : ℝ))
      Filter.atTop (nhds (denote circuit)) := by
  induction circuit with
  | rational value => exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  | add left right leftIH rightIH =>
      simpa only [enclose, Interval.add, denote, Rat.cast_add] using
        And.intro (leftIH.1.add rightIH.1) (leftIH.2.add rightIH.2)
  | multiply left right leftIH rightIH =>
      have low := ((leftIH.1.mul rightIH.1).min (leftIH.1.mul rightIH.2)).min
        ((leftIH.2.mul rightIH.1).min (leftIH.2.mul rightIH.2))
      have high := ((leftIH.1.mul rightIH.1).max (leftIH.1.mul rightIH.2)).max
        ((leftIH.2.mul rightIH.1).max (leftIH.2.mul rightIH.2))
      simpa only [enclose, Interval.multiply, denote, Rat.cast_min, Rat.cast_max,
        Rat.cast_mul, min_self, max_self] using And.intro low high
  | log input =>
      have approximation := CertifiedLogarithm.approximation_tendsto input.1 input.2
      have radius := CertifiedLogarithm.radius_tendsto_zero input.1 input.2
      simpa only [enclose, denote, Rat.cast_sub, Rat.cast_add, sub_zero, add_zero] using
        And.intro (approximation.sub radius) (approximation.add radius)

/-- Every strict comparison eventually has a rational separation certificate.
There is no corresponding blanket termination claim for equality. -/
theorem comparison_lt_eventually (left right : Circuit) (ordered : denote left < denote right) :
    ∀ᶠ n : Nat in Filter.atTop,
      Interval.compare (enclose n left) (enclose n right) = some .lt := by
  have separated := (endpoints_tendsto left).2.eventually_lt
    (endpoints_tendsto right).1 ordered
  filter_upwards [separated] with n separatedAt
  have rationalSeparation : (enclose n left).upper < (enclose n right).lower := by
    exact_mod_cast separatedAt
  simp [Interval.compare, rationalSeparation]

theorem comparison_gt_eventually (left right : Circuit) (ordered : denote right < denote left) :
    ∀ᶠ n : Nat in Filter.atTop,
      Interval.compare (enclose n left) (enclose n right) = some .gt := by
  have separated := (endpoints_tendsto right).2.eventually_lt
    (endpoints_tendsto left).1 ordered
  filter_upwards [separated] with n separatedAt
  have rationalSeparation : (enclose n right).upper < (enclose n left).lower := by
    exact_mod_cast separatedAt
  have firstImpossible : ¬ (enclose n left).upper < (enclose n right).lower := by
    intro contrary
    have reversed := Interval.compare_lt_sound (enclosure_sound n left)
      (enclosure_sound n right) (by simp [Interval.compare, contrary])
    exact (not_lt_of_gt ordered) reversed
  simp [Interval.compare, firstImpossible, rationalSeparation]

/-- Refinement alone is not an equality oracle: even two identical logarithm
circuits keep non-point enclosures at every finite series budget. -/
theorem identical_log_two_is_unresolved (terms : Nat) :
    Interval.compare (enclose terms (.log ⟨2, by norm_num⟩))
      (enclose terms (.log ⟨2, by norm_num⟩)) = none := by
  apply Interval.positive_width_is_unresolved
  change CertifiedLogarithm.approximation 2 terms - CertifiedLogarithm.radius 2 terms <
    CertifiedLogarithm.approximation 2 terms + CertifiedLogarithm.radius 2 terms
  have positiveRadius : 0 < CertifiedLogarithm.radius 2 terms := by
    unfold CertifiedLogarithm.radius CertifiedLogarithm.parameter
    positivity
  linarith

end Circuit

end Mettapedia.Algorithms.CertifiedRealCircuit
