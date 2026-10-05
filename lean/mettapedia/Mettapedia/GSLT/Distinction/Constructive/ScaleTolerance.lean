import Mettapedia.GSLT.Distinction.Constructive.DepthBound
import Mettapedia.Cybernetics.DistinctionCalculus.Basic

/-!
# Tolerances valued in an ordered group with a unit

A distinction-calculus observer (`DistinctionCalculus.Tolerance`) is a
similarity valued in a linearly ordered field, rational by default.  The
constructive layer computes in a linearly ordered additive group with a
positive unit (`Scale`), because the field and order laws of Mathlib's `ℚ`
depend on `Classical.choice` while those of `ℤ` and of ordered groups do not.

* **Scale-valued tolerances** (`ScaleTolerance`).  The same five laws with the
  unit in place of `1`: values between `0` and the unit, the unit on the
  diagonal, symmetry.  The distance is the unit minus the similarity, and the
  metric law is the same triangle inequality (`ScaleTolerance.Metric`).  A
  bounded pseudodistance is a tolerance (`ScaleTolerance.ofDistance`), and a
  crisp report is a metric tolerance (`ScaleTolerance.ofReport`).
* **Each depth bound is a metric tolerance**
  (`PresentedSystem.depthTolerance`, `depthTolerance_metric`): its distance is
  the depth bound, and no choice principle is used.
* **The bridge to the distinction calculus.**  Over a linearly ordered field
  with unit `1` a scale-valued tolerance is a tolerance of the distinction
  calculus with the same similarity, distance and metric law
  (`toleranceEquiv`, `toTolerance_distance`, `toTolerance_metric_iff`), and
  the crisp report goes to `Tolerance.ofReport` (`toTolerance_ofReport`).  A
  group with a unit is read into `ℚ` through a rational reading (`RatReading`:
  additive, order reflecting, the unit to `1`), for example `k ↦ k / unit` on
  the integers (`RatReading.integers`); reading a tolerance keeps its distance
  and its metric law (`ScaleTolerance.read_distance`,
  `ScaleTolerance.read_metric_iff`).  So every depth bound over the integers is a
  rational distinction-calculus tolerance (`depthTolerance_read_metric`), and
  the classical step is confined to the reading into `ℚ`.

`Tolerance` itself is unchanged.  The controls are in `ScaleToleranceControls`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Constructive

open Mettapedia.Cybernetics.DistinctionCalculus (Tolerance)

universe uX uY uV uS uAtom uLabel uObs

/-! ## Scale-valued tolerances -/

section Group

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- **A tolerance valued in an ordered additive group with a unit**: a
similarity between `0` and the unit, the unit on the diagonal, and symmetric.
It is not assumed transitive. -/
structure ScaleTolerance (X : Type uX) (one : V) where
  similarity : X → X → V
  nonnegative : ∀ x y, 0 ≤ similarity x y
  bounded : ∀ x y, similarity x y ≤ one
  reflexive : ∀ x, similarity x x = one
  symmetric : ∀ x y, similarity x y = similarity y x

namespace ScaleTolerance

variable {X : Type uX} {Y : Type uY} {one : V}

/-- The distance: the unit minus the similarity. -/
def distance (a : ScaleTolerance X one) (x y : X) : V := one - a.similarity x y

theorem distance_nonneg (a : ScaleTolerance X one) (x y : X) : 0 ≤ a.distance x y :=
  sub_nonneg.mpr (a.bounded x y)

theorem distance_le_one (a : ScaleTolerance X one) (x y : X) : a.distance x y ≤ one :=
  sub_le_self one (a.nonnegative x y)

omit [IsOrderedAddMonoid V] in
theorem distance_self (a : ScaleTolerance X one) (x : X) : a.distance x x = 0 := by
  rw [distance, a.reflexive, sub_self]

omit [IsOrderedAddMonoid V] in
theorem distance_symm (a : ScaleTolerance X one) (x y : X) : a.distance x y = a.distance y x := by
  rw [distance, distance, a.symmetric]

/-- The metric law: the triangle inequality of the distance. -/
def Metric (a : ScaleTolerance X one) : Prop :=
  ∀ x y z, a.distance x z ≤ a.distance x y + a.distance y z

/-- **A bounded pseudodistance is a tolerance**, with similarity the unit minus
the distance. -/
def ofDistance (d : X → X → V) (nonneg : ∀ x y, 0 ≤ d x y) (le_one : ∀ x y, d x y ≤ one)
    (self : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x) : ScaleTolerance X one where
  similarity x y := one - d x y
  nonnegative x y := sub_nonneg.mpr (le_one x y)
  bounded x y := sub_le_self one (nonneg x y)
  reflexive x := by rw [self, sub_zero]
  symmetric x y := by rw [symm]

theorem distance_ofDistance (d : X → X → V) (nonneg : ∀ x y, 0 ≤ d x y)
    (le_one : ∀ x y, d x y ≤ one) (self : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
    (x y : X) : (ofDistance d nonneg le_one self symm).distance x y = d x y :=
  sub_sub_cancel one (d x y)

/-- The tolerance of a crisp report: the unit on equal reports, `0` otherwise. -/
def ofReport [DecidableEq Y] (report : X → Y) (positive : 0 ≤ one) : ScaleTolerance X one where
  similarity x y := if report x = report y then one else 0
  nonnegative x y := by
    by_cases same : report x = report y
    · rw [if_pos same]
      exact positive
    · rw [if_neg same]
  bounded x y := by
    by_cases same : report x = report y
    · rw [if_pos same]
    · rw [if_neg same]
      exact positive
  reflexive x := if_pos rfl
  symmetric x y := by
    by_cases same : report x = report y
    · rw [if_pos same, if_pos same.symm]
    · rw [if_neg same, if_neg fun other => same other.symm]

/-- **A crisp report is a metric tolerance.** -/
theorem ofReport_metric [DecidableEq Y] (report : X → Y) (positive : 0 ≤ one) :
    (ofReport report positive).Metric := by
  intro x y z
  have nonneg := fun x y => (ofReport (one := one) report positive).distance_nonneg x y
  by_cases first : report x = report y
  · by_cases second : report y = report z
    · have outer : report x = report z := first.trans second
      change one - (if report x = report z then one else 0) ≤
        (one - if report x = report y then one else 0) + (one - if report y = report z then one else 0)
      rw [if_pos outer, if_pos first, if_pos second, sub_self, add_zero]
    · change one - (if report x = report z then one else 0) ≤
        (one - if report x = report y then one else 0) + (one - if report y = report z then one else 0)
      rw [if_pos first, if_neg second, sub_self, zero_add, sub_zero]
      exact sub_le_self one (by split <;> first | exact positive | exact le_rfl)
  · change one - (if report x = report z then one else 0) ≤
      (one - if report x = report y then one else 0) + (one - if report y = report z then one else 0)
    rw [if_neg first, sub_zero]
    exact le_add_of_le_of_nonneg (sub_le_self one (by split <;> first | exact positive | exact le_rfl))
      (nonneg y z)

end ScaleTolerance

/-! ## Each depth bound is a metric tolerance -/

namespace PresentedSystem

variable {S : GSLT.{uS}} {K : Scale V} (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)
  (W : Q.Vocabulary)

/-- **The tolerance of the depth-`n` bound**: similarity is the unit minus the
bound. -/
def depthTolerance (depth : ℕ) : ScaleTolerance S.Term K.one :=
  ScaleTolerance.ofDistance (Q.depthBound W depth) (Q.depthBound_nonneg W depth)
    (Q.depthBound_le_one W depth) (Q.depthBound_self W depth) (Q.depthBound_symm W depth)

theorem depthTolerance_distance (depth : ℕ) (left right : S.Term) :
    (Q.depthTolerance W depth).distance left right = Q.depthBound W depth left right :=
  ScaleTolerance.distance_ofDistance _ _ _ _ _ left right

/-- **Each depth bound is a metric tolerance.** -/
theorem depthTolerance_metric (depth : ℕ) : (Q.depthTolerance W depth).Metric := by
  intro first second third
  rw [Q.depthTolerance_distance, Q.depthTolerance_distance, Q.depthTolerance_distance]
  exact Q.depthBound_triangle W depth first second third

end PresentedSystem

end Group

/-! ## The bridge to the distinction calculus -/

section Field

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {X : Type uX}

namespace ScaleTolerance

/-- A tolerance with unit `1` in a linearly ordered field is a tolerance of the
distinction calculus. -/
def toTolerance (a : ScaleTolerance X (1 : R)) : Tolerance X R where
  similarity := a.similarity
  nonnegative := a.nonnegative
  bounded := a.bounded
  reflexive := a.reflexive
  symmetric := a.symmetric

/-- A tolerance of the distinction calculus is a tolerance with unit `1`. -/
def ofTolerance (a : Tolerance X R) : ScaleTolerance X (1 : R) where
  similarity := a.similarity
  nonnegative := a.nonnegative
  bounded := a.bounded
  reflexive := a.reflexive
  symmetric := a.symmetric

/-- **Over a linearly ordered field the two notions are one.** -/
def toleranceEquiv : ScaleTolerance X (1 : R) ≃ Tolerance X R where
  toFun := toTolerance
  invFun := ofTolerance
  left_inv _ := rfl
  right_inv _ := rfl

theorem toTolerance_distance (a : ScaleTolerance X (1 : R)) (x y : X) :
    a.toTolerance.distance x y = a.distance x y :=
  rfl

theorem toTolerance_metric_iff (a : ScaleTolerance X (1 : R)) : a.toTolerance.Metric ↔ a.Metric :=
  Iff.rfl

/-- The crisp report goes to the crisp report of the distinction calculus. -/
theorem toTolerance_ofReport {Y : Type uY} [DecidableEq Y] (report : X → Y) :
    (ofReport report (zero_le_one : (0 : R) ≤ 1)).toTolerance = Tolerance.ofReport report R :=
  rfl

end ScaleTolerance

end Field

/-! ## Reading a value scale into the rationals -/

section Reading

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- **A rational reading** of a group with a unit: additive, order reflecting,
and the unit read as `1`. -/
structure RatReading (one : V) where
  toRat : V → ℚ
  toRat_add : ∀ first second, toRat (first + second) = toRat first + toRat second
  toRat_le_iff : ∀ {first second : V}, toRat first ≤ toRat second ↔ first ≤ second
  toRat_one : toRat one = 1

namespace RatReading

variable {one : V} (reading : RatReading one)

omit [IsOrderedAddMonoid V] in
theorem toRat_zero : reading.toRat 0 = 0 := by
  have double := reading.toRat_add 0 0
  rw [add_zero] at double
  linarith

omit [IsOrderedAddMonoid V] in
theorem toRat_sub (first second : V) :
    reading.toRat (first - second) = reading.toRat first - reading.toRat second := by
  have split := reading.toRat_add (first - second) second
  rw [sub_add_cancel] at split
  linarith

/-- The integers with a positive unit, read as `k / unit`. -/
def integers (unit : ℤ) (positive : 0 < unit) : RatReading unit where
  toRat value := (value : ℚ) / unit
  toRat_add first second := by
    push_cast
    exact add_div _ _ _
  toRat_le_iff := by
    intro first second
    have unitPos : (0 : ℚ) < unit := by exact_mod_cast positive
    rw [div_le_div_iff_of_pos_right unitPos]
    exact Int.cast_le
  toRat_one := by
    have unitPos : (0 : ℚ) < unit := by exact_mod_cast positive
    exact div_self unitPos.ne'

end RatReading

namespace ScaleTolerance

variable {X : Type uX} {one : V}

/-- **Read a tolerance into the rationals**: a rational tolerance of the
distinction calculus. -/
def read (a : ScaleTolerance X one) (reading : RatReading one) : Tolerance X ℚ where
  similarity x y := reading.toRat (a.similarity x y)
  nonnegative x y := by
    rw [← reading.toRat_zero]
    exact reading.toRat_le_iff.mpr (a.nonnegative x y)
  bounded x y := by
    rw [← reading.toRat_one]
    exact reading.toRat_le_iff.mpr (a.bounded x y)
  reflexive x := by rw [a.reflexive, reading.toRat_one]
  symmetric x y := by rw [a.symmetric]

omit [IsOrderedAddMonoid V] in
/-- **Reading keeps the distance.** -/
theorem read_distance (a : ScaleTolerance X one) (reading : RatReading one) (x y : X) :
    (a.read reading).distance x y = reading.toRat (a.distance x y) := by
  change 1 - reading.toRat (a.similarity x y) = reading.toRat (one - a.similarity x y)
  rw [reading.toRat_sub, reading.toRat_one]

omit [IsOrderedAddMonoid V] in
/-- **Reading keeps the metric law, both ways.** -/
theorem read_metric_iff (a : ScaleTolerance X one) (reading : RatReading one) :
    (a.read reading).Metric ↔ a.Metric := by
  refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun z => ?_
  rw [read_distance, read_distance, read_distance, ← reading.toRat_add]
  exact reading.toRat_le_iff

end ScaleTolerance

/-- **Every depth bound, read into the rationals, is a metric tolerance of the
distinction calculus.** -/
theorem depthTolerance_read_metric {S : GSLT.{uS}} {K : Scale V}
    (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K) (W : Q.Vocabulary) (depth : ℕ)
    (reading : RatReading K.one) : ((Q.depthTolerance W depth).read reading).Metric :=
  ((Q.depthTolerance W depth).read_metric_iff reading).mpr (Q.depthTolerance_metric W depth)

end Reading

end Mettapedia.GSLT.Distinction.Constructive
