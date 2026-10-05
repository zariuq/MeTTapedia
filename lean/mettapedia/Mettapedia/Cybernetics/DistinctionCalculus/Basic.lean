import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Observers for distinction calculus

A tolerance is a similarity valued in a linearly ordered field, rational by
default: `Tolerance V` is `Tolerance V ℚ`, the exact executable fragment, and
`Tolerance V ℝ` carries the real observers whose distances need square roots.
Similarity is reflexive and symmetric, but is not assumed transitive. Its
complement is a bounded symmetric distance; the metric condition is an
additional law, not an implicit conversion to equality. "Metric" follows the
paper's convention: zero distance need not imply identity, so the
complementary distance is a pseudometric.

Reference: B. Goertzel, *The Distinction Calculus*, corrected September 2026,
Sections 2.1 and 2.3.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u v

/-- A bounded similarity, without a transitivity requirement, valued in a linearly
ordered field (rational unless another field is given). -/
structure Tolerance (V : Type u) (R : Type := ℚ) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  similarity : V → V → R
  nonnegative : ∀ x y, 0 ≤ similarity x y
  bounded : ∀ x y, similarity x y ≤ 1
  reflexive : ∀ x, similarity x x = 1
  symmetric : ∀ x y, similarity x y = similarity y x

namespace Tolerance

variable {V : Type u} {W : Type v} {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

def distance (a : Tolerance V R) (x y : V) : R := 1 - a.similarity x y

theorem distance_nonnegative (a : Tolerance V R) (x y : V) :
    0 ≤ a.distance x y := sub_nonneg.mpr (a.bounded x y)

theorem distance_bounded (a : Tolerance V R) (x y : V) :
    a.distance x y ≤ 1 := by
  have h := a.nonnegative x y
  dsimp [distance]
  linarith

@[simp] theorem distance_self (a : Tolerance V R) (x : V) :
    a.distance x x = 0 := by simp [distance, a.reflexive]

theorem distance_symm (a : Tolerance V R) (x y : V) :
    a.distance x y = a.distance y x := by rw [distance, distance, a.symmetric]

def Metric (a : Tolerance V R) : Prop :=
  ∀ x y z, a.distance x z ≤ a.distance x y + a.distance y z

/-- This is precisely the max-Lukasiewicz triangle condition. -/
theorem metric_iff_similarity (a : Tolerance V R) :
    a.Metric ↔ ∀ x y z,
      a.similarity x y + a.similarity y z - 1 ≤ a.similarity x z := by
  simp only [Metric, distance]
  constructor <;> intro h x y z <;> have bound := h x y z <;> linarith

/-- Zero observer distance is not, in general, identity of the observed data. -/
def Indistinguishable (a : Tolerance V R) (x y : V) : Prop := a.distance x y = 0

/-- Positive observer distance provides a witnessed distinction. -/
def Apart (a : Tolerance V R) (x y : V) : Prop := 0 < a.distance x y

theorem indistinguishable_iff_similarity_one (a : Tolerance V R) (x y : V) :
    a.Indistinguishable x y ↔ a.similarity x y = 1 := by
  dsimp [Indistinguishable, distance]
  constructor <;> intro h <;> linarith

theorem not_apart_iff_indistinguishable (a : Tolerance V R) (x y : V) :
    ¬ a.Apart x y ↔ a.Indistinguishable x y := by
  dsimp [Apart, Indistinguishable]
  constructor
  · intro h
    exact le_antisymm (le_of_not_gt h) (a.distance_nonnegative x y)
  · intro h
    simp [h]

theorem apart_implies_ne (a : Tolerance V R) {x y : V} (h : a.Apart x y) : x ≠ y := by
  intro equal
  subst y
  simp [Apart] at h

theorem apart_symm (a : Tolerance V R) {x y : V} (h : a.Apart x y) : a.Apart y x := by
  simpa only [Apart, a.distance_symm y x] using h

/-- Cotransitivity is earned by the metric law; tolerances alone do not have it. -/
theorem apart_cotrans (a : Tolerance V R) (metric : a.Metric)
    {x y : V} (h : a.Apart x y) (z : V) : a.Apart x z ∨ a.Apart z y := by
  by_cases first : a.Apart x z
  · exact Or.inl first
  · right
    have zero := (a.not_apart_iff_indistinguishable x z).mp first
    have triangle := metric x z y
    dsimp [Apart, Indistinguishable] at *
    linarith

def zeroSetoid (a : Tolerance V R) (metric : a.Metric) : Setoid V where
  r := a.Indistinguishable
  iseqv := ⟨fun x => a.distance_self x,
    fun h => (a.distance_symm _ _).trans h, by
      intro x y z xy yz
      have bound := metric x y z
      dsimp [Indistinguishable] at *
      exact le_antisymm (by linarith) (a.distance_nonnegative x z)⟩

/-- Under metric coherence, zero-distance states have literally identical rows. -/
theorem indistinguishable_iff_rows (a : Tolerance V R) (metric : a.Metric) (x y : V) :
    a.Indistinguishable x y ↔ ∀ z, a.similarity x z = a.similarity y z := by
  constructor
  · intro same z
    have left := metric x y z
    have right := metric y x z
    rw [a.distance_symm y x] at right
    dsimp [Indistinguishable, distance] at *
    linarith
  · intro rows
    exact (a.indistinguishable_iff_similarity_one x y).mpr
      ((rows y).trans (a.reflexive y))

def pullback (a : Tolerance W R) (f : V → W) : Tolerance V R where
  similarity x y := a.similarity (f x) (f y)
  nonnegative x y := a.nonnegative (f x) (f y)
  bounded x y := a.bounded (f x) (f y)
  reflexive x := a.reflexive (f x)
  symmetric x y := a.symmetric (f x) (f y)

@[simp] theorem distance_pullback (a : Tolerance W R) (f : V → W) (x y : V) :
    (a.pullback f).distance x y = a.distance (f x) (f y) := rfl

theorem metric_pullback (a : Tolerance W R) (metric : a.Metric) (f : V → W) :
    (a.pullback f).Metric := fun x y z => metric (f x) (f y) (f z)

/-- A precise report has a crisp metric observer, even when the report is lossy.
The field of values is rational unless given. -/
def ofReport [DecidableEq W] (report : V → W) (R : Type := ℚ) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] : Tolerance V R where
  similarity x y := if report x = report y then 1 else 0
  nonnegative x y := by split_ifs <;> norm_num
  bounded x y := by split_ifs <;> norm_num
  reflexive x := by simp
  symmetric x y := by simp [eq_comm]

@[simp] theorem ofReport_indistinguishable [DecidableEq W] (report : V → W) (x y : V) :
    (ofReport report R).Indistinguishable x y ↔ report x = report y := by
  rw [indistinguishable_iff_similarity_one]
  simp [ofReport]

theorem ofReport_metric [DecidableEq W] (report : V → W) : (ofReport report R).Metric := by
  rw [metric_iff_similarity]
  intro x y z
  dsimp [ofReport]
  split_ifs <;> simp_all

/-- Coarsening is the model class for path-derived similarities. -/
def Extends (base model : Tolerance V R) : Prop :=
  ∀ x y, base.similarity x y ≤ model.similarity x y

theorem distance_le_of_extends {base model : Tolerance V R}
    (hExt : base.Extends model) (x y : V) : model.distance x y ≤ base.distance x y := by
  exact sub_le_sub_left (hExt x y) 1

end Tolerance

end Mettapedia.Cybernetics.DistinctionCalculus
