import Mettapedia.Cybernetics.DistinctionCalculus.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Preservation grades and the metric structure of graded observers

A metric tolerance is a category enriched in the Łukasiewicz quantale: the
hom-object from `x` to `y` is the similarity, identities are similarity `1`,
and composition is the triangle law `a(x,y) + a(y,z) - 1 ≤ a(x,z)`. In
distance form it is a symmetric Lawvere metric space bounded by `1`.

* **Preservation grades** (HS16.02–HS16.04, Łukasiewicz form). A map has
  one-sided grade `1 − δ` when it adds at most `δ` to any distance
  (`ExpandsAtMost`), and two-sided grade `1 − δ` when it changes any distance
  by at most `δ` (`DistortsAtMost`). One-sided grade `1` is nonexpansiveness,
  the enriched-functor condition. Defects add along composites (grades
  multiply in the quantale). A constant map has one-sided grade `1` from every
  source (`expandsAtMost_const`): one-sided preservation permits total
  collapse. Its two-sided defect is the diameter of the source
  (`distortsAtMost_const_iff`).
* **Mathlib's metric structure.** On a type synonym, a metric tolerance is a
  `PseudoMetricSpace` whose distance is the tolerance's distance
  (`Observed`). Its zero kernel is Mathlib's inseparability
  (`observed_inseparable_iff`), and a nonexpansive map is `LipschitzWith 1`
  (`lipschitzWith_one_of_expandsAtMost`). The distinction calculus keeps
  observers as data rather than instances, since a carrier carries many
  observers at once; the synonym gives each one Mathlib's metric API.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u v w

variable {V : Type u} {W : Type v} {X : Type w}

namespace Tolerance

/-- **One-sided preservation at grade `1 − δ`**: the map adds at most `δ` to
any distance. -/
def ExpandsAtMost (a : Tolerance V) (b : Tolerance W) (f : V → W) (δ : ℚ) : Prop :=
  ∀ x y, b.distance (f x) (f y) ≤ a.distance x y + δ

/-- **Two-sided preservation at grade `1 − δ`**: the map changes any distance
by at most `δ`. -/
def DistortsAtMost (a : Tolerance V) (b : Tolerance W) (f : V → W) (δ : ℚ) : Prop :=
  ∀ x y, |b.distance (f x) (f y) - a.distance x y| ≤ δ

variable {a : Tolerance V} {b : Tolerance W} {c : Tolerance X}

theorem expandsAtMost_id (a : Tolerance V) : ExpandsAtMost a a id 0 :=
  fun x y => by simp

/-- **Defects add along composites** (HS16.02: grades multiply). -/
theorem ExpandsAtMost.comp {f : V → W} {g : W → X} {δ δ' : ℚ} (first : ExpandsAtMost a b f δ)
    (second : ExpandsAtMost b c g δ') : ExpandsAtMost a c (g ∘ f) (δ + δ') := by
  intro x y
  have := first x y
  have := second (f x) (f y)
  simp only [Function.comp_apply]
  linarith

theorem DistortsAtMost.comp {f : V → W} {g : W → X} {δ δ' : ℚ} (first : DistortsAtMost a b f δ)
    (second : DistortsAtMost b c g δ') : DistortsAtMost a c (g ∘ f) (δ + δ') := by
  intro x y
  simp only [Function.comp_apply]
  calc |c.distance (g (f x)) (g (f y)) - a.distance x y|
      ≤ |c.distance (g (f x)) (g (f y)) - b.distance (f x) (f y)| +
          |b.distance (f x) (f y) - a.distance x y| := abs_sub_le _ _ _
    _ ≤ δ' + δ := add_le_add (second (f x) (f y)) (first x y)
    _ = δ + δ' := add_comm δ' δ

/-- Two-sided preservation implies one-sided preservation. -/
theorem DistortsAtMost.expandsAtMost {f : V → W} {δ : ℚ} (distorts : DistortsAtMost a b f δ) :
    ExpandsAtMost a b f δ := fun x y => by
  have := (abs_le.mp (distorts x y)).2
  linarith

/-- **Collapse is perfect for one-sided preservation** (HS16.04): a constant
map never adds distance. -/
theorem expandsAtMost_const (a : Tolerance V) (b : Tolerance W) (w : W) :
    ExpandsAtMost a b (fun _ => w) 0 := fun x y => by
  simp only [distance_self, add_zero]
  exact a.distance_nonnegative x y

/-- **The two-sided defect of a collapse is the diameter of the source.** -/
theorem distortsAtMost_const_iff (a : Tolerance V) (b : Tolerance W) (w : W) {δ : ℚ} :
    DistortsAtMost a b (fun _ => w) δ ↔ ∀ x y, a.distance x y ≤ δ := by
  constructor
  · intro distorts x y
    have := distorts x y
    rw [distance_self, zero_sub, abs_neg, abs_of_nonneg (a.distance_nonnegative x y)] at this
    exact this
  · intro bound x y
    rw [distance_self, zero_sub, abs_neg, abs_of_nonneg (a.distance_nonnegative x y)]
    exact bound x y

/-- **Control**: collapsing two distinguishable Booleans has one-sided grade `1`
and two-sided defect `1`. -/
theorem collapse_grades :
    ExpandsAtMost (ofReport (id : Bool → Bool)) (ofReport (id : Bool → Bool)) (fun _ => false) 0 ∧
      ∀ δ < 1, ¬ DistortsAtMost (ofReport (id : Bool → Bool)) (ofReport (id : Bool → Bool))
        (fun _ => false) δ := by
  refine ⟨expandsAtMost_const _ _ _, fun δ small distorts => ?_⟩
  have := (distortsAtMost_const_iff _ _ _).mp distorts false true
  simp [distance, ofReport] at this
  linarith

end Tolerance

/-! ## Mathlib's metric structure -/

/-- The carrier of a metric tolerance, as a type synonym carrying its metric. -/
def Observed (a : Tolerance V) (_metric : a.Metric) : Type u := V

namespace Observed

variable (a : Tolerance V) (metric : a.Metric)

/-- View a point of the carrier in the observed space. -/
def of (x : V) : Observed a metric := x

/-- The underlying point of the carrier. -/
def val (x : Observed a metric) : V := x

noncomputable instance : PseudoMetricSpace (Observed a metric) where
  dist x y := (a.distance (val a metric x) (val a metric y) : ℝ)
  dist_self x := by rw [a.distance_self, Rat.cast_zero]
  dist_comm x y := by rw [a.distance_symm]
  dist_triangle x y z := by exact_mod_cast metric (val a metric x) (val a metric y) (val a metric z)

theorem dist_of (x y : V) : dist (of a metric x) (of a metric y) = (a.distance x y : ℝ) :=
  rfl

/-- **The zero kernel of a graded observer is Mathlib's inseparability.** -/
theorem observed_inseparable_iff (x y : V) :
    Inseparable (of a metric x) (of a metric y) ↔ a.Indistinguishable x y := by
  rw [Metric.inseparable_iff, dist_of]
  unfold Tolerance.Indistinguishable
  exact_mod_cast Iff.rfl

end Observed

/-- **A nonexpansive map is `LipschitzWith 1`** between the observed spaces. -/
theorem lipschitzWith_one_of_expandsAtMost {a : Tolerance V} {b : Tolerance W} (ha : a.Metric)
    (hb : b.Metric) {f : V → W} (nonexpansive : Tolerance.ExpandsAtMost a b f 0) :
    LipschitzWith 1 (fun x : Observed a ha => (Observed.of b hb (f x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  change (b.distance (f x) (f y) : ℝ) ≤ (a.distance x y : ℝ)
  have := nonexpansive x y
  rw [add_zero] at this
  exact_mod_cast this

end Mettapedia.Cybernetics.DistinctionCalculus
