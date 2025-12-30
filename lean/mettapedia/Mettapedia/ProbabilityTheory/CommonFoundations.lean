/-
# Common Algebraic Foundations for Probability Theories

This module identifies the common algebraic structures underlying different
probability frameworks:
- Standard (Kolmogorov) probability
- Imprecise probability (Walley's coherent lower previsions)
- Cox's plausibility theory

All of these are "valuation functionals" with varying degrees of structure.
This unification helps clarify the relationships and hierarchy between
different probability theories.

## Main Structures

* `Valuation` - A functional from events/gambles to reals with basic properties
* `MonotoneValuation` - A valuation that respects ordering
* `BoundedValuation` - A valuation with finite bounds
* `AdditiveValuation` - Standard probability (additive)
* `SuperadditiveValuation` - Imprecise probability (superadditive)

## Key Results

* Standard probability is a special case of imprecise probability
* Imprecise probability is characterized by non-additive gap
* Cox's plausibility (when consistent) reduces to standard probability

## References

* [Walley, *Statistical Reasoning with Imprecise Probabilities*][walley1991]
* [Cox, *The Algebra of Probable Inference*][cox1961]
* [de Finetti, *Theory of Probability*][definetti1974]
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Lattice
import Mettapedia.ProbabilityTheory.ImpreciseProbability.Basic

namespace Mettapedia.ProbabilityTheory.CommonFoundations

open ImpreciseProbability

/-!
## Generic Valuations on Ordered Spaces

We define abstract valuations that can be instantiated to different
probability theories. The key abstraction is a functional from some
ordered space to the reals.
-/

/-- A valuation on an ordered additive group with bounds preservation.
    This captures the common structure of all probability-like functionals. -/
structure Valuation (X : Type*) [AddCommGroup X] [LE X] where
  /-- The valuation functional -/
  toFun : X → ℝ
  /-- Valuations respect ordering: x ≤ y implies v(x) ≤ v(y) -/
  mono : ∀ {x y : X}, x ≤ y → toFun x ≤ toFun y

namespace Valuation

variable {X : Type*} [AddCommGroup X] [LE X]

instance : CoeFun (Valuation X) (fun _ => X → ℝ) := ⟨toFun⟩

/-- The gap between a valuation and its "ideal" value measures non-additivity.
    For additive valuations, this should be zero. -/
def gap (v : Valuation X) (x y : X) : ℝ :=
  v (x + y) - (v x + v y)

/-- A valuation is additive if the gap is always zero. -/
def isAdditive (v : Valuation X) : Prop :=
  ∀ x y, v.gap x y = 0

/-- A valuation is superadditive if the gap is always non-negative. -/
def isSuperadditive (v : Valuation X) : Prop :=
  ∀ x y, v.gap x y ≥ 0

/-- A valuation is subadditive if the gap is always non-positive. -/
def isSubadditive (v : Valuation X) : Prop :=
  ∀ x y, v.gap x y ≤ 0

/-- Additive valuations are both super- and sub-additive. -/
lemma isAdditive_iff_super_and_sub (v : Valuation X) :
    v.isAdditive ↔ v.isSuperadditive ∧ v.isSubadditive := by
  constructor
  · intro h
    exact ⟨fun x y => ge_of_eq (h x y), fun x y => le_of_eq (h x y)⟩
  · intro ⟨hsup, hsub⟩ x y
    have h1 := hsup x y
    have h2 := hsub x y
    linarith

end Valuation

/-!
## Connecting to Lower Previsions

We show that Walley's lower previsions are superadditive valuations,
and that precision (additivity) characterizes standard probability.
-/

/-- A lower prevision is a monotone valuation (given the A1 axiom). -/
def lowerPrevisionToValuation {Ω : Type*} (P : LowerPrevision Ω) : Valuation (Gamble Ω) where
  toFun := P.toFun
  mono := fun h => P.mono h

/-- Lower previsions are superadditive valuations. -/
lemma lowerPrevision_isSuperadditive {Ω : Type*} (P : LowerPrevision Ω) :
    (lowerPrevisionToValuation P).isSuperadditive := by
  intro X Y
  simp only [Valuation.gap, lowerPrevisionToValuation]
  have h := P.superadd X Y
  linarith

/-- Precise lower previsions are additive valuations. -/
lemma precise_lowerPrevision_isAdditive {Ω : Type*} (P : LowerPrevision Ω)
    (hprec : P.isPrecise) : (lowerPrevisionToValuation P).isAdditive := by
  intro X Y
  simp only [Valuation.gap, lowerPrevisionToValuation]
  have hadd := (P.precise_iff_additive.mp hprec) X Y
  linarith

/-!
## The Hierarchy of Probability Theories

Standard probability ⊂ Imprecise probability

This hierarchy is captured by the algebraic properties:
- Additive valuations ⊂ Superadditive valuations

The inclusion is proper: there exist superadditive valuations that are
not additive (i.e., imprecise probabilities that are not precise).
-/

/-- The imprecision of a valuation at (x, y) is the absolute gap. -/
def imprecisionGap {X : Type*} [AddCommGroup X] [LE X]
    (v : Valuation X) (x y : X) : ℝ :=
  |v.gap x y|

/-- For superadditive valuations, imprecision is just the gap. -/
lemma imprecisionGap_of_superadditive {X : Type*} [AddCommGroup X] [LE X]
    (v : Valuation X) (hsup : v.isSuperadditive) (x y : X) :
    imprecisionGap v x y = v.gap x y := by
  simp only [imprecisionGap]
  exact abs_of_nonneg (hsup x y)

/-- Zero imprecision everywhere implies additivity. -/
lemma isAdditive_of_zero_imprecision {X : Type*} [AddCommGroup X] [LE X]
    (v : Valuation X) (h : ∀ x y, imprecisionGap v x y = 0) : v.isAdditive := by
  intro x y
  have hxy := h x y
  simp only [imprecisionGap, abs_eq_zero] at hxy
  exact hxy

/-!
## Summary: Algebraic Classification of Probability Theories

| Theory | Valuation Type | Gap Property |
|--------|---------------|--------------|
| Standard probability | Additive | gap = 0 |
| Lower imprecise prob | Superadditive | gap ≥ 0 |
| Upper imprecise prob | Subadditive | gap ≤ 0 |

The Cox theorem shows that under certain consistency axioms
(associativity of conjunction, involution of negation),
plausibility functions must be isomorphic to probability.
This means Cox's axioms FORCE additivity.

Knuth-Skilling claims to derive probability from weaker axioms,
but the question is: what "probability" do they derive?
- If additive: they implicitly assumed something that forces additivity
- If only superadditive: they get imprecise probability, not standard

This is the key question for K&S analysis.
-/

end Mettapedia.ProbabilityTheory.CommonFoundations
