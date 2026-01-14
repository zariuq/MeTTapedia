/-
# Bridge: Connecting PlausibilitySpace to KnuthSkillingAlgebra

This module provides the formal connection between:
- `PlausibilitySpace` (distributive lattice of events)
- `KnuthSkillingAlgebra` (linearly ordered plausibility scale with ⊕)

The bridge is an `AdditiveValuation`: a monotone function v : Events → ℝ
that is additive on disjoint joins: v(a ⊔ b) = v(a) + v(b) when a ⊓ b = ⊥.

## Mathematical Context

In K&S's framework:
- Events E form a distributive lattice (PlausibilitySpace)
- Plausibilities form a linearly ordered monoid S (KnuthSkillingAlgebra)
- A valuation v : E → S connects them with: v(a ⊔ b) = v(a) ⊕ v(b) for disjoint a,b

The representation theorem (Appendix A) shows S embeds in (ℝ, +).
So the full pipeline is: E → S → ℝ, or directly E → ℝ via AdditiveValuation.

## Key Insight

We DON'T try to "induce" the operation ⊕ on range(v) by picking representative events.
That leads to well-definedness nightmares. Instead:
- The scale S already has its ⊕ operation
- The axiom is that v respects it on disjoint joins

For practical examples (Durrett Ch 1), we work directly with ℝ as the target.

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Durrett, "Probability: Theory and Examples" (5th ed), Chapter 1
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

open Classical

/-! ## AdditiveValuation: The Bridge to Classical Probability -/

/-- An `AdditiveValuation` is a valuation that is additive on disjoint joins.

This is the key bridge between K&S's abstract framework and classical probability.
The additivity axiom `v(a ⊔ b) = v(a) + v(b)` for disjoint events is exactly
what makes v a "probability measure" in the classical sense.

Positive example: Uniform measure on finite sets (counting measure / n)
Negative example: A monotone function that isn't additive (e.g., v(a) = 1 if a ≠ ⊥) -/
structure AdditiveValuation (α : Type*) [PlausibilitySpace α] extends Valuation α where
  /-- Additivity on disjoint joins: the fundamental axiom connecting ⊔ to + -/
  additive_disjoint : ∀ {a b : α}, Disjoint a b → val (a ⊔ b) = val a + val b

namespace AdditiveValuation

variable {α : Type*} [PlausibilitySpace α]

/-- Coercion to the underlying Valuation -/
instance : Coe (AdditiveValuation α) (Valuation α) := ⟨AdditiveValuation.toValuation⟩

/-- The value function -/
abbrev v (μ : AdditiveValuation α) : α → ℝ := μ.val

/-! ### Basic Properties -/

theorem v_bot (μ : AdditiveValuation α) : μ.v ⊥ = 0 := μ.val_bot

theorem v_top (μ : AdditiveValuation α) : μ.v ⊤ = 1 := μ.val_top

theorem v_mono (μ : AdditiveValuation α) : Monotone μ.v := μ.monotone

theorem v_nonneg (μ : AdditiveValuation α) (a : α) : 0 ≤ μ.v a :=
  μ.toValuation.nonneg a

theorem v_le_one (μ : AdditiveValuation α) (a : α) : μ.v a ≤ 1 :=
  μ.toValuation.le_one a

/-! ### Additivity Consequences -/

/-- Disjoint additivity restated -/
theorem v_add_of_disjoint (μ : AdditiveValuation α) {a b : α}
    (h : Disjoint a b) : μ.v (a ⊔ b) = μ.v a + μ.v b :=
  μ.additive_disjoint h

/-- Join with ⊥ doesn't change the value -/
theorem v_sup_bot (μ : AdditiveValuation α) (a : α) : μ.v (a ⊔ ⊥) = μ.v a := by
  simp only [sup_bot_eq]

/-- ⊥ join from the left -/
theorem v_bot_sup (μ : AdditiveValuation α) (a : α) : μ.v (⊥ ⊔ a) = μ.v a := by
  simp only [bot_sup_eq]

/-- Three-way additivity for pairwise disjoint elements -/
theorem v_add_three (μ : AdditiveValuation α) {a b c : α}
    (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    μ.v (a ⊔ b ⊔ c) = μ.v a + μ.v b + μ.v c := by
  have h_ab_c : Disjoint (a ⊔ b) c := by
    rw [disjoint_iff] at hab hac hbc ⊢
    calc (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) := inf_sup_right _ _ _
      _ = ⊥ ⊔ ⊥ := by rw [hac, hbc]
      _ = ⊥ := by simp
  calc μ.v (a ⊔ b ⊔ c) = μ.v (a ⊔ b) + μ.v c := μ.v_add_of_disjoint h_ab_c
    _ = (μ.v a + μ.v b) + μ.v c := by rw [μ.v_add_of_disjoint hab]
    _ = μ.v a + μ.v b + μ.v c := by ring

end AdditiveValuation

/-! ## General KSModel (for reference)

The most general bridge connects an arbitrary PlausibilitySpace to an
arbitrary KnuthSkillingAlgebra. We include this for completeness, though
for practical examples we use AdditiveValuation (with target ℝ).

```
structure KSModel (E S : Type*)
    [PlausibilitySpace E] [KnuthSkillingAlgebra S] where
  v : E → S
  mono : Monotone v
  v_bot : v ⊥ = KnuthSkillingAlgebraBase.ident
  v_sup_of_disjoint :
    ∀ {a b : E}, Disjoint a b → v (a ⊔ b) = KnuthSkillingAlgebraBase.op (v a) (v b)
```

When S = ℝ with (ident = 0, op = +), this reduces to AdditiveValuation
plus monotonicity (which follows from additivity + nonnegativity).
-/

/-! ## Boolean Algebra Properties

When the event space is a Boolean algebra (has complements), we get
additional properties like v(aᶜ) = 1 - v(a) and inclusion-exclusion.
These are proven in Examples/FiniteProbability.lean for concrete instances.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling
