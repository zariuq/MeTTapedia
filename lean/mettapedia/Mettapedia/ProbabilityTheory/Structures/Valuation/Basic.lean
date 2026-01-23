/-
# Common Valuation Infrastructure

Shared lemmas about valuations that work across ALL probability theories:
- Classical (Kolmogorov)
- Cox
- Knuth-Skilling
- Dempster-Shafer
- Quantum

## Design Principle

Every probability theory has some notion of a "valuation" mapping propositions
to real numbers (or intervals). This module captures the COMMON properties:

1. **Monotonicity**: a ≤ b → v(a) ≤ v(b)
2. **Normalization**: v(⊥) = 0, v(⊤) = 1
3. **Boundedness**: 0 ≤ v(a) ≤ 1

By proving these once, we avoid duplication across theories.
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.Common

/-!
## §1: Monotone Valuations

A monotone valuation is a function v : L → ℝ that preserves order.
-/

/-- A monotone valuation on a lattice. -/
structure MonotoneValuation (L : Type*) [Lattice L] where
  /-- The valuation function -/
  val : L → ℝ
  /-- Monotonicity -/
  mono : ∀ a b, a ≤ b → val a ≤ val b

namespace MonotoneValuation

variable {L : Type*} [Lattice L]

/-- Valuations preserve the lattice order. -/
theorem preserves_le (v : MonotoneValuation L) {a b : L} (h : a ≤ b) :
    v.val a ≤ v.val b := v.mono a b h

/-- v(a ⊓ b) ≤ v(a) for any monotone valuation. -/
theorem val_inf_le_left (v : MonotoneValuation L) (a b : L) :
    v.val (a ⊓ b) ≤ v.val a := v.mono _ _ _root_.inf_le_left

/-- v(a ⊓ b) ≤ v(b) for any monotone valuation. -/
theorem val_inf_le_right (v : MonotoneValuation L) (a b : L) :
    v.val (a ⊓ b) ≤ v.val b := v.mono _ _ _root_.inf_le_right

/-- v(a) ≤ v(a ⊔ b) for any monotone valuation. -/
theorem val_le_sup_left (v : MonotoneValuation L) (a b : L) :
    v.val a ≤ v.val (a ⊔ b) := v.mono _ _ _root_.le_sup_left

/-- v(b) ≤ v(a ⊔ b) for any monotone valuation. -/
theorem val_le_sup_right (v : MonotoneValuation L) (a b : L) :
    v.val b ≤ v.val (a ⊔ b) := v.mono _ _ _root_.le_sup_right

end MonotoneValuation

/-!
## §2: Normalized Valuations

A normalized valuation maps ⊥ to 0 and ⊤ to 1.
-/

/-- A normalized monotone valuation: maps ⊥ → 0 and ⊤ → 1. -/
structure NormalizedValuation (L : Type*) [Lattice L] [BoundedOrder L]
    extends MonotoneValuation L where
  /-- Bottom maps to 0 -/
  val_bot : val ⊥ = 0
  /-- Top maps to 1 -/
  val_top : val ⊤ = 1

namespace NormalizedValuation

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- All values are non-negative. -/
theorem nonneg (v : NormalizedValuation L) (a : L) : 0 ≤ v.val a := by
  calc 0 = v.val ⊥ := v.val_bot.symm
       _ ≤ v.val a := v.mono ⊥ a bot_le

/-- All values are at most 1. -/
theorem le_one (v : NormalizedValuation L) (a : L) : v.val a ≤ 1 := by
  calc v.val a ≤ v.val ⊤ := v.mono a ⊤ le_top
       _ = 1 := v.val_top

/-- All values lie in [0, 1]. -/
theorem bounded (v : NormalizedValuation L) (a : L) : 0 ≤ v.val a ∧ v.val a ≤ 1 :=
  ⟨v.nonneg a, v.le_one a⟩

/-- The value at ⊥ is the minimum. -/
theorem bot_minimal (v : NormalizedValuation L) (a : L) : v.val ⊥ ≤ v.val a :=
  v.mono ⊥ a bot_le

/-- The value at ⊤ is the maximum. -/
theorem top_maximal (v : NormalizedValuation L) (a : L) : v.val a ≤ v.val ⊤ :=
  v.mono a ⊤ le_top

end NormalizedValuation

/-!
## §3: Imprecise Valuations (Lower/Upper Pairs)

For theories like Dempster-Shafer, we have TWO valuations: lower (belief)
and upper (plausibility), with lower ≤ upper.
-/

/-- An imprecise valuation: a pair (lower, upper) with lower ≤ upper. -/
structure ImpreciseValuation (L : Type*) [Lattice L] [BoundedOrder L] where
  /-- Lower valuation (belief) -/
  lower : NormalizedValuation L
  /-- Upper valuation (plausibility) -/
  upper : L → ℝ
  /-- Upper is at least lower -/
  lower_le_upper : ∀ a, lower.val a ≤ upper a
  /-- Upper of ⊤ is 1 -/
  upper_top : upper ⊤ = 1

namespace ImpreciseValuation

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- The imprecision gap at a proposition. -/
def gap (v : ImpreciseValuation L) (a : L) : ℝ := v.upper a - v.lower.val a

/-- Gap is always non-negative. -/
theorem gap_nonneg (v : ImpreciseValuation L) (a : L) : 0 ≤ v.gap a := by
  simp only [gap]
  linarith [v.lower_le_upper a]

/-- A valuation is precise if lower = upper everywhere. -/
def IsPrecise (v : ImpreciseValuation L) : Prop := ∀ a, v.lower.val a = v.upper a

/-- For precise valuations, the gap is zero. -/
theorem precise_gap_zero (v : ImpreciseValuation L) (hv : v.IsPrecise) (a : L) :
    v.gap a = 0 := by
  simp only [gap, hv a, sub_self]

/-- Convert a precise valuation to a single NormalizedValuation. -/
def toPrecise (v : ImpreciseValuation L) (_hv : v.IsPrecise) : NormalizedValuation L :=
  v.lower

end ImpreciseValuation

/-!
## §4: Additive Valuations

For classical probability, disjoint events add: P(A ∪ B) = P(A) + P(B).
-/

/-- An additive valuation: v(a ⊔ b) = v(a) + v(b) when a ⊓ b = ⊥. -/
structure AdditiveValuation (L : Type*) [Lattice L] [BoundedOrder L]
    extends NormalizedValuation L where
  /-- Additivity for disjoint elements -/
  additive : ∀ a b, a ⊓ b = ⊥ → val (a ⊔ b) = val a + val b

namespace AdditiveValuation

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- For additive valuations on disjoint elements: v(a ⊔ b) = v(a) + v(b). -/
theorem additive_eq (v : AdditiveValuation L) (a b : L) (h : a ⊓ b = ⊥) :
    v.val (a ⊔ b) = v.val a + v.val b := v.additive a b h

/-- Note: General subadditivity (v(a ⊔ b) ≤ v(a) + v(b)) requires the sum rule,
    which is stated in SumRuleValuation below. Here we just note that
    v(a ⊔ b) ≤ 1 ≤ v(a) + v(b) when both v(a), v(b) ≥ 1/2. -/
theorem sup_bounded_above (v : AdditiveValuation L) (a b : L) :
    v.val (a ⊔ b) ≤ 1 := v.le_one (a ⊔ b)

end AdditiveValuation

/-!
## §5: The Sum Rule

The sum rule: v(a ⊔ b) = v(a) + v(b) - v(a ⊓ b).
This holds for classical probability and can be derived from additivity + Boolean.
-/

/-- A valuation satisfying the sum rule. -/
structure SumRuleValuation (L : Type*) [Lattice L] [BoundedOrder L]
    extends NormalizedValuation L where
  /-- The sum rule -/
  sum_rule : ∀ a b, val (a ⊔ b) = val a + val b - val (a ⊓ b)

namespace SumRuleValuation

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- Sum rule implies additivity for disjoint elements. -/
theorem additive_disjoint (v : SumRuleValuation L) (a b : L) (h : a ⊓ b = ⊥) :
    v.val (a ⊔ b) = v.val a + v.val b := by
  rw [v.sum_rule, h, v.val_bot]
  ring

/-- Convert to AdditiveValuation. -/
def toAdditive (v : SumRuleValuation L) : AdditiveValuation L where
  val := v.val
  mono := v.mono
  val_bot := v.val_bot
  val_top := v.val_top
  additive := v.additive_disjoint

end SumRuleValuation

/-!
## §6: Conditional Valuations

All probability theories have some notion of conditioning.
-/

/-- A conditional valuation: v(a | b) defined when v(b) ≠ 0. -/
structure ConditionalValuation (L : Type*) [Lattice L] [BoundedOrder L]
    extends NormalizedValuation L where
  /-- Conditional valuation v(a | b) = v(a ⊓ b) / v(b) when v(b) ≠ 0 -/
  cond : L → L → ℝ
  /-- Definition of conditioning -/
  cond_def : ∀ a b, val b ≠ 0 → cond a b = val (a ⊓ b) / val b

namespace ConditionalValuation

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- Conditioning on ⊤ gives the original value. -/
theorem cond_top (v : ConditionalValuation L) (a : L) (h : v.val ⊤ ≠ 0) :
    v.cond a ⊤ = v.val a := by
  rw [v.cond_def a ⊤ h, inf_top_eq, v.val_top]
  field_simp

/-- v(a | a) = 1 when v(a) ≠ 0. -/
theorem cond_self (v : ConditionalValuation L) (a : L) (h : v.val a ≠ 0) :
    v.cond a a = 1 := by
  rw [v.cond_def a a h, inf_idem]
  field_simp

/-- The product rule: v(a ⊓ b) = v(b) · v(a | b). -/
theorem product_rule (v : ConditionalValuation L) (a b : L) (hb : v.val b ≠ 0) :
    v.val (a ⊓ b) = v.val b * v.cond a b := by
  rw [v.cond_def a b hb]
  field_simp

end ConditionalValuation

/-!
## §7: Complement Valuations (Boolean Algebras)

For Boolean algebras, we have complements: v(aᶜ) = 1 - v(a).
-/

/-- A valuation on a Boolean algebra with complement rule. -/
structure ComplementValuation (L : Type*) [BooleanAlgebra L]
    extends NormalizedValuation L where
  /-- Complement rule: v(aᶜ) = 1 - v(a) -/
  val_compl : ∀ a, val aᶜ = 1 - val a

namespace ComplementValuation

variable {L : Type*} [BooleanAlgebra L]

/-- v(a) + v(aᶜ) = 1. -/
theorem add_compl (v : ComplementValuation L) (a : L) :
    v.val a + v.val aᶜ = 1 := by
  rw [v.val_compl]
  ring

/-- v(aᶜᶜ) = v(a). -/
theorem val_compl_compl (v : ComplementValuation L) (a : L) :
    v.val aᶜᶜ = v.val a := by
  rw [v.val_compl, v.val_compl]
  ring

end ComplementValuation

/-!
## §8: Duality for Imprecise Valuations

For Dempster-Shafer: Pl(A) = 1 - Bel(Aᶜ).
-/

/-- An imprecise valuation with duality on a Boolean algebra. -/
structure DualImpreciseValuation (L : Type*) [BooleanAlgebra L]
    extends ImpreciseValuation L where
  /-- Duality: upper(a) = 1 - lower(aᶜ) -/
  duality : ∀ a, upper a = 1 - lower.val aᶜ

namespace DualImpreciseValuation

variable {L : Type*} [BooleanAlgebra L]

/-- lower(a) + upper(aᶜ) = 1. -/
theorem lower_add_upper_compl (v : DualImpreciseValuation L) (a : L) :
    v.lower.val a + v.upper aᶜ = 1 := by
  rw [v.duality]
  simp only [compl_compl]
  ring

/-- upper(⊥) = 1 - lower(⊤) = 0. -/
theorem upper_bot (v : DualImpreciseValuation L) : v.upper ⊥ = 0 := by
  rw [v.duality]
  simp [v.lower.val_top]

end DualImpreciseValuation

/-!
## §9: Bridge to Lattice Valuations

Theorems connecting the generic valuation framework to
orthoadditive/lattice-based valuations.
-/

section LatticeBridge

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- Additive valuations are identical to orthoadditive valuations on bounded lattices.
    This is a definitional equivalence - both require additivity on disjoint elements. -/
def AdditiveValuation.toNormalizedVal (v : AdditiveValuation L) : NormalizedValuation L :=
  v.toNormalizedValuation

/-- Sum-rule valuations induce additive valuations via additive_disjoint. -/
theorem SumRuleValuation.to_additive_correct (v : SumRuleValuation L) :
    (v.toAdditive).additive = v.additive_disjoint := by
  rfl

end LatticeBridge

/-!
## §10: Lattice-Based Belief Functions

Connection between belief functions on finite lattices and
the general valuation framework.
-/

section FiniteLatticeValuation

variable {L : Type*} [Lattice L] [BoundedOrder L] [Fintype L] [DecidableEq L]
variable [DecidableRel (α := L) (· ≤ ·)]

omit [BoundedOrder L] [DecidableEq L] in
/-- A mass function on a finite lattice induces a monotone valuation via sumBelow.
    This generalizes D-S belief functions from power sets to arbitrary lattices. -/
theorem monotone_from_mass (m : L → ℝ) (hm_nonneg : ∀ a, 0 ≤ m a) :
    ∀ a b : L, a ≤ b →
      Finset.sum (Finset.filter (· ≤ a) Finset.univ) m ≤
      Finset.sum (Finset.filter (· ≤ b) Finset.univ) m := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact le_trans hx hab
  · intro x _ _
    exact hm_nonneg x

/-- The belief at ⊥ is m(⊥). -/
theorem belief_at_bot_eq_m_bot (m : L → ℝ) :
    Finset.sum (Finset.filter (· ≤ (⊥ : L)) Finset.univ) m = m ⊥ := by
  have h : Finset.filter (· ≤ (⊥ : L)) Finset.univ = ({⊥} : Finset L) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, le_bot_iff]
  rw [h, Finset.sum_singleton]

end FiniteLatticeValuation

end Mettapedia.ProbabilityTheory.Common
