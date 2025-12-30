/-
# Lattice Valuation Infrastructure

Generalized valuations on lattices that unify classical and quantum probability.

## Key Concepts

- **OrthoadditiveValuation**: Additive on orthogonal pairs (a ⊓ b = ⊥)
- **BeliefFromMass**: Construct a valuation from a mass function via sumBelow
- **Bridge theorems**: Connect to classical AdditiveValuation

## Design Philosophy

On finite lattices, "measure theory" becomes finite summation:
- Classical: sum over sets below
- Quantum: sum over projections below

Both use `sumBelow` from LatticeSummation.lean as the foundation.
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.Common.Valuation
import Mettapedia.ProbabilityTheory.Common.LatticeSummation

namespace Mettapedia.ProbabilityTheory.Common

/-!
## §1: Orthoadditive Valuations

A valuation is orthoadditive if it's additive on orthogonal pairs:
`v(a ⊔ b) = v(a) + v(b)` when `a ⊓ b = ⊥`.

This is exactly what classical probability says about disjoint events,
but here we make no assumption about distributivity.
-/

/-- An orthoadditive valuation on a bounded lattice.
    This generalizes classical additivity to non-Boolean lattices.

    Key property: v(a ⊔ b) = v(a) + v(b) when a ⊓ b = ⊥ (orthogonal).
    On Boolean algebras, this is exactly classical probability.
    On orthomodular lattices, this captures quantum probability. -/
structure OrthoadditiveValuation (L : Type*) [Lattice L] [BoundedOrder L]
    extends NormalizedValuation L where
  /-- Additivity for orthogonal (disjoint) elements -/
  orthoadditive : ∀ a b, a ⊓ b = ⊥ → val (a ⊔ b) = val a + val b

namespace OrthoadditiveValuation

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- For orthogonal elements: v(a ⊔ b) = v(a) + v(b). -/
theorem add_ortho (v : OrthoadditiveValuation L) {a b : L} (h : a ⊓ b = ⊥) :
    v.val (a ⊔ b) = v.val a + v.val b := v.orthoadditive a b h

/-- Orthoadditivity implies subadditivity for orthogonal pairs. -/
theorem sub_of_ortho (v : OrthoadditiveValuation L) {a b : L} (h : a ⊓ b = ⊥) :
    v.val (a ⊔ b) ≤ v.val a + v.val b := by
  rw [v.add_ortho h]

/-- v(a) = v(a ⊔ ⊥) = v(a) + v(⊥). -/
theorem add_bot (v : OrthoadditiveValuation L) (a : L) :
    v.val a + v.val ⊥ = v.val a := by
  rw [v.val_bot]; ring

/-- For complement pairs in Boolean algebras: v(a) + v(aᶜ) = 1. -/
theorem add_compl' {L' : Type*} [BooleanAlgebra L']
    (v : OrthoadditiveValuation L') (a : L') :
    v.val a + v.val aᶜ = 1 := by
  have h : a ⊓ aᶜ = ⊥ := inf_compl_eq_bot
  have htop : a ⊔ aᶜ = ⊤ := sup_compl_eq_top
  calc v.val a + v.val aᶜ = v.val (a ⊔ aᶜ) := (v.orthoadditive a aᶜ h).symm
       _ = v.val ⊤ := by rw [htop]
       _ = 1 := v.val_top

/-- In a Boolean algebra, orthoadditive implies the complement rule. -/
theorem val_compl_eq' {L' : Type*} [BooleanAlgebra L']
    (v : OrthoadditiveValuation L') (a : L') :
    v.val aᶜ = 1 - v.val a := by
  have h := v.add_compl' a
  linarith

/-- Every AdditiveValuation is an OrthoadditiveValuation. -/
def ofAdditive (v : AdditiveValuation L) : OrthoadditiveValuation L where
  toNormalizedValuation := v.toNormalizedValuation
  orthoadditive := v.additive

/-- Convert an OrthoadditiveValuation to an AdditiveValuation (same structure). -/
def toAdditive (v : OrthoadditiveValuation L) : AdditiveValuation L where
  toNormalizedValuation := v.toNormalizedValuation
  additive := v.orthoadditive

end OrthoadditiveValuation

/-!
## §2: Belief Functions from Mass

Given a mass function m : L → ℝ with m(⊥) = 0 and m ≥ 0,
we can construct a belief function via `sumBelow`.

This is the core construction that works for:
- Classical D-S belief functions
- Quantum belief functions on orthomodular lattices
-/

section BeliefFromMass

variable {L : Type*} [Lattice L] [BoundedOrder L] [Fintype L] [DecidableEq L]
variable [DecidableRel (α := L) (· ≤ ·)]

/-- A mass function on a finite lattice.
    This is the core data for constructing a belief function. -/
structure MassFunction (L : Type*) [Lattice L] [BoundedOrder L] where
  /-- The mass assignment -/
  m : L → ℝ
  /-- No mass on bottom -/
  m_bot : m ⊥ = 0
  /-- Non-negative masses -/
  m_nonneg : ∀ a, 0 ≤ m a

namespace MassFunction

/-- Belief at an element: sum of masses below. -/
noncomputable def belief [DecidableRel (α := L) (· ≤ ·)]
    (mf : MassFunction L) (a : L) : ℝ :=
  sumBelow mf.m a

/-- Total mass (belief at ⊤). -/
noncomputable def totalMass [DecidableRel (α := L) (· ≤ ·)]
    (mf : MassFunction L) : ℝ :=
  mf.belief ⊤

/-- Belief at ⊥ is m(⊥) = 0. -/
@[simp]
theorem belief_bot (mf : MassFunction L) : mf.belief ⊥ = 0 := by
  simp [belief, mf.m_bot]

/-- Belief is monotone. -/
theorem belief_mono (mf : MassFunction L) {a b : L} (h : a ≤ b) :
    mf.belief a ≤ mf.belief b :=
  sumBelow.mono_of_nonneg mf.m mf.m_nonneg h

/-- Belief is non-negative. -/
theorem belief_nonneg (mf : MassFunction L) (a : L) : 0 ≤ mf.belief a :=
  sumBelow.nonneg_of_nonneg mf.m mf.m_nonneg a

/-- m(a) ≤ belief(a). -/
theorem m_le_belief (mf : MassFunction L) (a : L) : mf.m a ≤ mf.belief a :=
  sumBelow.self_le_of_nonneg mf.m mf.m_nonneg a

/-- Belief at any element is at most total mass. -/
theorem belief_le_totalMass (mf : MassFunction L) (a : L) :
    mf.belief a ≤ mf.totalMass :=
  mf.belief_mono le_top

/-- A normalized mass function has total mass 1. -/
def IsNormalized (mf : MassFunction L) : Prop := mf.totalMass = 1

/-- If normalized, belief forms a MonotoneValuation. -/
noncomputable def toMonotoneValuation (mf : MassFunction L) : MonotoneValuation L where
  val := mf.belief
  mono := fun a b h => mf.belief_mono h

/-- If normalized, belief forms a NormalizedValuation. -/
noncomputable def toNormalizedValuation (mf : MassFunction L) (hn : mf.IsNormalized) :
    NormalizedValuation L where
  val := mf.belief
  mono := fun a b h => mf.belief_mono h
  val_bot := mf.belief_bot
  val_top := hn

end MassFunction

end BeliefFromMass

/-!
## §3: Bridge to Boolean Algebras

On Boolean algebras, the sum rule holds: v(a ⊔ b) = v(a) + v(b) - v(a ⊓ b).
This follows from orthoadditive + Boolean structure.
-/

section BooleanBridge

/-- On Boolean algebras, orthoadditive valuations satisfy the sum rule. -/
theorem OrthoadditiveValuation.sum_rule_on_boolean {L : Type*} [BooleanAlgebra L]
    (v : OrthoadditiveValuation L) (a b : L) :
    v.val (a ⊔ b) = v.val a + v.val b - v.val (a ⊓ b) := by
  -- Use distributivity to decompose a ⊔ b
  -- a ⊔ b = a ⊔ (b \ a) where b \ a = b ⊓ aᶜ
  -- and a ⊓ (b ⊓ aᶜ) = ⊥
  have hdisj : a ⊓ (b ⊓ aᶜ) = ⊥ := by
    calc a ⊓ (b ⊓ aᶜ) = (a ⊓ aᶜ) ⊓ b := by ac_rfl
         _ = ⊥ ⊓ b := by rw [inf_compl_eq_bot]
         _ = ⊥ := by simp
  have hsup : a ⊔ b = a ⊔ (b ⊓ aᶜ) := by
    -- a ⊔ b = a ⊔ (b ⊓ (a ⊔ aᶜ)) = a ⊔ ((b ⊓ a) ⊔ (b ⊓ aᶜ)) = (a ⊔ (b ⊓ a)) ⊔ (b ⊓ aᶜ)
    -- = a ⊔ (b ⊓ aᶜ) since a ⊔ (b ⊓ a) = a
    have h2 : b ⊓ (a ⊔ aᶜ) = (b ⊓ a) ⊔ (b ⊓ aᶜ) := inf_sup_left b a aᶜ
    have h3 : a ⊔ (a ⊓ b) = a := sup_inf_self
    calc a ⊔ b = a ⊔ (b ⊓ (a ⊔ aᶜ)) := by rw [sup_compl_eq_top, inf_top_eq]
         _ = a ⊔ ((b ⊓ a) ⊔ (b ⊓ aᶜ)) := by rw [h2]
         _ = a ⊔ ((a ⊓ b) ⊔ (b ⊓ aᶜ)) := by rw [inf_comm b a]
         _ = (a ⊔ (a ⊓ b)) ⊔ (b ⊓ aᶜ) := by rw [sup_assoc]
         _ = a ⊔ (b ⊓ aᶜ) := by rw [h3]
  rw [hsup, v.add_ortho hdisj]
  -- Now we need: v(b ⊓ aᶜ) = v(b) - v(a ⊓ b)
  -- This uses: b = (a ⊓ b) ⊔ (b ⊓ aᶜ) and (a ⊓ b) ⊓ (b ⊓ aᶜ) = ⊥
  have hb_disj : (a ⊓ b) ⊓ (b ⊓ aᶜ) = ⊥ := by
    calc (a ⊓ b) ⊓ (b ⊓ aᶜ) = (a ⊓ aᶜ) ⊓ (b ⊓ b) := by ac_rfl
         _ = ⊥ ⊓ b := by rw [inf_compl_eq_bot, inf_idem]
         _ = ⊥ := by simp
  have hb_eq : b = (a ⊓ b) ⊔ (b ⊓ aᶜ) := by
    calc b = b ⊓ ⊤ := by rw [inf_top_eq]
         _ = b ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top]
         _ = (b ⊓ a) ⊔ (b ⊓ aᶜ) := by rw [inf_sup_left]
         _ = (a ⊓ b) ⊔ (b ⊓ aᶜ) := by rw [inf_comm]
  have hval_b : v.val b = v.val (a ⊓ b) + v.val (b ⊓ aᶜ) := by
    conv_lhs => rw [hb_eq]
    exact v.add_ortho hb_disj
  linarith

/-- Convert orthoadditive to sum-rule valuation on Boolean algebras. -/
noncomputable def OrthoadditiveValuation.toSumRule {L : Type*} [BooleanAlgebra L]
    (v : OrthoadditiveValuation L) : SumRuleValuation L where
  toNormalizedValuation := v.toNormalizedValuation
  sum_rule := v.sum_rule_on_boolean

/-- On Boolean algebras, orthoadditive = sum-rule = additive (equivalent). -/
theorem orthoadditive_eq_additive_on_boolean {L : Type*} [BooleanAlgebra L] :
    ∀ (v : OrthoadditiveValuation L), v.toAdditive.additive = v.orthoadditive := by
  intro v
  rfl

end BooleanBridge

/-!
## §4: Orthomodular Valuation

For orthomodular lattices (quantum logic), we have a specialized valuation
that respects the orthomodular structure.
-/

/-- HasCompl provides complement operation. -/
class HasOrthocomplement (L : Type*) extends HasCompl L where
  compl_compl : ∀ a : L, aᶜᶜ = a

/-- An orthomodular valuation: orthoadditive + respects complements.
    This is the quantum analog of a probability measure. -/
structure OrthomodularValuation (L : Type*) [Lattice L] [BoundedOrder L] [HasCompl L]
    extends OrthoadditiveValuation L where
  /-- v(aᶜ) = 1 - v(a) (complement rule) -/
  val_compl : ∀ a, val aᶜ = 1 - val a

namespace OrthomodularValuation

variable {L : Type*} [Lattice L] [BoundedOrder L] [HasCompl L]

/-- v(a) + v(aᶜ) = 1. -/
theorem add_compl (v : OrthomodularValuation L) (a : L) :
    v.val a + v.val aᶜ = 1 := by
  rw [v.val_compl]
  ring

/-- v(⊥ᶜ) = 1. -/
theorem val_compl_bot (v : OrthomodularValuation L) [inst : HasOrthocomplement L]
    (h : (⊥ : L)ᶜ = ⊤) : v.val (⊥ : L)ᶜ = 1 := by
  rw [h, v.val_top]

/-- v(⊤ᶜ) = 0. -/
theorem val_compl_top (v : OrthomodularValuation L) [inst : HasOrthocomplement L]
    (h : (⊤ : L)ᶜ = ⊥) : v.val (⊤ : L)ᶜ = 0 := by
  rw [h, v.val_bot]

end OrthomodularValuation

/-!
## §5: Imprecise Lattice Valuations

For imprecise probability on lattices, we have lower and upper valuations
with lower ≤ upper pointwise.
-/

/-- An imprecise valuation on a lattice: [lower, upper] bounds. -/
structure ImpreciseLatticeValuation (L : Type*) [Lattice L] [BoundedOrder L] where
  /-- Lower valuation (belief-like) -/
  lower : MonotoneValuation L
  /-- Upper valuation (plausibility-like) -/
  upper : L → ℝ
  /-- Upper is at least lower -/
  lower_le_upper : ∀ a, lower.val a ≤ upper a
  /-- Lower normalized at bottom -/
  lower_bot : lower.val ⊥ = 0
  /-- Upper normalized at top -/
  upper_top : upper ⊤ = 1

namespace ImpreciseLatticeValuation

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- The imprecision gap. -/
def gap (v : ImpreciseLatticeValuation L) (a : L) : ℝ :=
  v.upper a - v.lower.val a

/-- Gap is non-negative. -/
theorem gap_nonneg (v : ImpreciseLatticeValuation L) (a : L) : 0 ≤ v.gap a := by
  simp only [gap]
  linarith [v.lower_le_upper a]

/-- A valuation is precise if lower = upper everywhere. -/
def IsPrecise (v : ImpreciseLatticeValuation L) : Prop :=
  ∀ a, v.lower.val a = v.upper a

end ImpreciseLatticeValuation

end Mettapedia.ProbabilityTheory.Common
