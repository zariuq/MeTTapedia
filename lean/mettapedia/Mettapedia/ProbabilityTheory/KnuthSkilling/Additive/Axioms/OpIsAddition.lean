/-
# K&S Operation is Addition (Derived Result)

## Summary

The Knuth-Skilling representation theorem **proves** that `op` becomes ordinary addition
under the embedding Θ : S → ℝ. This is **NOT an assumption but a THEOREM**.

## The Key Result

Given `[KnuthSkillingAlgebra α]` + `[NoAnomalousPairs α]` (or equivalently `[KSSeparation α]`):

  ∃ Θ : α → ℝ, Θ(op x y) = Θ x + Θ y

This is proven via:
1. `NoAnomalousPairs` → order embedding into (ℝ≥0, ×) via Hölder theorem
2. (ℝ≥0, ×) ≅ (ℝ, +) via logarithm
3. Composition gives Θ : α → ℝ with Θ(op x y) = Θ x + Θ y

Alternatively via the K&S separation path:
1. `KSSeparation` → Commutativity (`SandwichSeparation.lean`)
2. Commutativity + Archimedean → Hölder embedding (`HolderEmbedding.lean`)
3. Hölder embedding → Additivity

## Uniqueness

The representation is unique up to positive scaling:
- **Additive constant**: fixed by Θ(ident) = 0
- **Multiplicative constant**: free (choose a reference element for scale)

If Θ₁ and Θ₂ are both valid representations with Θ₁(ident) = Θ₂(ident) = 0,
then ∃ c > 0, Θ₂ = c · Θ₁.

## Mathematical Significance

This justifies interpreting K&S plausibility as "log-probability":
- If Θ(a) represents log P(a), then Θ(a ⊕ b) = Θ(a) + Θ(b)
- For independent events: log P(A∩B) = log P(A) + log P(B)
- **The K&S operation `op` IS addition in the representation space**

This is the theoretical foundation for treating the K&S scale as an additive structure,
enabling the connection to mathlib's measure theory.

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
- Luap, E. (2024). "OrderedSemigroups: Formalization in Lean 4"
- Hölder, O. (1901). "Die Axiome der Quantität und die Lehre vom Mass"
- Alimov, N. G. (1950). "On ordered semigroups"
-/

import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.SandwichSeparation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.OpIsAddition

open KnuthSkillingMonoidBase KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.OrderedSemigroupEmbedding.HolderEmbedding
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.AnomalousPairs

/-! ## Section 1: The Main Derived Result -/

/-- **K&S Representation Theorem: op becomes + under embedding**

This is a DERIVED result, not an assumption. Given:
- `[KnuthSkillingMonoidBase α]` (the basic K&S axioms, with identity)
- `[NoAnomalousPairs α]` (no oscillating power sequences)

There exists Θ : α → ℝ such that:
1. **Order-preserving**: a ≤ b ↔ Θ a ≤ Θ b
2. **Normalized**: Θ(ident) = 0
3. **Additive**: Θ(op x y) = Θ x + Θ y

The last property is the key: it says that `op` becomes ordinary `+` in ℝ.

This theorem is what justifies treating the K&S scale as an additive structure
and connecting it to mathlib's measure theory. -/
theorem op_is_addition_via_Θ (α : Type*) [KnuthSkillingMonoidBase α] [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      (∀ x y : α, Θ (op x y) = Θ x + Θ y) :=
  representation_from_noAnomalousPairs

/-- Identity-free version: existence of an additive order embedding (no normalization). -/
theorem op_is_addition_via_Θ_semigroup (α : Type*) [KSSemigroupBase α] [NoAnomalousPairs α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      (∀ x y : α, Θ (op x y) = Θ x + Θ y) :=
  representation_semigroup

/-- Alternative path via KSSeparation (the original K&S approach).

`KSSeparation` is the "sandwich axiom" from K&S Appendix A. It implies:
1. Commutativity of `op`
2. The Archimedean property
3. No anomalous pairs

And thus the representation theorem follows. -/
theorem op_is_addition_via_KSSeparation (α : Type*)
    [KnuthSkillingAlgebraBase α] [KSSeparation α] [KSSeparationStrict α] :
    ∃ Θ : α → ℝ,
      (∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b) ∧
      Θ ident = 0 ∧
      (∀ x y : α, Θ (op x y) = Θ x + Θ y) :=
by
  obtain ⟨Θ, hΘ_order, hΘ_add⟩ := HasRepresentationTheorem.exists_representation (α := α)
  have hΘ_ident : Θ ident = 0 := by
    -- Θ ident = Θ ident + Θ ident
    have h := hΘ_add ident ident
    have h' : Θ ident = Θ ident + Θ ident := by
      simpa [op_ident_left] using h
    linarith
  exact ⟨Θ, hΘ_order, hΘ_ident, hΘ_add⟩

/-! ## Section 2: Consequences of Additivity -/

/-- Commutativity is a consequence of the additive representation.

If Θ(op x y) = Θ x + Θ y, then since + is commutative in ℝ, we have
Θ(op x y) = Θ(op y x), and since Θ is injective (order-preserving), op x y = op y x. -/
theorem op_comm_from_representation (α : Type*) [KSSemigroupBase α] [HasRepresentationTheorem α] :
    ∀ x y : α, op x y = op y x :=
  Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.op_comm_of_hasRepresentationTheorem (α := α)

/-- Iterate of op becomes multiplication in the representation.

Θ(x ⊕ x ⊕ ... ⊕ x) = n · Θ(x) -/
theorem iterate_op_is_smul (α : Type*) [KnuthSkillingMonoidBase α]
    (Θ : α → ℝ) (hΘ_ident : Θ ident = 0) (hΘ_add : ∀ x y : α, Θ (op x y) = Θ x + Θ y) :
    ∀ (x : α) (n : ℕ), Θ (iterate_op x n) = n * Θ x := by
  intro x n
  induction n with
  | zero => simp [iterate_op_zero, hΘ_ident]
  | succ n ih =>
    rw [iterate_op_succ, hΘ_add, ih]
    simp only [Nat.cast_succ]
    ring

/-! ## Section 3: Uniqueness (Up to Positive Scaling)

The representation Θ : α → ℝ satisfying the three properties is unique up to
a positive multiplicative constant. The additive constant is fixed by Θ(ident) = 0.
-/

/-- If two representations agree at identity, they differ by a positive scale factor.

This is a direct application of `representation_uniqueness_structure` from HolderEmbedding.lean,
which proves uniqueness using the Archimedean property inherent in NoAnomalousPairs. -/
theorem representation_unique_up_to_scale (α : Type*) [KnuthSkillingMonoidBase α]
    (Θ₁ Θ₂ : α → ℝ)
    (hΘ₁_order : ∀ a b : α, a ≤ b ↔ Θ₁ a ≤ Θ₁ b)
    (hΘ₂_order : ∀ a b : α, a ≤ b ↔ Θ₂ a ≤ Θ₂ b)
    (hΘ₁_ident : Θ₁ ident = 0)
    (hΘ₂_ident : Θ₂ ident = 0)
    (hΘ₁_add : ∀ x y : α, Θ₁ (op x y) = Θ₁ x + Θ₁ y)
    (hΘ₂_add : ∀ x y : α, Θ₂ (op x y) = Θ₂ x + Θ₂ y)
    (a : α) (ha : ident < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : α, Θ₂ x = c * Θ₁ x :=
  representation_uniqueness_structure_of_ref Θ₁ Θ₂ hΘ₁_order hΘ₂_order hΘ₁_add hΘ₂_add hΘ₁_ident hΘ₂_ident a ha

/-! ## Section 4: Documentation Summary

### What This File Establishes

1. **Main Theorem** (`op_is_addition_via_Θ`):
   - K&S axioms + NoAnomalousPairs → ∃ Θ : α → ℝ with Θ(op x y) = Θ x + Θ y
   - This is DERIVED, not assumed

2. **Consequences**:
   - Commutativity of `op` follows from additivity
   - Powers become scalar multiples: Θ(x^n) = n · Θ(x)

3. **Uniqueness**:
   - The representation is unique up to positive scaling
   - Normalization Θ(ident) = 0 fixes the additive constant
   - A choice of scale (reference element) fixes the multiplicative constant

### Why This Matters

This theorem is the **theoretical foundation** for:
- Treating K&S plausibility as log-probability
- Connecting K&S to mathlib's measure theory (via additive structure)
- Justifying the transition from `op` to `+` in the scale

The key point: **we don't assume op is like +; we PROVE it**.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms.OpIsAddition
