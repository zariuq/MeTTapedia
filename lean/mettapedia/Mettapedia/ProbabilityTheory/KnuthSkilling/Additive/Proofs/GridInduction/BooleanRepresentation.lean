import Mathlib.Data.Real.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Tactic

/-!
# K&S Boolean Representation

This file defines the `KSBooleanRepresentation` structure for representing
K&S probability on Boolean algebras. This is a **standalone** file with
NO dependencies on PLN or other application-specific modules.

## Main Definitions

* `KSRepresentation` - An additive order-preserving map to ℝ≥0
* `KSBooleanRepresentation` - K&S representation on a Boolean algebra with modularity
* `probability` - Normalized probability P(a) = Θ(a) / Θ(⊤)
* `condProb` - Conditional probability P(b|a)

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
- ToProbDist.lean for the direct KS → ProbDist path (preferred)
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.BooleanRepresentation

/-!
## §1: K&S Representation Structure

We work with the representation theorem output: an additive order embedding Θ.
-/

/-- The K&S representation: an additive order-preserving map to ℝ≥0 -/
structure KSRepresentation (α : Type*) [LE α] where
  /-- The additive valuation -/
  Θ : α → ℝ
  /-- Non-negativity -/
  Θ_nonneg : ∀ a, 0 ≤ Θ a
  /-- Order preservation -/
  Θ_mono : ∀ a b, a ≤ b → Θ a ≤ Θ b

/-- A K&S representation on a Boolean algebra with additivity -/
structure KSBooleanRepresentation (α : Type*) [BooleanAlgebra α] extends KSRepresentation α where
  /-- Modularity: Θ(a ∨ b) + Θ(a ∧ b) = Θ(a) + Θ(b) -/
  Θ_modular : ∀ a b, Θ (a ⊔ b) + Θ (a ⊓ b) = Θ a + Θ b
  /-- Bottom is zero -/
  Θ_bot : Θ ⊥ = 0

namespace KSBooleanRepresentation

variable {α : Type*} [BooleanAlgebra α] (R : KSBooleanRepresentation α)

/-!
## §2: Normalization to Probability
-/

/-- Normalized probability: P(a) = Θ(a) / Θ(⊤) -/
noncomputable def probability (a : α) : ℝ :=
  if _h : R.Θ ⊤ = 0 then 0 else R.Θ a / R.Θ ⊤

/-- P(⊤) = 1 when Θ(⊤) ≠ 0 -/
theorem probability_top (h : R.Θ ⊤ ≠ 0) : R.probability ⊤ = 1 := by
  unfold probability
  rw [dif_neg h]
  exact div_self h

/-- When Θ(⊤) ≠ 0, probability eliminates the dite to give Θ(a) / Θ(⊤) -/
theorem probability_eq_div (h : R.Θ ⊤ ≠ 0) (a : α) :
    R.probability a = R.Θ a / R.Θ ⊤ := by
  unfold probability
  rw [dif_neg h]

/-- P(⊥) = 0 -/
theorem probability_bot : R.probability ⊥ = 0 := by
  unfold probability
  split_ifs with h
  · rfl
  · simp [R.Θ_bot]

/-- P is non-negative -/
theorem probability_nonneg (a : α) : 0 ≤ R.probability a := by
  unfold probability
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg (R.Θ_nonneg a) (R.Θ_nonneg ⊤)

/-- P(a) ≤ 1 when a ≤ ⊤ -/
theorem probability_le_one (a : α) : R.probability a ≤ 1 := by
  unfold probability
  split_ifs with h
  · exact zero_le_one
  · have h_top_pos : 0 < R.Θ ⊤ := lt_of_le_of_ne (R.Θ_nonneg ⊤) (Ne.symm h)
    rw [div_le_one h_top_pos]
    exact R.Θ_mono a ⊤ le_top

/-- P is in [0, 1] -/
theorem probability_mem_unit (a : α) : R.probability a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨R.probability_nonneg a, R.probability_le_one a⟩

/-- Finite additivity from modularity -/
theorem probability_modular (a b : α) (h : R.Θ ⊤ ≠ 0) :
    R.probability (a ⊔ b) + R.probability (a ⊓ b) = R.probability a + R.probability b := by
  simp only [probability, h, ↓reduceDIte]
  rw [← add_div, ← add_div, R.Θ_modular]

/-!
## §3: Conditional Probability
-/

/-- Conditional probability: P(b|a) = P(a ⊓ b) / P(a) -/
noncomputable def condProb (b a : α) : ℝ :=
  if _h : R.probability a = 0 then 0 else R.probability (a ⊓ b) / R.probability a

/-- The key lemma: P(a ⊓ b) = P(a) · P(b|a) -/
theorem prob_inf_eq_mul_cond (a b : α) (ha : R.probability a ≠ 0) :
    R.probability (a ⊓ b) = R.probability a * R.condProb b a := by
  simp [condProb, ha, mul_div_cancel₀]

/-!
## §4: Fréchet Bounds

The Fréchet bounds are a consequence of the Boolean algebra structure
and the non-negativity of Θ.
-/

/-- Fréchet lower bound: P(a ⊓ b) ≥ max(0, P(a) + P(b) - 1) -/
theorem frechet_lower (a b : α) (h : R.Θ ⊤ ≠ 0) :
    max 0 (R.probability a + R.probability b - 1) ≤ R.probability (a ⊓ b) := by
  apply max_le
  · exact R.probability_nonneg (a ⊓ b)
  · -- From modularity: P(a) + P(b) = P(a ⊔ b) + P(a ⊓ b)
    -- So P(a ⊓ b) = P(a) + P(b) - P(a ⊔ b) ≥ P(a) + P(b) - 1
    have hmod := R.probability_modular a b h
    have hle : R.probability (a ⊔ b) ≤ 1 := R.probability_le_one (a ⊔ b)
    -- linarith can use both equality (hmod) and inequality (hle) directly
    linarith

/-- Fréchet upper bound: P(a ⊓ b) ≤ min(P(a), P(b)) -/
theorem frechet_upper (a b : α) :
    R.probability (a ⊓ b) ≤ min (R.probability a) (R.probability b) := by
  apply le_min
  · -- P(a ⊓ b) ≤ P(a) since a ⊓ b ≤ a
    unfold probability
    split_ifs with h
    · exact le_refl 0
    · apply div_le_div_of_nonneg_right _ (R.Θ_nonneg ⊤)
      exact R.Θ_mono (a ⊓ b) a inf_le_left
  · -- P(a ⊓ b) ≤ P(b) since a ⊓ b ≤ b
    unfold probability
    split_ifs with h
    · exact le_refl 0
    · apply div_le_div_of_nonneg_right _ (R.Θ_nonneg ⊤)
      exact R.Θ_mono (a ⊓ b) b inf_le_right

end KSBooleanRepresentation

end Mettapedia.ProbabilityTheory.KnuthSkilling.BooleanRepresentation
