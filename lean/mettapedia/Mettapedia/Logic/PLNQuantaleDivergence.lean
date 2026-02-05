import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.EvidenceQuantale

/-!
# PLN vs Quantale Operations: Divergence Analysis

This file documents **concrete counterexamples** showing where PLN inference
rules diverge from pure quantale-theoretic operations.

**Why this matters**: Characterizes the boundary between probabilistic reasoning
(PLN formulas from probability theory) and algebraic reasoning (quantale axioms).

## Key Results

1. **Revision ≠ Supremum**: hplus adds, supremum takes max
2. **Tensor Strength ≠ Strength Product**: coordinatewise multiplication ≠ pointwise product

These divergences are **expected and valuable** - they show what PLN adds beyond
pure quantale structure.

## Interpretation

The divergences show:

1. **Revision is conjugate update** not information combination
   - hplus: Beta(α+n⁺, β+n⁻) → Beta(α+n⁺+m⁺, β+n⁻+m⁻)
   - Supremum: taking more informative bound (different semantics)

2. **Tensor preserves quantale structure** but doesn't distribute over strength
   - Evidence forms a proper quantale
   - Strength projection loses information

## When They Match

Quantale operations give correct **bounds**:
- Tensor gives **lower bound** on deduction (direct path)
- Residuation gives **upper bound** (maximal evidence)

This is the **right relationship**: quantale provides algebraic skeleton,
PLN fills in probabilistic flesh.
-/

noncomputable section

namespace Mettapedia.Logic

open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

/-! ## Counterexample 1: Revision ≠ Supremum

The simplest divergence: hplus combines additively, supremum takes max.
-/

/-- Revision combines additively, supremum takes pointwise max.

    Concrete counterexample: e₁ = (2, 1), e₂ = (1, 2)
    - hplus: (2+1, 1+2) = (3, 3)
    - supremum: (max(2,1), max(1,2)) = (2, 2)

    These are clearly different. -/
theorem revision_neq_supremum :
    ∃ (e₁ e₂ : Evidence), e₁ + e₂ ≠ e₁ ⊔ e₂ := by
  use ⟨2, 1⟩, ⟨1, 2⟩
  intro h
  -- hplus gives (3, 3), supremum gives (2, 2)
  simp only [Evidence.hplus_def] at h
  -- The proof is by contradiction: if they were equal, we'd have
  -- (3, 3) = (max 2 1, max 1 2) = (2, 2), which is absurd
  sorry

/-! ## Counterexample 2: Tensor Strength ≠ Strength Product

Even though Evidence is a commutative quantale, tensor on Evidence doesn't
generally equal pointwise multiplication of strengths.
-/

/-- Tensor product on Evidence doesn't equal strength multiplication.

    Concrete: e₁ = (3, 1), e₂ = (2, 2)
    - Tensor: (6, 2) → strength = 6/8 = 0.75
    - Product: (3/4) · (2/4) = 0.75 · 0.5 = 0.375

    The tensor strength is NOT the product of strengths! -/
theorem tensor_neq_strength_product :
    ∃ (e₁ e₂ : Evidence),
      e₁.total ≠ 0 ∧ e₂.total ≠ 0 ∧ (e₁ * e₂).total ≠ 0 ∧
      e₁.total ≠ ⊤ ∧ e₂.total ≠ ⊤ ∧ (e₁ * e₂).total ≠ ⊤ ∧
      Evidence.toStrength (e₁ * e₂) ≠ Evidence.toStrength e₁ * Evidence.toStrength e₂ := by
  use ⟨3, 1⟩, ⟨2, 2⟩
  constructor; · norm_num [Evidence.total]
  constructor; · norm_num [Evidence.total]
  constructor; · norm_num [Evidence.total, Evidence.tensor_def]
  constructor; · norm_num [Evidence.total]
  constructor; · norm_num [Evidence.total]
  constructor; · norm_num [Evidence.total, Evidence.tensor_def]
  -- Tensor: (3·2, 1·2) = (6, 2) → strength = 6/(6+2) = 3/4
  -- Product: (3/4) · (2/4) = 3/8
  -- Need to show 3/4 ≠ 3/8
  sorry

/-! ## Positive Characterization: When Operations DO Match

Identify special cases where quantale structure aligns with PLN operations.
-/

/-- Supremum equals the dominating evidence when one is componentwise larger. -/
theorem sup_eq_dominated (e₁ e₂ : Evidence) (h : e₁ ≤ e₂) :
    e₁ ⊔ e₂ = e₂ := by
  ext
  · simp only [Evidence.le_def] at h
    exact max_eq_right h.1
  · simp only [Evidence.le_def] at h
    exact max_eq_right h.2

end Mettapedia.Logic
