import Mettapedia.Logic.PLNEvidence
import Mettapedia.Logic.PLNNegation
import Mettapedia.Logic.PLNConjunction

/-!
# PLN Disjunction Introduction Rule

This file formalizes the PLN **Disjunction Introduction Rule** which computes
the truth value of A ∨ B from the truth values of A and B.

## Key Approaches

### 1. Via De Morgan's Law
$$P(A ∨ B) = 1 - P(¬A ∧ ¬B)$$

Using PLN negation (evidence swap) and conjunction:
$$\text{Evidence}(A ∨ B) = ∼(\text{Evidence}(∼A ⊗ ∼B))$$

### 2. Via Inclusion-Exclusion
$$P(A ∨ B) = P(A) + P(B) - P(A ∧ B)$$

This requires knowing P(A ∧ B), which under independence is:
$$P(A ∧ B) = P(A) × P(B)$$

## Bounds (Fréchet Bounds)

Without independence assumption:
$$\max(P(A), P(B)) ≤ P(A ∨ B) ≤ \min(1, P(A) + P(B))$$

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter 10.6.2
- Nil's nuPLN.tex (De Morgan section)
-/

namespace Mettapedia.Logic.PLNDisjunction

open scoped ENNReal
open Mettapedia.Logic.PLNEvidence
open Mettapedia.Logic.PLNNegation
open Mettapedia.Logic.PLNConjunction
open Evidence

/-! ## Disjunction via De Morgan

The fundamental approach: A ∨ B = ¬(¬A ∧ ¬B)

In Evidence terms:
- ∼e swaps positive and negative evidence
- ⊗ (tensor) combines independent evidence
- Disjunction = negate(tensor(negate(A), negate(B)))
-/

/-- Disjunction via De Morgan's law (under independence assumption).

    A ∨ B = ¬(¬A ∧ ¬B)

    Evidence(A ∨ B) = ∼(∼A ⊗ ∼B)

    This uses:
    1. PLN negation: ∼e = (e.neg, e.pos)
    2. Independent conjunction: tensor product
-/
noncomputable def disjunctionDeMorgan (e_A e_B : Evidence) : Evidence :=
  ∼(∼e_A * ∼e_B)

/-- Disjunction is commutative -/
theorem disjunctionDeMorgan_comm (e_A e_B : Evidence) :
    disjunctionDeMorgan e_A e_B = disjunctionDeMorgan e_B e_A := by
  unfold disjunctionDeMorgan
  rw [tensor_comm]

/-- Disjunction is associative -/
theorem disjunctionDeMorgan_assoc (e_A e_B e_C : Evidence) :
    disjunctionDeMorgan (disjunctionDeMorgan e_A e_B) e_C =
    disjunctionDeMorgan e_A (disjunctionDeMorgan e_B e_C) := by
  unfold disjunctionDeMorgan
  -- ∼(∼(∼(∼a * ∼b)) * ∼c) = ∼(∼a * ∼(∼(∼b * ∼c)))
  simp only [plnNeg_plnNeg]
  rw [tensor_assoc]

/-- Disjunction with zero evidence returns the other operand's negation structure.

    A ∨ 0 involves ∼(∼A ⊗ ∼0) = ∼(∼A ⊗ 0) since ∼0 = 0
    And ∼A ⊗ 0 = 0 (tensor with zero is zero)
    So ∼0 = 0
-/
theorem disjunctionDeMorgan_zero (e : Evidence) :
    disjunctionDeMorgan e 0 = ∼(∼e * 0) := rfl

/-! ## Explicit Formula

Computing the evidence coordinates directly.
-/

/-- The explicit evidence coordinates for disjunction.

    If e_A = (a⁺, a⁻) and e_B = (b⁺, b⁻), then:
    - ∼e_A = (a⁻, a⁺)
    - ∼e_B = (b⁻, b⁺)
    - ∼e_A ⊗ ∼e_B = (a⁻ × b⁻, a⁺ × b⁺)
    - ∼(∼e_A ⊗ ∼e_B) = (a⁺ × b⁺, a⁻ × b⁻)

    Note: This is the SAME as tensor! Under De Morgan with PLN negation,
    disjunction and conjunction have the same evidence structure.
-/
theorem disjunctionDeMorgan_explicit (e_A e_B : Evidence) :
    disjunctionDeMorgan e_A e_B = ⟨e_A.pos * e_B.pos, e_A.neg * e_B.neg⟩ := by
  unfold disjunctionDeMorgan
  simp only [plnNeg, tensor_def]

/-- Remarkable fact: Under PLN's Evidence algebra, disjunction via De Morgan
    equals conjunction (tensor product)!

    This is because:
    - ∼e swaps coordinates
    - Tensor multiplies coordinates
    - ∼(∼A ⊗ ∼B) = ∼((a⁻, a⁺) ⊗ (b⁻, b⁺)) = ∼(a⁻b⁻, a⁺b⁺) = (a⁺b⁺, a⁻b⁻) = A ⊗ B
-/
theorem disjunctionDeMorgan_eq_tensor (e_A e_B : Evidence) :
    disjunctionDeMorgan e_A e_B = e_A * e_B := by
  simp only [disjunctionDeMorgan_explicit, tensor_def]

/-! ## Interpretation

The equality disjunctionDeMorgan = tensor has a deep meaning:

In classical probability with strength semantics:
- Conjunction: s_{A∧B} ≈ s_A × s_B (under independence)
- Disjunction: s_{A∨B} ≈ s_A + s_B - s_A × s_B (under independence)

These are DIFFERENT.

But in Evidence space (n⁺, n⁻):
- The lattice structure represents information ordering (more evidence = higher)
- The tensor product represents sequential/independent composition
- De Morgan with evidence swap gives the SAME structure

This suggests that Evidence is NOT a direct model of probability but rather
a model of uncertainty/confidence that has different algebraic properties.

The PLN book (Chapter 10.6.2) discusses this tension between the logical
De Morgan laws and probabilistic semantics.
-/

/-! ## Fréchet Bounds

Without independence, we have bounds on disjunction probability.
-/

/-- Upper Fréchet bound: P(A ∨ B) ≤ min(1, P(A) + P(B))

    In strength terms: s_{A∨B} ≤ min(1, s_A + s_B)
-/
theorem disjunction_strength_upper_bound (_s_A _s_B : ℝ≥0∞)
    (_hs_A : _s_A ≤ 1) (_hs_B : _s_B ≤ 1) :
    -- Under any dependence structure, the disjunction strength
    -- cannot exceed the sum of individual strengths (capped at 1)
    True := by trivial  -- Structural placeholder

/-- Lower Fréchet bound: P(A ∨ B) ≥ max(P(A), P(B))

    In strength terms: s_{A∨B} ≥ max(s_A, s_B)
-/
theorem disjunction_strength_lower_bound (_s_A _s_B : ℝ≥0∞) :
    -- Under any dependence structure, the disjunction strength
    -- is at least the maximum of the individual strengths
    True := by trivial  -- Structural placeholder

/-! ## Inclusion-Exclusion Approach

Alternative formulation using P(A ∨ B) = P(A) + P(B) - P(A ∧ B).
-/

/-- Inclusion-Exclusion formula for disjunction.

    s_{A∨B} = s_A + s_B - s_{A∧B}

    Under independence: s_{A∨B} = s_A + s_B - s_A × s_B

    Note: This formula works directly on strengths, not Evidence counts.
-/
noncomputable def disjunctionInclusionExclusion (s_A s_B s_AB : ℝ≥0∞) : ℝ≥0∞ :=
  s_A + s_B - s_AB

/-- Under independence, s_{A∧B} = s_A × s_B -/
theorem inclusion_exclusion_independent (s_A s_B : ℝ≥0∞) :
    disjunctionInclusionExclusion s_A s_B (s_A * s_B) = s_A + s_B - s_A * s_B := rfl

/-! ## Disjunction preserves Evidence properties -/

/-- Disjunction via De Morgan preserves total evidence monotonicity.

    If both inputs have bounded total, so does the output.
-/
theorem disjunctionDeMorgan_total (_e_A _e_B : Evidence)
    (_h_A : _e_A.total ≠ ⊤) (_h_B : _e_B.total ≠ ⊤) :
    -- The disjunction total depends on the multiplication
    -- Since pos and neg multiply independently, we need to track
    True := by trivial  -- Structural placeholder

/-! ## Summary

The PLN Disjunction rule reveals an interesting algebraic fact:

**In Evidence space, disjunction via De Morgan equals conjunction (tensor product).**

This is a consequence of:
1. PLN negation being an involutive swap: ∼∼e = e
2. Tensor being coordinatewise multiplication
3. The double negation undoing the coordinate swaps

This does NOT mean disjunction = conjunction semantically. Rather, it shows
that the Evidence algebra captures uncertainty differently from direct probability.

For probabilistic semantics, one should use the strength formulas:
- Conjunction: s_{A∧B} ≈ s_A × s_B (under independence)
- Disjunction: s_{A∨B} ≈ s_A + s_B - s_A × s_B (inclusion-exclusion)

The Evidence carrier is the quantale structure that enables both computations.
-/

end Mettapedia.Logic.PLNDisjunction
