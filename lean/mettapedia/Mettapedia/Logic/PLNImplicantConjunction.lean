import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNConjunction
import Mettapedia.ProbabilityTheory.Basic

/-!
# PLN Implicant Conjunction Introduction

This file formalizes the PLN **Implicant Conjunction Introduction** rule:

$$A → C, B → C ⊢ (A ∧ B) → C$$

Given that A implies C with some strength, and B implies C with some strength,
what is the strength of (A ∧ B) implying C?

## Key Formula (from Nil's nuPLN.tex)

Under independence assumptions:
1. A and B are globally independent: P(A,B) = P(A) × P(B)
2. A and B are conditionally independent given C: P(A,B|C) = P(A|C) × P(B|C)

The formula is:
$$P(C|A,B) = \frac{P(C|A) × P(C|B)}{P(C)}$$

## Derivation

By Bayes' formula:
$$P(C|A,B) = \frac{P(A,B|C) × P(C)}{P(A,B)}$$

Using both independence assumptions:
$$P(C|A,B) = \frac{P(A|C) × P(B|C) × P(C)}{P(A) × P(B)}$$

Using Bayes to substitute P(A|C) = P(C|A)P(A)/P(C) and similarly for B:
$$P(C|A,B) = \frac{P(C|A) × P(C|B)}{P(C)}$$

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009)
- Nil's nuPLN.tex, Section "Implicant Conjunction Introduction"
-/

namespace Mettapedia.Logic.PLNImplicantConjunction

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNConjunction
open Mettapedia.ProbabilityTheory
open MeasureTheory
open Evidence

/-! ## The Implicant Conjunction Formula

P(C|A,B) = P(C|A) × P(C|B) / P(C)

In PLN terms:
- s_{A→C} = P(C|A)
- s_{B→C} = P(C|B)
- s_C = P(C)
- s_{(A∧B)→C} = s_{A→C} × s_{B→C} / s_C
-/

/-- The implicant conjunction formula for strengths.

    Given:
    - s_AC: strength of A → C (i.e., P(C|A))
    - s_BC: strength of B → C (i.e., P(C|B))
    - s_C: marginal strength of C (i.e., P(C))

    Returns the strength of (A ∧ B) → C under independence assumptions.

    Formula: s_{(A∧B)→C} = s_{A→C} × s_{B→C} / s_C
-/
noncomputable def implicantConjunctionStrength (s_AC s_BC s_C : ℝ≥0∞) : ℝ≥0∞ :=
  s_AC * s_BC / s_C

/-! ## Properties of the Formula -/

/-- The formula is symmetric in A and B (order doesn't matter) -/
theorem implicantConjunction_comm (s_AC s_BC s_C : ℝ≥0∞) :
    implicantConjunctionStrength s_AC s_BC s_C =
    implicantConjunctionStrength s_BC s_AC s_C := by
  unfold implicantConjunctionStrength
  rw [mul_comm s_AC s_BC]

/-- When s_C = 1 (C is certain), the formula simplifies to the product -/
theorem implicantConjunction_certain_C (s_AC s_BC : ℝ≥0∞) :
    implicantConjunctionStrength s_AC s_BC 1 = s_AC * s_BC := by
  unfold implicantConjunctionStrength
  simp only [div_one]

/-- When A → C is certain (s_AC = 1), the result depends only on s_BC / s_C -/
theorem implicantConjunction_certain_AC (s_BC s_C : ℝ≥0∞) :
    implicantConjunctionStrength 1 s_BC s_C = s_BC / s_C := by
  unfold implicantConjunctionStrength
  simp only [one_mul]

/-- When both implications are certain, result is 1/s_C -/
theorem implicantConjunction_both_certain (s_C : ℝ≥0∞) :
    implicantConjunctionStrength 1 1 s_C = 1 / s_C := by
  unfold implicantConjunctionStrength
  simp only [one_mul]

/-! ## Bounds on the Result

The formula can exceed 1 when the premises are strong and C is rare.
PLN typically caps the result at 1.
-/

/-- The raw formula can exceed 1. For valid probability semantics,
    the result should be capped: min(1, s_AC × s_BC / s_C) -/
noncomputable def implicantConjunctionStrengthCapped (s_AC s_BC s_C : ℝ≥0∞) : ℝ≥0∞ :=
  min 1 (implicantConjunctionStrength s_AC s_BC s_C)

/-- The capped version is at most 1 -/
theorem implicantConjunctionStrengthCapped_le_one (s_AC s_BC s_C : ℝ≥0∞) :
    implicantConjunctionStrengthCapped s_AC s_BC s_C ≤ 1 :=
  min_le_left 1 _

/-- The capped version is at most the uncapped version -/
theorem implicantConjunctionStrengthCapped_le (s_AC s_BC s_C : ℝ≥0∞) :
    implicantConjunctionStrengthCapped s_AC s_BC s_C ≤
    implicantConjunctionStrength s_AC s_BC s_C :=
  min_le_right 1 _

/-! ## Evidence-Based Formulation

Converting the strength formula to work on Evidence.
-/

/-- Implicant conjunction on Evidence.

    Given Evidence for A→C and B→C, plus the marginal strength of C,
    compute Evidence for (A∧B)→C.

    This combines:
    1. The strength formula: s = s_AC × s_BC / s_C
    2. Total evidence from inputs (heuristic: minimum of the two totals)
-/
noncomputable def implicantConjunctionEvidence
    (e_AC e_BC : Evidence) (s_C : ℝ≥0∞)
    (_h_AC : e_AC.total ≠ 0) (_h_BC : e_BC.total ≠ 0)
    (_h_sC : s_C ≠ 0) (_h_sC_top : s_C ≠ ⊤) : Evidence :=
  let s_AC := toStrength e_AC
  let s_BC := toStrength e_BC
  let s_result := min 1 (s_AC * s_BC / s_C)  -- Capped to [0,1]
  -- Heuristic: total evidence is minimum of inputs (conservative)
  let total_ev := min e_AC.total e_BC.total
  -- Construct evidence with computed strength and total
  ⟨s_result * total_ev, (1 - s_result) * total_ev⟩

/-! ## Confidence Propagation

How confidence propagates through implicant conjunction.
The result confidence depends on both input confidences.
-/

/-- Confidence heuristic: take minimum of input confidences.

    The reasoning is that the result is only as reliable as the
    weakest premise.
-/
noncomputable def implicantConjunctionConfidence (c_AC c_BC : ℝ≥0∞) : ℝ≥0∞ :=
  min c_AC c_BC

/-- Alternative: harmonic combination of confidences
    This is a reasonable heuristic for combining confidence values. -/
noncomputable def implicantConjunctionConfidenceHarmonic (c_AC c_BC : ℝ≥0∞) : ℝ≥0∞ :=
  2 * c_AC * c_BC / (c_AC + c_BC)

/-! ## Independence Conditions

The formula requires independence assumptions. We formalize these.
-/

/-- A predicate expressing that two events are independent with respect
    to a probability distribution represented by strength. -/
structure IndependenceCondition (s_A s_B s_AB : ℝ≥0∞) : Prop where
  /-- Global independence: P(A ∧ B) = P(A) × P(B) -/
  global : s_AB = s_A * s_B

/-- The conditional independence condition for the formula to hold.

    A and B are conditionally independent given C:
    P(A,B|C) = P(A|C) × P(B|C)
-/
structure ConditionalIndependenceCondition
    (s_AC s_BC s_ABC s_C : ℝ≥0∞) : Prop where
  /-- Conditional independence given C -/
  cond : s_ABC * s_C = s_AC * s_BC * s_C

/-! ## Validity Theorem

Under the independence assumptions, the formula is correct.
-/

/-- The main validity theorem for implicant conjunction.

    Under independence assumptions, the formula gives the correct
    conditional probability P(C|A,B).

    This is essentially a reformulation of the derivation in the docstring.
-/
theorem implicantConjunction_valid
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [IsFiniteMeasure μ]
    (A B C : Set Ω)
    (hA : μ A ≠ 0) (hB : μ B ≠ 0) (hC : μ C ≠ 0)
    (hAB : μ (A ∩ B) ≠ 0)
    (hIndep : μ.real (A ∩ B) = μ.real A * μ.real B)
    (hCondIndep : condProb μ (A ∩ B) C = condProb μ A C * condProb μ B C) :
    condProb μ C (A ∩ B) = (condProb μ C A) * (condProb μ C B) / μ.real C := by
  have hAreal : μ.real A ≠ 0 := measureReal_ne_zero_of_measure_ne_zero (μ := μ) hA
  have hBreal : μ.real B ≠ 0 := measureReal_ne_zero_of_measure_ne_zero (μ := μ) hB
  have hCreal : μ.real C ≠ 0 := measureReal_ne_zero_of_measure_ne_zero (μ := μ) hC
  have hABreal : μ.real (A ∩ B) ≠ 0 :=
    measureReal_ne_zero_of_measure_ne_zero (μ := μ) hAB

  -- Bayes: P(C | A∩B) = P(A∩B | C) * P(C) / P(A∩B)
  have h_bayes_C_AB :
      condProb μ C (A ∩ B) = condProb μ (A ∩ B) C * μ.real C / μ.real (A ∩ B) := by
    simpa using (bayes (μ := μ) (A := C) (B := (A ∩ B)) hC hAB)

  -- Bayes: P(A | C) and P(B | C) expressed via P(C | A), P(C | B)
  have h_bayes_A_C : condProb μ A C = condProb μ C A * μ.real A / μ.real C := by
    simpa using (bayes (μ := μ) (A := A) (B := C) hA hC)
  have h_bayes_B_C : condProb μ B C = condProb μ C B * μ.real B / μ.real C := by
    simpa using (bayes (μ := μ) (A := B) (B := C) hB hC)

  -- Combine everything; the only real content is cancelling `P(A)P(B)` using independence.
  -- The rest is algebra in `ℝ`.
  have h_nonzero_prod : (μ.real A * μ.real B : ℝ) ≠ 0 := by
    exact mul_ne_zero hAreal hBreal

  -- Rewrite and simplify.
  calc
    condProb μ C (A ∩ B)
        = (condProb μ (A ∩ B) C) * μ.real C / μ.real (A ∩ B) := h_bayes_C_AB
    _ = (condProb μ A C * condProb μ B C) * μ.real C / μ.real (A ∩ B) := by
          simp [hCondIndep, mul_assoc]
    _ = ((condProb μ C A) * μ.real A / μ.real C) * ((condProb μ C B) * μ.real B / μ.real C) *
          μ.real C / μ.real (A ∩ B) := by
          simp [h_bayes_A_C, h_bayes_B_C]
    _ = (condProb μ C A) * (condProb μ C B) / μ.real C := by
          -- `field_simp` handles the division; use independence to replace `P(A∩B)` with `P(A)P(B)`.
          have hIndep' : (μ.real (A ∩ B) : ℝ) = μ.real A * μ.real B := hIndep
          -- Replace `P(A∩B)` so it cancels.
          -- Then cancel the remaining `P(C)` factor.
          field_simp [hAreal, hBreal, hCreal, hABreal, hIndep', h_nonzero_prod]
          -- After clearing denominators, the remaining goal is a commutativity/associativity shuffle
          -- together with `hIndep'`.
          simp [hIndep', mul_assoc, mul_left_comm, mul_comm]

/-! ## Connection to PLN Deduction

Implicant Conjunction relates to the Deduction rule.
While Deduction chains: A→B, B→C ⊢ A→C
Implicant Conjunction combines: A→C, B→C ⊢ (A∧B)→C

Both are fundamental PLN inference patterns.
-/

/-- The implicant conjunction can be seen as a "merge" of two evidence
    paths to the same conclusion. -/
theorem implicant_conjunction_is_merge
    (e_AC e_BC : Evidence) (s_C : ℝ≥0∞)
    (hAC : e_AC.total ≠ 0) (hBC : e_BC.total ≠ 0)
    (hsC : s_C ≠ 0) (hsC_top : s_C ≠ ⊤) :
    implicantConjunctionEvidence e_AC e_BC s_C hAC hBC hsC hsC_top =
      implicantConjunctionEvidence e_BC e_AC s_C hBC hAC hsC hsC_top := by
  simp [implicantConjunctionEvidence, mul_comm, min_comm]

/-! ## Summary

The Implicant Conjunction rule answers: "If A implies C and B implies C,
how strongly does (A ∧ B) imply C?"

Key points:
1. **Formula**: s_{(A∧B)→C} = s_{A→C} × s_{B→C} / s_C
2. **Requires independence**: A and B must be globally and conditionally independent
3. **Caps at 1**: The raw formula can exceed 1 for rare conclusions
4. **Evidence combination**: Uses strength formula with heuristic for total evidence

This rule is essential for PLN reasoning about conjunctions of causes/premises.
-/

end Mettapedia.Logic.PLNImplicantConjunction
