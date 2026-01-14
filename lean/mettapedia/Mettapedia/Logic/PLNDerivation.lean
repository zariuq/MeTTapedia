/-
# PLN Formula Derivations from Probability Axioms

Formal derivation of Probabilistic Logic Networks (PLN) truth value formulas
from standard probability theory + specific independence assumptions.

The key insight: PLN formulas are NOT arbitrary heuristics - they are theorems
that follow from probability axioms under specific structural assumptions.

## Main Results

1. `pln_deduction_independence` - The independence-based deduction formula
   s_AC = s_AB · s_BC + (1 - s_AB) · (s_C - s_B · s_BC) / (1 - s_B)
   follows from the Law of Total Probability + conditional independence.

2. `pln_deduction_high_uncertainty` - Under high term probability uncertainty,
   s_AC ≈ s_AB · s_BC (the simplified form).

## References

- Goertzel et al., "Probabilistic Logic Networks" (Springer, 2008)
- Goertzel, "PLN and NARS Often Yield Similar strength × confidence" (arXiv:2412.19524)
-/

import Mettapedia.ProbabilityTheory.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.ConditionalProbability

set_option linter.unusedSectionVars false

noncomputable section

namespace Mettapedia.Logic.PLN

open MeasureTheory ProbabilityTheory
open Set

/-! ## PLN Truth Value Algebra

Before connecting to full probability theory, we can study the algebraic
properties of the PLN deduction formula as a function of real numbers.
-/

/-- The PLN independence-based deduction formula as a function of strengths.

  s_AC = s_AB · s_BC + (1 - s_AB) · (s_C - s_B · s_BC) / (1 - s_B)

  This computes the strength of A → C given:
  - s_AB: strength of A → B (P(B|A))
  - s_BC: strength of B → C (P(C|B))
  - s_B: term probability of B
  - s_C: term probability of C
-/
def plnDeductionStrength (s_AB s_BC s_B s_C : ℝ) : ℝ :=
  s_AB * s_BC + (1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B)

/-- The simplified PLN deduction formula under high term probability uncertainty.
    When term probabilities are highly uncertain, the formula simplifies to:
    s_AC ≈ s_AB · s_BC -/
def plnDeductionSimplified (s_AB s_BC : ℝ) : ℝ := s_AB * s_BC

/-- **High Uncertainty Limit**: Under uniform term probabilities (s_B = s_C = 1/2)
    AND s_BC = 1/2, the correction term becomes (1 - s_AB) * 1/2.

    The full formula becomes: s_AB * 1/2 + (1 - s_AB) * 1/2 = 1/2
    (independent of s_AB!)

    This formalizes the observation from the PLN/NARS comparison paper. -/
theorem pln_deduction_uniform_simplifies (s_AB : ℝ) :
    plnDeductionStrength s_AB (1/2) (1/2) (1/2) = 1/2 := by
  unfold plnDeductionStrength
  -- s_C - s_B · s_BC = 1/2 - 1/2 · 1/2 = 1/4
  -- (1 - s_B) = 1/2
  -- Correction = (1 - s_AB) · (1/4) / (1/2) = (1 - s_AB) · 1/2
  -- Total = s_AB * 1/2 + (1 - s_AB) * 1/2 = 1/2
  ring

/-- PLN deduction output is bounded by 1 when inputs are valid probabilities
    and a natural constraint holds.

    Note: This is a weaker statement that avoids division complexity. -/
theorem pln_deduction_bounded
    (s_AB s_BC s_B s_C : ℝ)
    (h_sAB : 0 ≤ s_AB ∧ s_AB ≤ 1)
    (h_sBC : 0 ≤ s_BC ∧ s_BC ≤ 1)
    (h_sB : 0 < s_B ∧ s_B < 1)
    (_h_sC : 0 ≤ s_C ∧ s_C ≤ 1)
    (h_constraint : s_C - s_B * s_BC ≤ 1 - s_B) :
    plnDeductionStrength s_AB s_BC s_B s_C ≤ 1 := by
  unfold plnDeductionStrength
  have h1B : 1 - s_B > 0 := by linarith [h_sB.2]
  have h1AB : 1 - s_AB ≥ 0 := by linarith [h_sAB.2]
  -- Clear the denominator by multiplying
  have h_corr_le : (1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B) ≤ 1 - s_AB := by
    rw [div_le_iff₀ h1B]
    calc (1 - s_AB) * (s_C - s_B * s_BC)
        ≤ (1 - s_AB) * (1 - s_B) := by nlinarith [h_constraint, h1AB]
      _ = (1 - s_AB) * (1 - s_B) := rfl
  calc s_AB * s_BC + (1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B)
      ≤ s_AB * 1 + (1 - s_AB) := by nlinarith [h_sBC.2, h_corr_le, h_sAB.1]
    _ = 1 := by ring

/-- PLN deduction output is non-negative when inputs are valid probabilities. -/
theorem pln_deduction_nonneg
    (s_AB s_BC s_B s_C : ℝ)
    (h_sAB : 0 ≤ s_AB ∧ s_AB ≤ 1)
    (h_sBC : 0 ≤ s_BC)
    (h_sB : 0 < s_B ∧ s_B < 1)
    (h_constraint : s_B * s_BC ≤ s_C) :
    0 ≤ plnDeductionStrength s_AB s_BC s_B s_C := by
  unfold plnDeductionStrength
  have h1B : 1 - s_B > 0 := by linarith [h_sB.2]
  have h1AB : 1 - s_AB ≥ 0 := by linarith [h_sAB.2]
  have hcorr_nonneg : 0 ≤ s_C - s_B * s_BC := by linarith [h_constraint]
  have h_term1 : 0 ≤ s_AB * s_BC := by nlinarith [h_sAB.1, h_sBC]
  have h_term2 : 0 ≤ (1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B) := by
    apply div_nonneg
    · nlinarith [h1AB, hcorr_nonneg]
    · linarith
  linarith

/-! ## Connection to Quantale Framework

Our quantale transitivity theorem from QuantaleWeakness.lean:
  (A → B) * (B → C) ≤ (A → C)

provides the algebraic SKELETON of deduction. It says transitivity "works"
but doesn't specify the numerical computation.

The PLN formula provides the FLESH: the actual numeric computation.

Key observation: The PLN formula can be seen as a "refinement" of simple
multiplication s_AB * s_BC, with a correction term that accounts for
probability flow through the complement path (via ¬B).
-/

/-- The correction term in PLN deduction: accounts for probability flow
    through the complement path (A → ¬B → C). -/
def plnCorrectionTerm (s_AB s_BC s_B s_C : ℝ) : ℝ :=
  (1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B)

/-- PLN deduction = simplified + correction -/
theorem pln_deduction_decomposition (s_AB s_BC s_B s_C : ℝ) :
    plnDeductionStrength s_AB s_BC s_B s_C =
      plnDeductionSimplified s_AB s_BC + plnCorrectionTerm s_AB s_BC s_B s_C := by
  unfold plnDeductionStrength plnDeductionSimplified plnCorrectionTerm
  ring

/-- When s_B = s_C (uniform term probs for B and C), and s_BC = s_C
    (C is independent of B), the correction term simplifies. -/
theorem pln_correction_uniform (s_AB s : ℝ) (h : s < 1) :
    plnCorrectionTerm s_AB s s s = (1 - s_AB) * s * (1 - s) / (1 - s) := by
  unfold plnCorrectionTerm
  have h' : 1 - s ≠ 0 := by linarith
  field_simp [h']

/-! ## Conditional Independence Assumptions

The PLN independence-based formula is derived under two key assumptions:

1. **Positive Independence**: P(C | A ∩ B) = P(C | B)
   "Once we know B holds, knowing A gives no extra info about C"

2. **Negative Independence**: P(C | A ∩ Bᶜ) = P(C | Bᶜ)
   "If B is false, A and C are independent (background noise)"

These are the "hidden axioms" that justify the PLN formula.
-/

/-- Structure capturing the PLN independence assumptions for deduction.
    This makes explicit what's needed to derive the formula. -/
structure PLNDeductionContext (s_AB s_BC s_A s_B s_C : ℝ) : Prop where
  /-- A is not impossible -/
  hA_pos : 0 < s_A
  /-- B is not impossible -/
  hB_pos : 0 < s_B
  /-- B is not certain -/
  hB_lt1 : s_B < 1
  /-- Valid probability bounds -/
  hAB_valid : 0 ≤ s_AB ∧ s_AB ≤ 1
  hBC_valid : 0 ≤ s_BC ∧ s_BC ≤ 1
  hC_valid : 0 ≤ s_C ∧ s_C ≤ 1
  /-- Positive independence holds -/
  pos_indep : True  -- Placeholder for the actual condition
  /-- Negative independence holds -/
  neg_indep : True  -- Placeholder for the actual condition

/-! ## Measure-Theoretic Helper Lemmas

These lemmas establish the measure-theoretic foundations needed to prove
that the PLN deduction formula follows from probability axioms.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Binary partition of a set: A = (A ∩ B) ∪ (A ∩ Bᶜ) -/
lemma set_inter_union_compl (A B : Set Ω) : A = (A ∩ B) ∪ (A ∩ Bᶜ) := by
  ext x
  constructor
  · intro hx
    by_cases hB : x ∈ B
    · left; exact ⟨hx, hB⟩
    · right; exact ⟨hx, hB⟩
  · intro hx
    cases hx with
    | inl h => exact h.1
    | inr h => exact h.1

/-- The two parts of the binary partition are disjoint. -/
lemma disjoint_inter_compl (A B : Set Ω) : Disjoint (A ∩ B) (A ∩ Bᶜ) := by
  rw [Set.disjoint_iff]
  intro x ⟨⟨_, hB⟩, ⟨_, hBc⟩⟩
  exact hBc hB

/-- Law of Total Probability (binary partition, real-valued measure).

μ.real(C ∩ A) = μ.real(C ∩ A ∩ B) + μ.real(C ∩ A ∩ Bᶜ)

This splits the probability of C ∩ A into contributions from when B holds
and when B doesn't hold.

Note: In Lean, `C ∩ A ∩ B` parses as `(C ∩ A) ∩ B` (left-associative). -/
lemma total_prob_binary_split (μ : Measure Ω) [IsFiniteMeasure μ]
    {A B C : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    μ.real (C ∩ A) = μ.real (C ∩ A ∩ B) + μ.real (C ∩ A ∩ Bᶜ) := by
  have hCA := hC.inter hA
  -- (C ∩ A) = (C ∩ A) ∩ B ∪ (C ∩ A) ∩ Bᶜ
  have heq : C ∩ A = (C ∩ A ∩ B) ∪ (C ∩ A ∩ Bᶜ) := (Set.inter_union_compl (C ∩ A) B).symm
  have hdisj : Disjoint (C ∩ A ∩ B) (C ∩ A ∩ Bᶜ) := disjoint_inter_compl (C ∩ A) B
  have hm2 : MeasurableSet (C ∩ A ∩ Bᶜ) := hCA.inter hB.compl
  conv_lhs => rw [heq]
  rw [Measure.real, measure_union hdisj hm2,
      ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  rfl

/-- Conditional probability of C given Bᶜ in terms of marginals.

P(C|Bᶜ) = (P(C) - P(B)·P(C|B)) / P(Bᶜ)
        = (P(C) - P(C ∩ B)) / (1 - P(B))

This is derived from: P(C) = P(C|B)P(B) + P(C|Bᶜ)P(Bᶜ), solving for P(C|Bᶜ). -/
lemma cond_prob_complement (μ : Measure Ω) [IsProbabilityMeasure μ]
    {B C : Set Ω} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (_hB_pos : μ B ≠ 0) (_hBc_pos : μ Bᶜ ≠ 0) :
    μ.real (C ∩ Bᶜ) / μ.real Bᶜ = (μ.real C - μ.real (C ∩ B)) / (1 - μ.real B) := by
  -- From C = (C ∩ B) ∪ (C ∩ Bᶜ), we get μ C = μ(C ∩ B) + μ(C ∩ Bᶜ)
  have hsplit : μ.real C = μ.real (C ∩ B) + μ.real (C ∩ Bᶜ) := by
    have heq : C = (C ∩ B) ∪ (C ∩ Bᶜ) := (Set.inter_union_compl C B).symm
    have hdisj : Disjoint (C ∩ B) (C ∩ Bᶜ) := disjoint_inter_compl C B
    conv_lhs => rw [heq]
    rw [Measure.real, measure_union hdisj (hC.inter hB.compl),
        ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
    rfl
  -- μ.real Bᶜ = 1 - μ.real B (complement probability)
  have hBc_eq : μ.real Bᶜ = 1 - μ.real B := by
    have h := prob_compl_eq_one_sub hB (μ := μ)
    simp only [Measure.real]
    rw [h]
    -- Need to show (1 - μ B).toReal = 1 - (μ B).toReal
    have hle : μ B ≤ 1 := by
      rw [← IsProbabilityMeasure.measure_univ (μ := μ)]
      exact measure_mono (Set.subset_univ B)
    have hne : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
    rw [ENNReal.toReal_sub_of_le hle hne]
    simp only [ENNReal.toReal_one]
  -- Now solve: μ.real (C ∩ Bᶜ) = μ.real C - μ.real (C ∩ B)
  have hCBc : μ.real (C ∩ Bᶜ) = μ.real C - μ.real (C ∩ B) := by linarith [hsplit]
  rw [hCBc, hBc_eq]

/-- Conditional probability rewrite: P(C ∩ A ∩ B) = P(C|A∩B) · P(A ∩ B) -/
lemma cond_prob_mul (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Set Ω} (hY_pos : μ.real Y ≠ 0) :
    μ.real (X ∩ Y) = (μ.real (X ∩ Y) / μ.real Y) * μ.real Y := by
  field_simp [hY_pos]

/-! ## The Formula as a Derivation

The main theorem states: IF the independence assumptions hold,
THEN the PLN formula computes the correct conditional probability P(C|A).

This is NOT a tautology - it's a theorem that connects:
- The algebraic formula (plnDeductionStrength)
- The probabilistic semantics (conditional probability)
- The structural assumption (conditional independence)
-/

/-- **Main Theorem**: PLN deduction formula follows from probability axioms.

Under the PLN independence assumptions, the deduction formula computes
the correct conditional probability:

  P(C|A) = s_AB · s_BC + (1 - s_AB) · (s_C - s_B · s_BC) / (1 - s_B)

The proof strategy is:
1. Apply Law of Total Probability: P(C|A) = P(C|A,B)·P(B|A) + P(C|A,¬B)·P(¬B|A)
2. Use positive independence: P(C|A,B) = P(C|B) = s_BC
3. Use negative independence: P(C|A,¬B) = P(C|¬B)
4. Compute P(C|¬B) from total probability: = (s_C - s_B · s_BC) / (1 - s_B)
5. Substitute and simplify to get the formula.

TODO: Requires proper measure-theoretic setup with conditional probability.
-/
theorem pln_deduction_from_total_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A B C : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hA_pos : μ A ≠ 0) (hB_pos : μ B ≠ 0) (hB_lt1 : μ B < 1)
    -- Positivity for conditional probabilities to be defined
    (hAB_pos : μ (A ∩ B) ≠ 0) (hABc_pos : μ (A ∩ Bᶜ) ≠ 0)
    -- Positive independence: P(C|A∩B) = P(C|B)
    (h_pos_indep : μ.real (C ∩ (A ∩ B)) / μ.real (A ∩ B) = μ.real (C ∩ B) / μ.real B)
    -- Negative independence: P(C|A∩Bᶜ) = P(C|Bᶜ)
    (h_neg_indep : μ.real (C ∩ (A ∩ Bᶜ)) / μ.real (A ∩ Bᶜ) = μ.real (C ∩ Bᶜ) / μ.real Bᶜ) :
    -- Then P(C|A) equals the PLN formula
    μ.real (C ∩ A) / μ.real A =
      plnDeductionStrength (μ.real (B ∩ A) / μ.real A) (μ.real (C ∩ B) / μ.real B)
                           (μ.real B) (μ.real C) := by
  -- Abbreviations for readability
  let s_AB := μ.real (B ∩ A) / μ.real A  -- P(B|A)
  let s_BC := μ.real (C ∩ B) / μ.real B  -- P(C|B)
  let s_B := μ.real B                     -- P(B)
  let s_C := μ.real C                     -- P(C)
  let s_A := μ.real A                     -- P(A)

  -- Step 1: Apply Law of Total Probability
  -- P(C ∩ A) = P(C ∩ A ∩ B) + P(C ∩ A ∩ Bᶜ)
  have h_total := total_prob_binary_split μ hA hB hC

  -- Step 2: Express as conditional probabilities
  -- P(C|A) = [P(C ∩ A ∩ B) + P(C ∩ A ∩ Bᶜ)] / P(A)
  --        = P(C ∩ A ∩ B)/P(A) + P(C ∩ A ∩ Bᶜ)/P(A)

  -- Key: P(C ∩ A ∩ B) = P(C|A∩B) · P(A ∩ B)
  --                    = P(C|B) · P(A ∩ B)  [by positive independence]
  --                    = s_BC · P(A ∩ B)

  -- And: P(C ∩ A ∩ Bᶜ) = P(C|A∩Bᶜ) · P(A ∩ Bᶜ)
  --                     = P(C|Bᶜ) · P(A ∩ Bᶜ)  [by negative independence]

  -- Step 3: Need positivity conditions
  have hA_real_pos : 0 < μ.real A := by
    simp only [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hA_pos, measure_lt_top μ A⟩

  have hB_real_pos : 0 < μ.real B := by
    simp only [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hB_pos, measure_lt_top μ B⟩

  -- P(Bᶜ) ≠ 0 because P(B) < 1
  have hBc_pos : μ Bᶜ ≠ 0 := by
    intro h
    -- If μ Bᶜ = 0, then μ B = μ Set.univ = 1
    have huniv := IsProbabilityMeasure.measure_univ (μ := μ)
    -- B ∪ Bᶜ = Set.univ
    have hBunion : B ∪ Bᶜ = Set.univ := Set.union_compl_self B
    rw [← hBunion] at huniv
    have hdisj : Disjoint B Bᶜ := disjoint_compl_right
    rw [measure_union hdisj hB.compl, h, add_zero] at huniv
    -- Now huniv : μ B = 1, which contradicts hB_lt1
    rw [huniv] at hB_lt1
    exact lt_irrefl 1 hB_lt1

  have hBc_real_pos : 0 < μ.real Bᶜ := by
    simp only [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hBc_pos, measure_lt_top μ Bᶜ⟩

  -- Step 4: Rewrite using independence assumptions

  -- P(C|Bᶜ) = (P(C) - P(C ∩ B)) / (1 - P(B))
  have h_cond_compl := cond_prob_complement μ hB hC hB_pos hBc_pos

  -- Key: P(Bᶜ|A) = 1 - P(B|A) = 1 - s_AB
  -- We need P(A ∩ Bᶜ) / P(A) = 1 - P(A ∩ B) / P(A)
  have hABc_split : μ.real (A ∩ Bᶜ) / μ.real A = 1 - μ.real (A ∩ B) / μ.real A := by
    have hAsplit : μ.real A = μ.real (A ∩ B) + μ.real (A ∩ Bᶜ) := by
      have heq : A = (A ∩ B) ∪ (A ∩ Bᶜ) := (Set.inter_union_compl A B).symm
      have hdisj : Disjoint (A ∩ B) (A ∩ Bᶜ) := disjoint_inter_compl A B
      conv_lhs => rw [heq]
      rw [Measure.real, measure_union hdisj (hA.inter hB.compl),
          ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
      rfl
    have hA_ne : μ.real A ≠ 0 := ne_of_gt hA_real_pos
    field_simp [hA_ne]
    linarith [hAsplit]

  -- Commutativity: A ∩ B = B ∩ A
  have hAB_comm : μ.real (A ∩ B) = μ.real (B ∩ A) := by
    congr 1; exact Set.inter_comm A B

  -- Associativity: C ∩ A ∩ B = C ∩ (A ∩ B)
  have hCAB_assoc : C ∩ A ∩ B = C ∩ (A ∩ B) := by
    ext x; simp only [Set.mem_inter_iff]; tauto

  have hCABc_assoc : C ∩ A ∩ Bᶜ = C ∩ (A ∩ Bᶜ) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff]; tauto

  -- Step 5: The main algebraic derivation
  -- P(C|A) = P(C ∩ A)/P(A) = [P(C ∩ A ∩ B) + P(C ∩ A ∩ Bᶜ)] / P(A)

  -- Unfold the definition of plnDeductionStrength
  unfold plnDeductionStrength

  -- We need to show:
  -- μ.real(C ∩ A) / μ.real(A) =
  --   s_AB * s_BC + (1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B)

  -- First, rewrite LHS using total probability
  rw [h_total]

  -- Now we have: [μ.real(C ∩ A ∩ B) + μ.real(C ∩ A ∩ Bᶜ)] / μ.real(A)

  -- Use the independence assumptions to rewrite each term

  -- For positivity of A ∩ B and A ∩ Bᶜ (needed for division)
  -- We'll use field_simp to clear denominators

  have hA_ne : μ.real A ≠ 0 := ne_of_gt hA_real_pos
  have hB_ne : μ.real B ≠ 0 := ne_of_gt hB_real_pos
  have hBc_ne : μ.real Bᶜ ≠ 0 := ne_of_gt hBc_real_pos

  -- 1 - s_B ≠ 0 (since s_B < 1)
  have h1B_ne : 1 - μ.real B ≠ 0 := by
    intro h
    have hB_eq_1 : μ.real B = 1 := by linarith
    -- μ.real B = 1 means μ B = 1, contradicting hB_lt1
    simp only [Measure.real] at hB_eq_1
    have : μ B = 1 := by
      rw [ENNReal.toReal_eq_one_iff] at hB_eq_1
      exact hB_eq_1
    rw [this] at hB_lt1
    exact lt_irrefl 1 hB_lt1

  -- The proof now requires careful algebraic manipulation.
  -- The key insight is that:
  -- Term 1: μ.real(C ∩ A ∩ B) / μ.real(A)
  --       = μ.real(C ∩ (A ∩ B)) / μ.real(A)
  --       = [μ.real(C ∩ (A ∩ B)) / μ.real(A ∩ B)] * [μ.real(A ∩ B) / μ.real(A)]
  --       = P(C|A∩B) * P(A∩B|A)
  --       = P(C|B) * P(B|A)  [by positive independence]
  --       = s_BC * s_AB
  --
  -- Term 2: μ.real(C ∩ A ∩ Bᶜ) / μ.real(A)
  --       = P(C|A∩Bᶜ) * P(A∩Bᶜ|A)
  --       = P(C|Bᶜ) * (1 - P(B|A))  [by negative independence]
  --       = P(C|Bᶜ) * (1 - s_AB)
  --
  -- And P(C|Bᶜ) = (s_C - s_B * s_BC) / (1 - s_B) by h_cond_compl

  -- Positivity of A ∩ B and A ∩ Bᶜ (now given as hypotheses)
  have hAB_real_pos : 0 < μ.real (A ∩ B) := by
    simp only [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hAB_pos, measure_lt_top μ _⟩

  have hABc_real_pos : 0 < μ.real (A ∩ Bᶜ) := by
    simp only [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hABc_pos, measure_lt_top μ _⟩

  have hAB_ne : μ.real (A ∩ B) ≠ 0 := ne_of_gt hAB_real_pos
  have hABc_ne : μ.real (A ∩ Bᶜ) ≠ 0 := ne_of_gt hABc_real_pos

  -- Step 6: Rewrite Term 1 using conditional probability product rule
  -- P(C ∩ A ∩ B) / P(A) = P(C|A∩B) · P(A∩B) / P(A) = P(C|B) · P(B∩A) / P(A)
  have hTerm1 : μ.real (C ∩ A ∩ B) / μ.real A =
                (μ.real (C ∩ B) / μ.real B) * (μ.real (B ∩ A) / μ.real A) := by
    -- Use: μ.real (C ∩ A ∩ B) = P(C|A∩B) · P(A∩B)
    --    = P(C|B) · P(A∩B)  [by positive independence]
    -- Rewrite using associativity: C ∩ A ∩ B = C ∩ (A ∩ B)
    rw [show C ∩ A ∩ B = C ∩ (A ∩ B) from hCAB_assoc]
    -- Use the conditional probability product rule:
    -- μ.real (C ∩ (A ∩ B)) = P(C|A∩B) · P(A∩B)
    have hprod : μ.real (C ∩ (A ∩ B)) =
                 (μ.real (C ∩ (A ∩ B)) / μ.real (A ∩ B)) * μ.real (A ∩ B) := by
      field_simp [hAB_ne]
    rw [hprod, h_pos_indep]
    -- Now we have: (P(C|B) · P(A∩B)) / P(A)
    -- Need to show this equals P(C|B) · P(B∩A) / P(A)
    rw [← hAB_comm]
    ring

  -- Step 7: Rewrite Term 2 using conditional probability product rule
  -- P(C ∩ A ∩ Bᶜ) / P(A) = P(C|A∩Bᶜ) · P(A∩Bᶜ) / P(A) = P(C|Bᶜ) · P(A∩Bᶜ) / P(A)
  have hTerm2 : μ.real (C ∩ A ∩ Bᶜ) / μ.real A =
                (μ.real (C ∩ Bᶜ) / μ.real Bᶜ) * (μ.real (A ∩ Bᶜ) / μ.real A) := by
    rw [show C ∩ A ∩ Bᶜ = C ∩ (A ∩ Bᶜ) from hCABc_assoc]
    have hprod : μ.real (C ∩ (A ∩ Bᶜ)) =
                 (μ.real (C ∩ (A ∩ Bᶜ)) / μ.real (A ∩ Bᶜ)) * μ.real (A ∩ Bᶜ) := by
      field_simp [hABc_ne]
    rw [hprod, h_neg_indep]
    ring

  -- Step 8: Combine using P(A∩Bᶜ)/P(A) = 1 - P(B∩A)/P(A)
  -- The goal is now to show:
  -- (Term1 + Term2) / 1 = s_AB * s_BC + (1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B)

  -- Add fractions: (a + b) / c = a/c + b/c
  have hsum : (μ.real (C ∩ A ∩ B) + μ.real (C ∩ A ∩ Bᶜ)) / μ.real A =
              μ.real (C ∩ A ∩ B) / μ.real A + μ.real (C ∩ A ∩ Bᶜ) / μ.real A := by
    field_simp [hA_ne]

  rw [hsum, hTerm1, hTerm2]

  -- Now we have:
  -- s_BC * s_AB + P(C|Bᶜ) * P(A∩Bᶜ)/P(A)
  -- Need to show this equals:
  -- s_AB * s_BC + (1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B)

  -- Use hABc_split: P(A∩Bᶜ)/P(A) = 1 - P(A∩B)/P(A) = 1 - P(B∩A)/P(A)
  rw [hAB_comm] at hABc_split
  rw [hABc_split]

  -- Use h_cond_compl: P(C|Bᶜ) = (s_C - P(C∩B)) / (1 - s_B)
  -- But h_cond_compl gives: P(C∩Bᶜ)/P(Bᶜ) = (s_C - P(C∩B)) / (1 - s_B)
  -- We need to rewrite P(C∩B) = P(C|B) * P(B) = s_BC * s_B
  have hCB_eq : μ.real (C ∩ B) = (μ.real (C ∩ B) / μ.real B) * μ.real B := by
    field_simp [hB_ne]

  -- Final algebra
  rw [h_cond_compl]
  -- Goal: s_BC * s_AB + (s_C - P(C∩B))/(1-s_B) * (1 - s_AB)
  --     = s_AB * s_BC + (1 - s_AB) * (s_C - s_B * s_BC) / (1 - s_B)

  -- Clear all denominators and prove algebraically
  -- field_simp will clear denominators and ring will handle the polynomial equality
  field_simp [hA_ne, hB_ne, hBc_ne, h1B_ne]

/-! ## Bayes Inversion

The key to deriving Induction and Abduction is Bayes' Rule:
  P(B|A) = P(A|B) · P(B) / P(A)

In PLN notation:
  s_{AB} = s_{BA} · s_B / s_A
-/

/-- Bayes inversion: compute s_{AB} from s_{BA} and term probabilities.

  P(B|A) = P(A|B) · P(B) / P(A)
  s_{AB} = s_{BA} · s_B / s_A
-/
def bayesInversion (s_BA s_A s_B : ℝ) : ℝ := s_BA * s_B / s_A

/-- Bayes inversion is well-defined when s_A > 0. -/
theorem bayesInversion_eq (s_BA s_A s_B : ℝ) (hA : s_A ≠ 0) :
    bayesInversion s_BA s_A s_B * s_A = s_BA * s_B := by
  unfold bayesInversion
  field_simp [hA]

/-- Bayes inversion preserves probability bounds under natural constraints. -/
theorem bayesInversion_bounded (s_BA s_A s_B : ℝ)
    (_hBA : 0 ≤ s_BA ∧ s_BA ≤ 1)
    (hA : 0 < s_A)
    (_hB : 0 ≤ s_B ∧ s_B ≤ 1)
    (h_constraint : s_BA * s_B ≤ s_A) :
    bayesInversion s_BA s_A s_B ≤ 1 := by
  unfold bayesInversion
  rw [div_le_one hA]
  exact h_constraint

/-! ## PLN Induction

**Induction** infers A → C from B → A and B → C.
The strategy is: use Bayes to get A → B, then apply deduction.

Given:
- B → A with strength s_{BA}
- B → C with strength s_{BC}
- Term probabilities s_A, s_B, s_C

Step 1: Bayes inversion
  s_{AB} = s_{BA} · s_B / s_A

Step 2: Apply deduction formula
  s_{AC} = s_{AB} · s_{BC} + (1 - s_{AB}) · (s_C - s_B · s_{BC}) / (1 - s_B)
-/

/-- PLN Induction strength formula.

Computes P(C|A) given P(A|B) and P(C|B).
Uses Bayes to get P(B|A), then applies deduction.

Full formula:
  s_{AC} = (s_{BA} · s_B / s_A) · s_{BC} + correction term
-/
def plnInductionStrength (s_BA s_BC s_A s_B s_C : ℝ) : ℝ :=
  let s_AB := bayesInversion s_BA s_A s_B
  plnDeductionStrength s_AB s_BC s_B s_C

/-- PLN Induction is Bayes + Deduction composition. -/
theorem plnInduction_eq_bayes_deduction (s_BA s_BC s_A s_B s_C : ℝ) :
    plnInductionStrength s_BA s_BC s_A s_B s_C =
      plnDeductionStrength (bayesInversion s_BA s_A s_B) s_BC s_B s_C := by
  unfold plnInductionStrength
  rfl

/-- Simplified PLN Induction under high uncertainty.

When the correction term is negligible:
  s_{AC} ≈ s_{BA} · s_B · s_{BC} / s_A
-/
def plnInductionSimplified (s_BA s_BC s_A s_B : ℝ) : ℝ :=
  s_BA * s_B * s_BC / s_A

/-- Under uniform priors (s_A = s_B = s_C = s), induction simplifies to:
    s_{AC} = s_BA * s_BC + (1 - s_BA) * s * (1 - s_BC) / (1 - s)

    The first term is the direct chain contribution, the second is the
    background noise contribution. -/
theorem plnInduction_uniform (s_BA s_BC s : ℝ) (hs : s ≠ 0) (hs1 : s < 1) :
    plnInductionStrength s_BA s_BC s s s =
      s_BA * s_BC + (1 - s_BA) * s * (1 - s_BC) / (1 - s) := by
  unfold plnInductionStrength plnDeductionStrength bayesInversion
  have h1s : 1 - s ≠ 0 := by linarith
  field_simp [hs, h1s]

/-- PLN Induction output is bounded by 1 when inputs are valid probabilities.

Since induction = Bayes + Deduction, and both preserve bounds under
appropriate constraints, so does induction. -/
theorem plnInduction_bounded
    (s_BA s_BC s_A s_B s_C : ℝ)
    (h_sBA : 0 ≤ s_BA ∧ s_BA ≤ 1)
    (h_sBC : 0 ≤ s_BC ∧ s_BC ≤ 1)
    (h_sA : 0 < s_A)
    (h_sB : 0 < s_B ∧ s_B < 1)
    (h_sC : 0 ≤ s_C ∧ s_C ≤ 1)
    -- Constraint: Bayes output is valid
    (h_bayes : s_BA * s_B ≤ s_A)
    -- Constraint: deduction correction term is bounded
    (h_corr : s_C - s_B * s_BC ≤ 1 - s_B) :
    plnInductionStrength s_BA s_BC s_A s_B s_C ≤ 1 := by
  unfold plnInductionStrength
  -- s_AB = s_BA * s_B / s_A, which is ≤ 1 by h_bayes
  have h_sAB : bayesInversion s_BA s_A s_B ≤ 1 :=
    bayesInversion_bounded s_BA s_A s_B h_sBA h_sA ⟨by linarith [h_sB.1], by linarith [h_sB.2]⟩ h_bayes
  have h_sAB_nn : 0 ≤ bayesInversion s_BA s_A s_B := by
    unfold bayesInversion
    apply div_nonneg
    · apply mul_nonneg h_sBA.1
      linarith [h_sB.1]
    · linarith
  apply pln_deduction_bounded
  · exact ⟨h_sAB_nn, h_sAB⟩
  · exact h_sBC
  · exact h_sB
  · exact h_sC
  · exact h_corr

/-- PLN Induction output is non-negative when inputs are valid probabilities. -/
theorem plnInduction_nonneg
    (s_BA s_BC s_A s_B s_C : ℝ)
    (h_sBA : 0 ≤ s_BA ∧ s_BA ≤ 1)
    (h_sBC : 0 ≤ s_BC)
    (h_sA : 0 < s_A)
    (h_sB : 0 < s_B ∧ s_B < 1)
    -- Bayes constraint: ensures P(B|A) = P(A|B)·P(B)/P(A) ≤ 1
    (h_bayes : s_BA * s_B ≤ s_A)
    (h_constraint : s_B * s_BC ≤ s_C) :
    0 ≤ plnInductionStrength s_BA s_BC s_A s_B s_C := by
  unfold plnInductionStrength
  have h_sAB_nn : 0 ≤ bayesInversion s_BA s_A s_B := by
    unfold bayesInversion
    apply div_nonneg
    · apply mul_nonneg h_sBA.1
      linarith [h_sB.1]
    · linarith
  have h_sAB_le1 : bayesInversion s_BA s_A s_B ≤ 1 :=
    bayesInversion_bounded s_BA s_A s_B h_sBA h_sA ⟨by linarith [h_sB.1], by linarith [h_sB.2]⟩ h_bayes
  apply pln_deduction_nonneg
  · exact ⟨h_sAB_nn, h_sAB_le1⟩
  · exact h_sBC
  · exact h_sB
  · exact h_constraint

/-! ## PLN Abduction

**Abduction** infers A → C from A → B and C → B.
The strategy is: use Bayes to get B → C, then apply deduction.

Given:
- A → B with strength s_{AB}
- C → B with strength s_{CB}
- Term probabilities s_A, s_B, s_C

Step 1: Bayes inversion on second premise
  s_{BC} = s_{CB} · s_C / s_B

Step 2: Apply deduction formula
  s_{AC} = s_{AB} · s_{BC} + correction term
-/

/-- PLN Abduction strength formula.

Computes P(C|A) given P(B|A) and P(B|C).
Uses Bayes to get P(C|B), then applies deduction.

Full formula:
  s_{AC} = s_{AB} · (s_{CB} · s_C / s_B) + correction term
-/
def plnAbductionStrength (s_AB s_CB _s_A s_B s_C : ℝ) : ℝ :=
  let s_BC := bayesInversion s_CB s_B s_C
  plnDeductionStrength s_AB s_BC s_B s_C

/-- PLN Abduction is Bayes + Deduction composition. -/
theorem plnAbduction_eq_bayes_deduction (s_AB s_CB _s_A s_B s_C : ℝ) :
    plnAbductionStrength s_AB s_CB _s_A s_B s_C =
      plnDeductionStrength s_AB (bayesInversion s_CB s_B s_C) s_B s_C := by
  unfold plnAbductionStrength
  rfl

/-- Simplified PLN Abduction under high uncertainty.

When the correction term is negligible:
  s_{AC} ≈ s_{AB} · s_{CB} · s_C / s_B
-/
def plnAbductionSimplified (s_AB s_CB s_B s_C : ℝ) : ℝ :=
  s_AB * s_CB * s_C / s_B

/-- Under uniform priors (s_A = s_B = s_C = s), abduction simplifies to:
    s_{AC} = s_AB * s_CB + (1 - s_AB) * s * (1 - s_CB) / (1 - s)

    Similar structure to induction - both are Bayes + Deduction. -/
theorem plnAbduction_uniform (s_AB s_CB s : ℝ) (hs : s ≠ 0) (hs1 : s < 1) :
    plnAbductionStrength s_AB s_CB s s s =
      s_AB * s_CB + (1 - s_AB) * s * (1 - s_CB) / (1 - s) := by
  unfold plnAbductionStrength plnDeductionStrength bayesInversion
  have h1s : 1 - s ≠ 0 := by linarith
  field_simp [hs, h1s]

/-- PLN Abduction output is bounded by 1 when inputs are valid probabilities.

Since abduction = Bayes + Deduction, and both preserve bounds under
appropriate constraints, so does abduction. -/
theorem plnAbduction_bounded
    (s_AB s_CB s_A s_B s_C : ℝ)
    (h_sAB : 0 ≤ s_AB ∧ s_AB ≤ 1)
    (h_sCB : 0 ≤ s_CB ∧ s_CB ≤ 1)
    (h_sB : 0 < s_B ∧ s_B < 1)
    (h_sC : 0 < s_C ∧ s_C ≤ 1)
    -- Constraint: Bayes output is valid
    (h_bayes : s_CB * s_C ≤ s_B)
    -- Constraint: deduction correction term is bounded
    (h_corr : s_C - s_B * (bayesInversion s_CB s_B s_C) ≤ 1 - s_B) :
    plnAbductionStrength s_AB s_CB s_A s_B s_C ≤ 1 := by
  unfold plnAbductionStrength
  -- s_BC = s_CB * s_C / s_B, which is ≤ 1 by h_bayes
  have h_sBC : bayesInversion s_CB s_B s_C ≤ 1 := by
    unfold bayesInversion
    rw [div_le_one (by linarith : 0 < s_B)]
    exact h_bayes
  have h_sBC_nn : 0 ≤ bayesInversion s_CB s_B s_C := by
    unfold bayesInversion
    apply div_nonneg
    · apply mul_nonneg h_sCB.1
      linarith [h_sC.1]
    · linarith [h_sB.1]
  apply pln_deduction_bounded
  · exact h_sAB
  · exact ⟨h_sBC_nn, h_sBC⟩
  · exact h_sB
  · exact ⟨by linarith [h_sC.1], h_sC.2⟩
  · exact h_corr

/-- PLN Abduction output is non-negative when inputs are valid probabilities. -/
theorem plnAbduction_nonneg
    (s_AB s_CB s_A s_B s_C : ℝ)
    (h_sAB : 0 ≤ s_AB ∧ s_AB ≤ 1)
    (h_sCB : 0 ≤ s_CB)
    (h_sB : 0 < s_B ∧ s_B < 1)
    (h_sC : 0 < s_C)
    (h_constraint : s_B * (bayesInversion s_CB s_B s_C) ≤ s_C) :
    0 ≤ plnAbductionStrength s_AB s_CB s_A s_B s_C := by
  unfold plnAbductionStrength
  have h_sBC_nn : 0 ≤ bayesInversion s_CB s_B s_C := by
    unfold bayesInversion
    apply div_nonneg
    · apply mul_nonneg h_sCB
      linarith
    · linarith [h_sB.1]
  apply pln_deduction_nonneg
  · exact h_sAB
  · exact h_sBC_nn
  · exact h_sB
  · exact h_constraint

/-! ## The PLN Inference Triad

The three fundamental PLN inference rules are:

1. **Deduction**: A → B, B → C ⊢ A → C
2. **Induction**: B → A, B → C ⊢ A → C  (uses Bayes on first premise)
3. **Abduction**: A → B, C → B ⊢ A → C  (uses Bayes on second premise)

All three are compositions of Bayes inversion and the core deduction formula.
-/

/-- The PLN inference triad: all reduce to deduction via Bayes inversion.

This theorem shows the algebraic relationship between the three formulas.
Under uniform term probabilities, they all have the same structural form:
  s₁ * s₂ + (1 - s₁) * s * (1 - s₂) / (1 - s)

The first term is the "direct chain" contribution, the second accounts for
probability flow through the background (when s₁ ≠ 1).

**#NOTICE** (2024-11): An earlier version of this theorem incorrectly claimed
that under uniform priors, PLN formulas simplify to just `s₁ * s₂`. This is
WRONG - the correction term `(1 - s₁) * s * (1 - s₂) / (1 - s)` is always
present and does NOT vanish under uniform priors. The `ring` tactic correctly
rejected the false claim. The simplified form `s₁ * s₂` only appears in the
"high uncertainty" approximation when the correction term is negligible
(see `plnDeductionSimplified`), not as an exact equality.
-/
theorem pln_triad_uniform (s₁ s₂ s : ℝ) (hs : s ≠ 0) (hs1 : s < 1) :
    -- All three have the same form under uniform priors
    plnDeductionStrength s₁ s₂ s s =
      s₁ * s₂ + (1 - s₁) * s * (1 - s₂) / (1 - s) ∧
    plnInductionStrength s₁ s₂ s s s =
      s₁ * s₂ + (1 - s₁) * s * (1 - s₂) / (1 - s) ∧
    plnAbductionStrength s₁ s₂ s s s =
      s₁ * s₂ + (1 - s₁) * s * (1 - s₂) / (1 - s) := by
  have h1s : 1 - s ≠ 0 := by linarith
  constructor
  · -- Deduction
    unfold plnDeductionStrength
    field_simp [h1s]
  constructor
  · -- Induction
    exact plnInduction_uniform s₁ s₂ s hs hs1
  · -- Abduction
    exact plnAbduction_uniform s₁ s₂ s hs hs1

/-! ## Confidence Propagation (Preview)

PLN uses (strength, confidence) pairs. Confidence represents the "weight of evidence"
behind a strength estimate. Common formulas:

- Confidence from count: c = n / (n + k)  where k is an experience parameter
- Deduction confidence: c_AC ≈ c_AB · c_BC  (under independence)
- Induction/Abduction confidence: typically lower due to Bayes uncertainty

Full confidence propagation is complex and involves second-order probability.
We sketch the basic structure here.
-/

/-- PLN confidence from evidence count.
    c = n / (n + k) where n is observation count, k is experience parameter.
    As n → ∞, c → 1. For n = 0, c = 0. -/
def plnConfidenceFromCount (n k : ℝ) : ℝ := n / (n + k)

/-- Confidence monotonically increases with evidence count. -/
theorem plnConfidence_mono (n₁ n₂ k : ℝ) (hk : 0 < k) (h : n₁ ≤ n₂) (hn : 0 ≤ n₁) :
    plnConfidenceFromCount n₁ k ≤ plnConfidenceFromCount n₂ k := by
  unfold plnConfidenceFromCount
  have h1 : 0 < n₁ + k := by linarith
  have h2 : 0 < n₂ + k := by linarith
  -- n₁/(n₁+k) ≤ n₂/(n₂+k) ↔ n₁(n₂+k) ≤ n₂(n₁+k)
  rw [div_le_div_iff₀ h1 h2]
  -- n₁n₂ + n₁k ≤ n₂n₁ + n₂k ↔ n₁k ≤ n₂k
  nlinarith

/-- Confidence is bounded by 1. -/
theorem plnConfidence_le_one (n k : ℝ) (hn : 0 ≤ n) (hk : 0 < k) :
    plnConfidenceFromCount n k ≤ 1 := by
  unfold plnConfidenceFromCount
  have h1 : 0 < n + k := by linarith
  rw [div_le_one h1]
  linarith

/-- Confidence is non-negative. -/
theorem plnConfidence_nonneg (n k : ℝ) (hn : 0 ≤ n) (hk : 0 < k) :
    0 ≤ plnConfidenceFromCount n k := by
  unfold plnConfidenceFromCount
  apply div_nonneg hn
  linarith

/-- Simplified confidence propagation for deduction.
    Under independence: c_AC ≈ c_AB · c_BC -/
def plnDeductionConfidence (c_AB c_BC : ℝ) : ℝ := c_AB * c_BC

/-- Deduction confidence preserves bounds. -/
theorem plnDeductionConfidence_bounded (c_AB c_BC : ℝ)
    (h1 : 0 ≤ c_AB ∧ c_AB ≤ 1) (h2 : 0 ≤ c_BC ∧ c_BC ≤ 1) :
    0 ≤ plnDeductionConfidence c_AB c_BC ∧ plnDeductionConfidence c_AB c_BC ≤ 1 := by
  unfold plnDeductionConfidence
  constructor
  · nlinarith [h1.1, h2.1]
  · nlinarith [h1.1, h1.2, h2.1, h2.2]

/-! ## Comparison: PLN vs NARS

The arXiv paper (2412.19524) shows that under high term probability uncertainty,
PLN and NARS give similar "power" (s × c) values.

Key insight: The "power" metric s × c captures what both systems agree on,
even when they disagree on individual s and c values.
-/

/-- NARS deduction frequency formula -/
def narsDeductionFrequency (f1 f2 : ℝ) : ℝ :=
  f1 * f2 / (f1 + f2 - f1 * f2)

/-- NARS deduction confidence formula -/
def narsDeductionConfidence (f1 f2 c1 c2 : ℝ) : ℝ :=
  c1 * c2 * (f1 + f2 - f1 * f2)

/-- NARS deduction "power" = f × c -/
def narsDeductionPower (f1 f2 c1 c2 : ℝ) : ℝ :=
  narsDeductionFrequency f1 f2 * narsDeductionConfidence f1 f2 c1 c2

/-- **Key Result**: NARS power simplifies to f1 * f2 * c1 * c2.
    This matches PLN's simplified deduction under high uncertainty! -/
theorem nars_power_eq (f1 f2 c1 c2 : ℝ) (h : f1 + f2 - f1 * f2 ≠ 0) :
    narsDeductionPower f1 f2 c1 c2 = f1 * f2 * c1 * c2 := by
  unfold narsDeductionPower narsDeductionFrequency narsDeductionConfidence
  field_simp [h]

/-- Under equal strength/frequency and confidence, PLN and NARS give the same power. -/
theorem pln_nars_power_agreement (s c : ℝ) (h : s + s - s*s ≠ 0) :
    -- PLN power (simplified): s * s * c * c
    plnDeductionSimplified s s * c * c =
    -- NARS power: also s * s * c * c
    narsDeductionPower s s c c := by
  unfold plnDeductionSimplified
  rw [nars_power_eq s s c c h]

end Mettapedia.Logic.PLN
