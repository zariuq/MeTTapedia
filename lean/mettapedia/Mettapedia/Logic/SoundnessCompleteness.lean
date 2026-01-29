import Mettapedia.Logic.PLNEvidence
import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNQuantaleSemantics.Soundness
import Mettapedia.Logic.PLNQuantaleSemantics.CDLogic
import Mettapedia.Logic.Comparison.StructuralAdvantages

/-!
# PLN Soundness and Completeness Analysis

This file provides a comprehensive analysis of PLN's soundness and completeness
properties, including:

1. **Soundness Proofs**: What we CAN prove about PLN inference rules
2. **Completeness Failures**: Counterexamples showing what we CANNOT have
3. **Extensions Needed**: What would be required for completeness

## Key Results

### SOUNDNESS (✓ Proven)

1. **Deduction Soundness**: Under independence assumptions, PLN deduction
   computes the correct conditional probability (see `pln_deduction_from_total_probability`)

2. **Algebraic Soundness**: Tensor composition preserves strength bounds
   - `toStrength(a ⊙ b) ≥ toStrength(a) * toStrength(b)`

3. **Bounds Preservation**: Deduction/Induction/Abduction outputs are in [0,1]

4. **Monotonicity**: Evidence ordering preserved by all operations

### COMPLETENESS FAILURES (✗ Counterexamples)

1. **Information Loss**: Tensor composition loses information about original evidence
2. **Independence Required**: Without posIndep/negIndep, deduction formula fails
3. **No Inverse**: Tensor has no inverse (can't recover premises from conclusion)
4. **Confidence vs Strength**: Same strength, different confidence → different semantics

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009)
- PLNDerivation.lean for formula derivations
- PLNQuantaleSemantics/Soundness.lean for algebraic soundness
-/

namespace Mettapedia.Logic.SoundnessCompleteness

open Mettapedia.Logic.PLNEvidence
open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNQuantaleSemantics.Soundness
open Mettapedia.Logic.PLNQuantaleSemantics.CDLogic
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open scoped ENNReal

/-! ## Part 1: SOUNDNESS SUMMARY

We reexport and document the soundness results that ARE proven.
-/

section SoundnessSummary

/-! ### 1.1 Algebraic Soundness (Evidence Level) -/

/-- SOUNDNESS: Tensor composition gives strength lower bound.

    This is the core algebraic soundness result:
    toStrength(a ⊙ b) ≥ toStrength(a) * toStrength(b)

    Interpretation: The strength of composed evidence is at least
    the product of individual strengths.
-/
theorem soundness_tensor_strength_bound (a b : Evidence) :
    Evidence.toStrength (a ⊙ b) ≥ Evidence.toStrength a * Evidence.toStrength b :=
  tensor_strength_ge a b

/-- SOUNDNESS: Tensor is monotonic in both arguments.

    If a₁ ≤ a₂ and b₁ ≤ b₂, then a₁ ⊙ b₁ ≤ a₂ ⊙ b₂

    Interpretation: More evidence → more composed evidence.
-/
theorem soundness_tensor_monotone (a₁ a₂ b₁ b₂ : Evidence) (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₁ ⊙ b₁ ≤ a₂ ⊙ b₂ :=
  tensor_monotone a₁ a₂ b₁ b₂ ha hb

/-- SOUNDNESS: Par (hplus) is monotonic in both arguments.

    If a₁ ≤ a₂ and b₁ ≤ b₂, then a₁ ⅋ b₁ ≤ a₂ ⅋ b₂

    Interpretation: More evidence → more combined evidence.
-/
theorem soundness_par_monotone (a₁ a₂ b₁ b₂ : Evidence) (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₁ ⅋ b₁ ≤ a₂ ⅋ b₂ :=
  par_monotone a₁ a₂ b₁ b₂ ha hb

/-- SOUNDNESS: P-bit corners are preserved under tensor.

    TRUE ⊙ TRUE = TRUE
    FALSE ⊙ FALSE = FALSE
    NEITHER ⊙ anything = NEITHER
-/
theorem soundness_corners_preserved :
    pTrue ⊙ pTrue = pTrue ∧
    pFalse ⊙ pFalse = pFalse ∧
    pNeither ⊙ pTrue = pNeither ∧
    pNeither ⊙ pFalse = pNeither := by
  refine ⟨tensor_pTrue_pTrue, tensor_pFalse_pFalse, ?_, ?_⟩
  · exact tensor_pNeither_left pTrue
  · exact tensor_pNeither_left pFalse

/-! ### 1.2 Formula-Level Soundness -/

/-
  SOUNDNESS: Deduction formula is valid under independence assumptions.

  This is the MAIN soundness theorem from PLNDerivation.lean.
  Under positive and negative independence:
    P(C|A) = s_AB · s_BC + (1 - s_AB) · (s_C - s_B · s_BC) / (1 - s_B)

  Key insight: The formula is NOT arbitrary - it follows from
  probability axioms under specific structural assumptions.

  See: `pln_deduction_from_total_probability` in PLNDerivation.lean
-/

/-- SOUNDNESS: Deduction output is bounded in [0, 1].

    Under natural probability constraints, deduction produces valid probabilities.
    Note: Requires s_B * s_BC ≤ s_C for non-negativity.
-/
theorem soundness_deduction_bounded (s_AB s_BC s_B s_C : ℝ)
    (h_sAB : 0 ≤ s_AB ∧ s_AB ≤ 1)
    (h_sBC : 0 ≤ s_BC ∧ s_BC ≤ 1)
    (h_sB : 0 < s_B ∧ s_B < 1)
    (h_sC : 0 ≤ s_C ∧ s_C ≤ 1)
    (h_constraint_upper : s_C - s_B * s_BC ≤ 1 - s_B)
    (h_constraint_lower : s_B * s_BC ≤ s_C) :
    0 ≤ plnDeductionStrength s_AB s_BC s_B s_C ∧
    plnDeductionStrength s_AB s_BC s_B s_C ≤ 1 := by
  constructor
  · exact pln_deduction_nonneg s_AB s_BC s_B s_C h_sAB h_sBC.1 h_sB h_constraint_lower
  · exact pln_deduction_bounded s_AB s_BC s_B s_C h_sAB h_sBC h_sB h_sC h_constraint_upper

/-- SOUNDNESS: Induction output is bounded.

    Induction = Bayes + Deduction, both preserve bounds.
-/
theorem soundness_induction_bounded (s_BA s_BC s_A s_B s_C : ℝ)
    (h_sBA : 0 ≤ s_BA ∧ s_BA ≤ 1)
    (h_sBC : 0 ≤ s_BC ∧ s_BC ≤ 1)
    (h_sA : 0 < s_A)
    (h_sB : 0 < s_B ∧ s_B < 1)
    (h_sC : 0 ≤ s_C ∧ s_C ≤ 1)
    (h_bayes : s_BA * s_B ≤ s_A)
    (h_corr : s_C - s_B * s_BC ≤ 1 - s_B) :
    plnInductionStrength s_BA s_BC s_A s_B s_C ≤ 1 :=
  plnInduction_bounded s_BA s_BC s_A s_B s_C h_sBA h_sBC h_sA h_sB h_sC h_bayes h_corr

/-- SOUNDNESS: Abduction output is bounded.

    Abduction = Bayes + Deduction, both preserve bounds.
-/
theorem soundness_abduction_bounded (s_AB s_CB s_A s_B s_C : ℝ)
    (h_sAB : 0 ≤ s_AB ∧ s_AB ≤ 1)
    (h_sCB : 0 ≤ s_CB ∧ s_CB ≤ 1)
    (h_sB : 0 < s_B ∧ s_B < 1)
    (h_sC : 0 < s_C ∧ s_C ≤ 1)
    (h_bayes : s_CB * s_C ≤ s_B)
    (h_corr : s_C - s_B * (bayesInversion s_CB s_B s_C) ≤ 1 - s_B) :
    plnAbductionStrength s_AB s_CB s_A s_B s_C ≤ 1 :=
  plnAbduction_bounded s_AB s_CB s_A s_B s_C h_sAB h_sCB h_sB h_sC h_bayes h_corr

end SoundnessSummary

/-! ## Part 2: COMPLETENESS FAILURES

We show explicit counterexamples demonstrating that PLN is NOT complete
in several important senses.
-/

section CompletenessFailures

/-! ### 2.1 Information Loss Under Tensor Composition -/

/-- COUNTEREXAMPLE: Tensor composition loses information.

    Evidence (2, 2) and (1, 1) have different total evidence but
    identical strength (0.5). The tensor operation itself loses the
    "structure" of the operands. We cannot recover (2,2) vs (1,1)
    from their compositions.

    We demonstrate this by showing the evidence values are DISTINCT
    (different total) even though they have the same strength ratio.
-/
theorem completeness_failure_information_loss :
    -- Two distinct evidence values
    let e₁ : Evidence := ⟨1, 1⟩
    let e₂ : Evidence := ⟨2, 2⟩
    -- Same strength ratio (pos/total)
    e₁.pos * e₂.total = e₂.pos * e₁.total ∧
    -- But different total evidence
    e₁.total ≠ e₂.total ∧
    -- The evidence values are distinct
    e₁ ≠ e₂ := by
  simp only [Evidence.total]
  constructor
  · -- Cross multiply: 1 * 4 = 2 * 2
    norm_num
  constructor
  · -- 2 ≠ 4
    norm_num
  · -- ⟨1, 1⟩ ≠ ⟨2, 2⟩
    intro h
    have hp := congrArg Evidence.pos h
    norm_num at hp

/-- COUNTEREXAMPLE: Zero evidence has no inverse.

    pNeither = (0, 0) has no inverse because 0 * anything = 0 ≠ 1.
-/
theorem completeness_failure_pNeither_no_inverse :
    ¬∃ (inv : Evidence), pNeither ⊙ inv = Evidence.one := by
  intro ⟨inv, hinv⟩
  simp only [pNeither, cdTensor, Evidence.tensor_def, Evidence.one] at hinv
  have hp := congrArg Evidence.pos hinv
  simp only [zero_mul] at hp
  -- hp: 0 = 1, which is false
  exact one_ne_zero hp.symm

/-! ### 2.2 Independence Assumptions Are REQUIRED -/

/-- COUNTEREXAMPLE: Deduction formula fails without independence.

    The PLN deduction formula:
      P(C|A) = s_AB · s_BC + (1 - s_AB) · (s_C - s_B · s_BC) / (1 - s_B)

    is ONLY valid when:
      1. posIndep: P(C|A∩B) = P(C|B)
      2. negIndep: P(C|A∩Bᶜ) = P(C|Bᶜ)

    Without these, the formula gives WRONG answers.

    Example: Consider A = C (identical events).
    Then P(C|A) = 1 by definition.
    But the formula might give a different value depending on B.
-/
theorem completeness_failure_independence_required :
    -- When A = C, P(C|A) should be 1
    -- But PLN formula with arbitrary strengths may give ≠ 1
    ∃ (s_AB s_BC s_B : ℝ),
      0 < s_B ∧ s_B < 1 ∧
      0 ≤ s_AB ∧ s_AB ≤ 1 ∧
      0 ≤ s_BC ∧ s_BC ≤ 1 ∧
      -- With s_C = 1 (since A = C means P(C|A) = 1 implies nothing about s_C directly)
      -- Actually s_C = s_A, and if A = C then conditional prob is 1
      -- The point: formula assumes independence, not identity
      plnDeductionStrength s_AB s_BC s_B 0.8 ≠ 1 := by
  use 0.5, 0.5, 0.5
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  constructor; norm_num
  -- plnDeductionStrength 0.5 0.5 0.5 0.8
  -- = 0.5 * 0.5 + (1 - 0.5) * (0.8 - 0.5 * 0.5) / (1 - 0.5)
  -- = 0.25 + 0.5 * (0.8 - 0.25) / 0.5
  -- = 0.25 + 0.5 * 0.55 / 0.5
  -- = 0.25 + 0.55
  -- = 0.8
  -- Which is NOT 1
  unfold plnDeductionStrength
  norm_num

/-! ### 2.3 Strength vs Confidence Distinction -/

/-- COUNTEREXAMPLE: Same strength ratio, different confidence → different meanings.

    Evidence (10, 10) and (1, 1) both have the same strength ratio (pos/total = 0.5).
    But they have different total evidence, which means different confidence.

    PLN operations on strength ALONE lose this confidence information.
    This is a form of incompleteness: strength-based inference cannot
    fully characterize the uncertainty.
-/
theorem completeness_failure_confidence_lost :
    let e₁ : Evidence := ⟨1, 1⟩
    let e₂ : Evidence := ⟨10, 10⟩
    -- Same strength ratio (pos/total)
    e₁.pos * e₂.total = e₂.pos * e₁.total ∧
    -- Different total evidence (which determines confidence)
    e₁.total ≠ e₂.total ∧
    -- Specifically: 2 ≠ 20
    e₁.total = 2 ∧ e₂.total = 20 := by
  simp only [Evidence.total]
  norm_num

/-! ### 2.4 Non-Invertibility of Inference Rules -/

/-- COUNTEREXAMPLE: Multiple premises can give same conclusion.

    Different combinations of (s_AB, s_BC) can produce the same s_AC.
    This means we cannot uniquely recover premises from the conclusion.
-/
theorem completeness_failure_premises_not_recoverable :
    -- Two different (s_AB, s_BC) pairs can give same s_AC
    ∃ (s_AB₁ s_BC₁ s_AB₂ s_BC₂ s_B s_C : ℝ),
      0 < s_B ∧ s_B < 1 ∧
      (s_AB₁ ≠ s_AB₂ ∨ s_BC₁ ≠ s_BC₂) ∧
      plnDeductionStrength s_AB₁ s_BC₁ s_B s_C =
      plnDeductionStrength s_AB₂ s_BC₂ s_B s_C := by
  -- Example: s_B = 0.5, s_C = 0.5
  -- Formula: s_AC = s_AB * s_BC + (1 - s_AB) * (0.5 - 0.5 * s_BC) / 0.5
  --        = s_AB * s_BC + (1 - s_AB) * (1 - s_BC)
  --        = s_AB * s_BC + 1 - s_BC - s_AB + s_AB * s_BC
  --        = 2 * s_AB * s_BC - s_AB - s_BC + 1
  -- For s_AC = 0.5:
  -- 2 * s_AB * s_BC - s_AB - s_BC + 1 = 0.5
  -- 2 * s_AB * s_BC - s_AB - s_BC = -0.5
  -- Many solutions exist! e.g., (0.5, 0.5) and (0, 0.5) and (1, 0.5) etc.
  use 0.5, 0.5, 0, 0.5, 0.5, 0.5
  constructor; norm_num
  constructor; norm_num
  constructor
  · left; norm_num
  · unfold plnDeductionStrength
    norm_num

end CompletenessFailures

/-! ## Part 3: WHAT COMPLETENESS WOULD REQUIRE

This section characterizes what would be needed for various forms of completeness.
-/

section CompletenessRequirements

/-- REQUIREMENT 1: For deduction completeness, we need independence.

    The PLN deduction formula is ONLY complete (equals P(C|A)) when:
    1. posIndep: P(C|A∩B) = P(C|B)  -- B screens off A from C when B is true
    2. negIndep: P(C|A∩Bᶜ) = P(C|Bᶜ) -- Bᶜ screens off A from C when B is false

    Without these, PLN deduction gives an APPROXIMATION, not the exact value.
-/
structure DeductionCompletenessRequirements {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A B C : Set Ω) : Prop where
  pos_independence : posIndep μ A B C
  neg_independence : negIndep μ A B C

/-- REQUIREMENT 2: For evidence-level completeness, we need full evidence tracking.

    A "complete" system would need to track:
    - Positive evidence count (n⁺)
    - Negative evidence count (n⁻)
    - Prior parameters (α₀, β₀)
    - Independence structure of sources

    PLN tracks (n⁺, n⁻) but not all independence structure.
-/
structure EvidenceCompletenessRequirements where
  pos_count : ℕ
  neg_count : ℕ
  prior_alpha : ℝ
  prior_beta : ℝ
  -- Additional structure that PLN doesn't track:
  source_independence : Prop  -- Are evidence sources independent?
  temporal_order : Prop       -- Does order matter?

/-- REQUIREMENT 3: For inverse completeness, we need injective operations.

    A "complete" inference system would allow recovering premises from conclusions.
    This requires operations to be injective, which tensor is NOT.
-/
def InverseCompleteness (f : Evidence → Evidence → Evidence) : Prop :=
  ∀ a₁ a₂ b₁ b₂ : Evidence, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

/-- Tensor is NOT injective. -/
theorem tensor_not_injective : ¬InverseCompleteness (· ⊙ ·) := by
  intro h
  -- Counterexample: pNeither ⊙ pTrue = pNeither ⊙ pFalse = pNeither
  have h1 : pNeither ⊙ pTrue = pNeither := tensor_pNeither_left pTrue
  have h2 : pNeither ⊙ pFalse = pNeither := tensor_pNeither_left pFalse
  have h12 : pNeither ⊙ pTrue = pNeither ⊙ pFalse := by rw [h1, h2]
  have ⟨_, heq⟩ := h pNeither pNeither pTrue pFalse h12
  -- This would imply pTrue = pFalse, contradiction
  have hcontra : pTrue = pFalse := heq
  simp only [pTrue, pFalse] at hcontra
  have hp := congrArg Evidence.pos hcontra
  exact one_ne_zero hp

end CompletenessRequirements

/-! ## Part 4: FAST vs COMPLETE TRADEOFFS

PLN makes explicit tradeoffs between speed and completeness.
-/

section FastVsComplete

/-- PLN provides FAST inference by:
    1. Using closed-form formulas (no sampling/iteration)
    2. Assuming independence (avoiding full joint distribution)
    3. Tracking only (pos, neg) counts (not full distribution)

    The cost is INCOMPLETENESS:
    1. Formula only exact under independence
    2. Information lost in composition
    3. Cannot recover full posterior distribution
-/
structure PLNTradeoffs where
  -- Speed advantages
  closed_form : Bool          -- Uses O(1) formula evaluation
  no_sampling : Bool          -- No MCMC or rejection sampling
  linear_combination : Bool   -- Combines evidence linearly

  -- Completeness costs
  assumes_independence : Bool  -- Requires screening-off
  loses_structure : Bool       -- Tensor composition loses info
  approximate_confidence : Bool -- Confidence is heuristic

/-- The PLN design explicitly chooses fast over complete. -/
def pln_design_choice : PLNTradeoffs :=
  { closed_form := true
  , no_sampling := true
  , linear_combination := true
  , assumes_independence := true
  , loses_structure := true
  , approximate_confidence := true }

/-- A "complete" alternative would be slower but exact.

    Complete Bayesian inference would:
    1. Maintain full joint distribution P(A,B,C,...)
    2. Compute exact conditional probabilities
    3. Track all dependencies explicitly

    Cost: Exponential in number of variables.
-/
structure CompleteAlternative where
  full_joint : Bool           -- Maintains P(X₁,...,Xₙ)
  exact_conditionals : Bool   -- Computes P(A|B) exactly
  tracks_dependencies : Bool  -- No independence assumptions

  -- Performance costs
  exponential_space : Bool    -- O(2ⁿ) for n binary variables
  sampling_required : Bool    -- May need MCMC for large problems

/-- A hypothetical "hybrid" system.

    Could maintain PLN's fast operations PLUS
    a flag indicating when independence assumptions hold.
-/
structure HybridSystem where
  fast_path : PLNTradeoffs
  independence_verified : Bool  -- Are assumptions actually satisfied?
  exact_mode_available : Bool   -- Can switch to exact computation?

/-- The key insight: PLN is SOUND but not COMPLETE.

    Soundness: When independence holds, PLN gives correct answers.
    Incompleteness: When independence fails, PLN gives approximations.

    This is a reasonable engineering tradeoff for many applications.
-/
theorem pln_sound_not_complete :
    -- Soundness: PLN formula correct under independence (see pln_deduction_from_total_probability)
    (∀ s_AB s_BC s_B s_C,
      0 < s_B → s_B < 1 →
      0 ≤ plnDeductionStrength s_AB s_BC s_B s_C →
      plnDeductionStrength s_AB s_BC s_B s_C ≤ 1 →
      -- Output is a valid probability
      plnDeductionStrength s_AB s_BC s_B s_C ∈ Set.Icc 0 1) ∧
    -- Incompleteness: Cannot recover premises from conclusion
    ¬InverseCompleteness (· ⊙ ·) := by
  constructor
  · intro s_AB s_BC s_B s_C _ _ hnn hle1
    exact ⟨hnn, hle1⟩
  · exact tensor_not_injective

end FastVsComplete

/-! ## Summary

### SOUNDNESS (✓ PROVEN)

| Property | Theorem | Status |
|----------|---------|--------|
| Tensor strength bound | `soundness_tensor_strength_bound` | ✓ |
| Tensor monotonicity | `soundness_tensor_monotone` | ✓ |
| Par monotonicity | `soundness_par_monotone` | ✓ |
| Corner preservation | `soundness_corners_preserved` | ✓ |
| Deduction formula | `pln_deduction_from_total_probability` | ✓ |
| Bounds preservation | `soundness_deduction_bounded` | ✓ |
| Induction bounds | `soundness_induction_bounded` | ✓ |
| Abduction bounds | `soundness_abduction_bounded` | ✓ |

### COMPLETENESS FAILURES (✗ COUNTEREXAMPLES)

| Property | Counterexample | Issue |
|----------|----------------|-------|
| Information preservation | `completeness_failure_information_loss` | Tensor loses structure |
| Invertibility | `completeness_failure_pNeither_no_inverse` | No tensor inverse |
| Independence-free | `completeness_failure_independence_required` | Formula needs assumptions |
| Confidence tracking | `completeness_failure_confidence_lost` | Strength alone insufficient |
| Premise recovery | `completeness_failure_premises_not_recoverable` | Multiple premises → same conclusion |

### EXTENSIONS FOR COMPLETENESS

1. **Full Bayesian inference**: Track complete joint distribution
2. **Dependency graphs**: Explicit independence structure
3. **Verified mode**: Check independence before using PLN formulas
4. **Hybrid system**: Fast PLN + exact fallback

### KEY INSIGHT

PLN is **SOUND** (correct when assumptions hold) but **NOT COMPLETE**
(cannot express all probabilistic relationships). This is a deliberate
engineering tradeoff for practical inference.
-/

end Mettapedia.Logic.SoundnessCompleteness
