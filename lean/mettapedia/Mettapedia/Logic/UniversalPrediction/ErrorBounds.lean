import Mettapedia.Logic.UniversalPrediction.ConvergenceCriteria
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Error Bounds (Hutter 2005, Theorem 3.36)

This file formalizes the error bounds for universal prediction from
Chapter 3 of Hutter's "Universal Artificial Intelligence".

## Main Definitions

* `optimalPrediction` - The optimal prediction given the true distribution μ
* `universalPrediction` - The prediction using the universal semimeasure ξ
* `errorProb` - Probability of prediction error at time t
* `expectedOptimalErrors` - Total expected errors for optimal predictor
* `expectedUniversalErrors` - Total expected errors for universal predictor

## Main Results

* Theorem 3.36: E^ξ - E^μ ≤ √(4·E^μ·S_n) + S_n

## References

- Hutter, M. (2005). "Universal Artificial Intelligence", Theorem 3.36
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators
open FiniteHorizon Convergence ConvergenceCriteria

namespace ErrorBounds

/-! ## Definitions for Prediction Errors -/

/-- Optimal prediction at time t given history x: predict argmax_b μ(b|x).
    For binary alphabet, predict true if μ(true|x) ≥ 1/2. -/
def optimalPrediction (μ : PrefixMeasure) (x : BinString) : Bool :=
  FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1/2

/-- Universal prediction at time t given history x: predict argmax_b ξ(b|x).
    For binary alphabet, predict true if ξ(true|x) ≥ 1/2. -/
def universalPrediction (ξ : Semimeasure) (x : BinString) : Bool :=
  FiniteHorizon.condProb ξ x true ≥ 1/2

/-- Probability of error for a prediction when true distribution is μ.
    Error occurs when predicted symbol ≠ actual symbol.

    For prediction b: error = 1 - μ(b|x) -/
def errorProb (μ : PrefixMeasure) (prediction : Bool) (x : BinString) : ℝ :=
  1 - FiniteHorizon.condProb μ.toSemimeasure x prediction

/-- Error probability for optimal predictor Θ_μ.
    e^μ_t(x_{<t}) = 1 - max{μ(b|x_{<t}) : b} = min{1 - μ(b|x_{<t}) : b} -/
def optimalErrorProb (μ : PrefixMeasure) (x : BinString) : ℝ :=
  errorProb μ (optimalPrediction μ x) x

/-- Error probability for universal predictor Θ_ξ (using true distribution μ). -/
def universalErrorProb (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString) : ℝ :=
  errorProb μ (universalPrediction ξ x) x

/-- Expected errors at horizon n for optimal predictor:
    E^μ_n = ∑_{t<n} E_μ[e^μ_t(x_{<t})]. -/
def expectedOptimalErrors (μ : PrefixMeasure) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, expectPrefix μ k (optimalErrorProb μ)

/-- Expected errors at horizon n for universal predictor:
    E^ξ_n = ∑_{t<n} E_μ[e^ξ_t(x_{<t})]. -/
def expectedUniversalErrors (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, expectPrefix μ k (universalErrorProb μ ξ)

/-! ## Key Properties -/

/-- Conditional probability is at most 1.
    This follows from ρ(x ++ b) ≤ ρ(x) by semimeasure monotonicity. -/
theorem condProb_le_one' (ρ : Semimeasure) (x : BinString) (b : Bool) :
    FiniteHorizon.condProb ρ x b ≤ 1 := by
  unfold FiniteHorizon.condProb conditionalENN
  -- condProb = ρ(x++b) / ρ(x) ≤ ρ(x) / ρ(x) = 1 when ρ(x) > 0
  -- When ρ(x) = 0, the division gives 0 ≤ 1
  by_cases hx0 : ρ x = 0
  · -- When ρ(x) = 0, division by 0 gives 0
    simp [hx0]
  · -- When ρ(x) > 0, use monotonicity
    have hxTop : ρ x ≠ ⊤ := semimeasure_ne_top ρ x
    have hmono : ρ (x ++ [b]) ≤ ρ x := by simpa using ρ.mono x b
    have h1Top : (1 : ENNReal) ≠ ⊤ := by simp
    -- The child is also finite
    have hchildTop : ρ (x ++ [b]) ≠ ⊤ := ne_top_of_le_ne_top hxTop hmono
    -- Now ρ(x++b)/ρ(x) ≤ ρ(x)/ρ(x) = 1
    have hdiv_le : ρ (x ++ [b]) / ρ x ≤ 1 := by
      rw [ENNReal.div_le_iff hx0 hxTop]
      simp [hmono]
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top h1Top hdiv_le) h1Top).mpr hdiv_le

/-- Error probability is in [0, 1]. -/
theorem errorProb_nonneg (μ : PrefixMeasure) (b : Bool) (x : BinString) :
    0 ≤ errorProb μ b x := by
  unfold errorProb
  have h := condProb_le_one' μ.toSemimeasure x b
  linarith

/-- The optimal predictor minimizes error probability.
    This is inequality (3.35): E^μ_n ≤ E^p_n for any predictor p. -/
theorem optimalErrorProb_le_errorProb (μ : PrefixMeasure) (x : BinString) (b : Bool) :
    optimalErrorProb μ x ≤ errorProb μ b x := by
  -- The optimal predictor chooses argmax μ(·|x), minimizing 1 - μ(·|x)
  unfold optimalErrorProb optimalPrediction errorProb
  -- Handle μ x = 0 case: both conditionals are 0, so all errors are 1
  by_cases hμx : μ x = 0
  · -- When μ x = 0, condProb is 0 (division by 0)
    have hpt0 : FiniteHorizon.condProb μ.toSemimeasure x true = 0 := by
      simp only [FiniteHorizon.condProb, conditionalENN]
      simp [hμx]
    have hpf0 : FiniteHorizon.condProb μ.toSemimeasure x false = 0 := by
      simp only [FiniteHorizon.condProb, conditionalENN]
      simp [hμx]
    -- Both errors are 1, optimal prediction is false (since 0 < 1/2)
    have hpt_lt_half : FiniteHorizon.condProb μ.toSemimeasure x true < 1/2 := by simp [hpt0]
    have hpred_eq : (decide (FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1/2)) = false := by
      simp only [decide_eq_false_iff_not, not_le]; exact hpt_lt_half
    -- Now simplify: optimalErrorProb = 1 - condProb(false) = 1 - 0 = 1
    rw [hpred_eq, hpf0]
    -- Goal: 1 - 0 ≤ 1 - condProb b
    match b with
    | false => rw [hpf0]
    | true => rw [hpt0]
  · -- When μ x ≠ 0, use pt + pf = 1
    have hsum : FiniteHorizon.condProb μ.toSemimeasure x true +
                FiniteHorizon.condProb μ.toSemimeasure x false = 1 :=
      Convergence.condProb_sum_eq_one μ x hμx
    have hpf_eq : FiniteHorizon.condProb μ.toSemimeasure x false =
                  1 - FiniteHorizon.condProb μ.toSemimeasure x true := by linarith
    -- Now analyze based on whether condProb true ≥ 1/2
    by_cases hpt_ge : FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1/2
    · -- optimalPrediction = true
      have hpred_eq : (decide (FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1/2)) = true := by
        simp only [decide_eq_true_iff]; exact hpt_ge
      rw [hpred_eq]
      -- optimalErrorProb = 1 - condProb true (error for true)
      match b with
      | false =>
        -- errorProb false = 1 - condProb false = 1 - (1 - condProb true) = condProb true
        -- Need: 1 - condProb true ≤ 1 - condProb false, i.e., condProb false ≤ condProb true
        rw [hpf_eq]
        linarith
      | true => rfl
    · -- optimalPrediction = false
      push_neg at hpt_ge
      have hpred_eq : (decide (FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1/2)) = false := by
        simp only [decide_eq_false_iff_not, not_le]; exact hpt_ge
      rw [hpred_eq]
      -- optimalErrorProb = 1 - condProb false (error for false)
      match b with
      | false => rfl
      | true =>
        -- errorProb true = 1 - condProb true
        -- Need: 1 - condProb false ≤ 1 - condProb true, i.e., condProb true ≤ condProb false
        rw [hpf_eq]
        linarith

/-- Expected errors for optimal predictor ≤ expected errors for universal predictor. -/
theorem expectedOptimalErrors_le_universal (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    expectedOptimalErrors μ n ≤ expectedUniversalErrors μ ξ n := by
  unfold expectedOptimalErrors expectedUniversalErrors
  apply Finset.sum_le_sum
  intro k _hk
  unfold expectPrefix
  apply Finset.sum_le_sum
  intro f _hf
  apply mul_le_mul_of_nonneg_left
  · exact optimalErrorProb_le_errorProb μ (List.ofFn f) _
  · exact ENNReal.toReal_nonneg

/-! ## Theorem 3.36: Error Bounds -/

/-- Key algebraic lemma for error bounds: u ≤ A + B·u²/2 when 2AB ≥ 1.
    This follows from analyzing the quadratic f(u) = A + Bu²/2 - u. -/
lemma am_gm_error_bound {A B u : ℝ} (hAB : 2 * A * B ≥ 1) (hA : A > 0) (hB : B > 0)
    (_hu0 : 0 ≤ u) (_hu1 : u ≤ 1) : u ≤ A + B * u ^ 2 / 2 := by
  -- The function f(u) = A + Bu²/2 - u has minimum at u = 1/B.
  -- We need f(u) ≥ 0 for all u ∈ [0, 1].
  -- Key: from 2AB ≥ 1, we get A ≥ 1/(2B).
  have hA_ge : A ≥ 1 / (2 * B) := by
    have h := hAB
    have hBpos : B > 0 := hB
    have : A * (2 * B) ≥ 1 := by linarith
    calc A = A * (2 * B) / (2 * B) := by field_simp
      _ ≥ 1 / (2 * B) := by apply div_le_div_of_nonneg_right this; linarith
  -- Now show u ≤ A + B*u²/2 via completing the square
  -- Rewrite as: A + B*u²/2 - u ≥ 0
  -- = B/2 * (u² - 2u/B) + A
  -- = B/2 * ((u - 1/B)² - 1/B²) + A
  -- = B/2 * (u - 1/B)² - 1/(2B) + A
  -- ≥ 0 - 1/(2B) + A = A - 1/(2B) ≥ 0 (by hA_ge)
  have hkey : A + B * u ^ 2 / 2 - u = B / 2 * (u - 1 / B) ^ 2 + (A - 1 / (2 * B)) := by
    field_simp
    ring
  have hsq_ge : B / 2 * (u - 1 / B) ^ 2 ≥ 0 := by
    apply mul_nonneg
    · linarith
    · exact sq_nonneg _
  have hdiff_ge : A - 1 / (2 * B) ≥ 0 := by linarith
  have hrhs_ge : B / 2 * (u - 1 / B) ^ 2 + (A - 1 / (2 * B)) ≥ 0 := by linarith
  linarith

/-- Helper: sqDistStep is non-negative -/
lemma sqDistStep_nonneg (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString) :
    0 ≤ sqDistStep μ ξ x := by
  unfold sqDistStep
  rw [Entropy.sqDistBinary_eq_two_mul]
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  exact sq_nonneg _

/-- Helper: When predictions agree, universalErrorProb = optimalErrorProb -/
lemma error_eq_when_predictions_agree (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (h : universalPrediction ξ x = optimalPrediction μ x) :
    universalErrorProb μ ξ x = optimalErrorProb μ x := by
  unfold universalErrorProb optimalErrorProb
  rw [h]

/-- Helper: Error probabilities for opposite predictions sum to 1 (when μ x ≠ 0) -/
lemma errorProb_true_add_false_eq_one (μ : PrefixMeasure) (x : BinString) (hμx : μ x ≠ 0) :
    errorProb μ true x + errorProb μ false x = 1 := by
  unfold errorProb
  have hsum := Convergence.condProb_sum_eq_one μ x hμx
  linarith

/-- Helper: When predictions disagree and μ x ≠ 0, error sum = 1 -/
lemma error_sum_eq_one_when_disagree (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (hμx : μ x ≠ 0) (h_disagree : universalPrediction ξ x ≠ optimalPrediction μ x) :
    optimalErrorProb μ x + universalErrorProb μ ξ x = 1 := by
  unfold optimalErrorProb universalErrorProb
  -- When they disagree, one is true and one is false
  cases h1 : optimalPrediction μ x with
  | false =>
    cases h2 : universalPrediction ξ x with
    | false =>
      rw [h1, h2] at h_disagree
      exact absurd rfl h_disagree
    | true =>
      -- Goal: errorProb μ false x + errorProb μ true x = 1
      have := errorProb_true_add_false_eq_one μ x hμx
      linarith
  | true =>
    cases h2 : universalPrediction ξ x with
    | false =>
      -- Goal: errorProb μ true x + errorProb μ false x = 1
      have := errorProb_true_add_false_eq_one μ x hμx
      linarith
    | true =>
      rw [h1, h2] at h_disagree
      exact absurd rfl h_disagree

/-- Helper: Error difference when predictions disagree -/
lemma error_diff_eq_abs_two_p_minus_one (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (hμx : μ x ≠ 0) (h_disagree : universalPrediction ξ x ≠ optimalPrediction μ x) :
    |universalErrorProb μ ξ x - optimalErrorProb μ x| =
    |2 * FiniteHorizon.condProb μ.toSemimeasure x true - 1| := by
  set p := FiniteHorizon.condProb μ.toSemimeasure x true
  have hsum := Convergence.condProb_sum_eq_one μ x hμx
  have hpf : FiniteHorizon.condProb μ.toSemimeasure x false = 1 - p := by linarith
  -- When predictions disagree, exactly one predicts true and one predicts false
  -- This means the error probabilities are errorProb μ true x and errorProb μ false x
  -- Their sum is 1, and their difference is |2p - 1|
  unfold universalErrorProb optimalErrorProb errorProb
  cases h1 : optimalPrediction μ x with
  | false =>
    cases h2 : universalPrediction ξ x with
    | false =>
      rw [h1, h2] at h_disagree
      exact absurd rfl h_disagree
    | true =>
      -- optimal predicts false, universal predicts true
      -- universalErrorProb = 1 - condProb true = 1 - p
      -- optimalErrorProb = 1 - condProb false = 1 - (1 - p) = p
      -- difference = (1 - p) - p = 1 - 2p
      rw [hpf]
      have hdiff : (1 - p) - (1 - (1 - p)) = 1 - 2 * p := by ring
      rw [hdiff]
      exact abs_sub_comm (1 : ℝ) (2 * p)
  | true =>
    cases h2 : universalPrediction ξ x with
    | false =>
      -- optimal predicts true, universal predicts false
      -- universalErrorProb = 1 - condProb false = 1 - (1 - p) = p
      -- optimalErrorProb = 1 - condProb true = 1 - p
      -- difference = p - (1 - p) = 2p - 1
      rw [hpf]
      have hdiff : (1 - (1 - p)) - (1 - p) = 2 * p - 1 := by ring
      rw [hdiff]
    | true =>
      rw [h1, h2] at h_disagree
      exact absurd rfl h_disagree

/-- Helper: When predictions disagree, sqDistStep ≥ (2p-1)²/2.
    This is the key connection between prediction error and squared distance.

    When μ predicts true (p ≥ 1/2) and ξ predicts false (q < 1/2):
    |p - q| = (p - q) ≥ (p - 1/2), so sqDistStep = 2(p-q)² ≥ 2(p-1/2)² = (2p-1)²/2.

    Similarly for the symmetric case. -/
lemma sqDistStep_ge_error_diff_sq (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (h_disagree : universalPrediction ξ x ≠ optimalPrediction μ x) :
    sqDistStep μ ξ x ≥ (2 * FiniteHorizon.condProb μ.toSemimeasure x true - 1) ^ 2 / 2 := by
  unfold sqDistStep
  rw [Entropy.sqDistBinary_eq_two_mul]
  -- sqDistStep = 2 * (p - q)² where p = condProb μ, q = condProb ξ
  set p := FiniteHorizon.condProb μ.toSemimeasure x true
  set q := FiniteHorizon.condProb ξ x true
  -- We need: 2 * (p - q)² ≥ (2p - 1)² / 2
  -- When predictions disagree: one of p,q ≥ 1/2 and the other < 1/2
  -- So |p - q| ≥ |p - 1/2|
  have key : |p - q| ≥ |p - 1/2| := by
    -- Analyze based on actual Bool predictions
    cases h1 : optimalPrediction μ x with
    | false =>
      cases h2 : universalPrediction ξ x with
      | false =>
        rw [h1, h2] at h_disagree
        exact absurd rfl h_disagree
      | true =>
        -- μ predicts false (p < 1/2), ξ predicts true (q ≥ 1/2)
        unfold optimalPrediction at h1
        unfold universalPrediction at h2
        simp only [decide_eq_false_iff_not, not_le] at h1
        simp only [decide_eq_true_iff] at h2
        have h1' : p < 1/2 := h1
        have h2' : q ≥ 1/2 := h2
        have hpq_pos : q - p > 0 := by linarith
        have hphalf_pos : 1/2 - p > 0 := by linarith
        rw [abs_sub_comm p q, abs_of_pos hpq_pos]
        rw [abs_sub_comm p (1/2 : ℝ), abs_of_pos hphalf_pos]
        linarith
    | true =>
      cases h2 : universalPrediction ξ x with
      | false =>
        -- μ predicts true (p ≥ 1/2), ξ predicts false (q < 1/2)
        unfold optimalPrediction at h1
        unfold universalPrediction at h2
        simp only [decide_eq_true_iff] at h1
        simp only [decide_eq_false_iff_not, not_le] at h2
        have h1' : p ≥ 1/2 := h1
        have h2' : q < 1/2 := h2
        have hpq_pos : p - q > 0 := by linarith
        have hphalf_nonneg : p - 1/2 ≥ 0 := by linarith
        rw [abs_of_pos hpq_pos, abs_of_nonneg hphalf_nonneg]
        linarith
      | true =>
        rw [h1, h2] at h_disagree
        exact absurd rfl h_disagree
  -- Now from |p - q| ≥ |p - 1/2|, get (p - q)² ≥ (p - 1/2)²
  -- |a| ≥ |b| implies a² = |a|² ≥ |b|² = b²
  have hsq : (p - q) ^ 2 ≥ (p - 1/2) ^ 2 := by
    have h1 : (p - q) ^ 2 = |p - q| ^ 2 := (sq_abs (p - q)).symm
    have h2 : (p - 1/2) ^ 2 = |p - 1/2| ^ 2 := (sq_abs (p - 1/2)).symm
    rw [h1, h2]
    apply sq_le_sq'
    · calc -|p - q| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
        _ ≤ |p - 1/2| := abs_nonneg _
    · exact key
  -- And 2(p-q)² ≥ 2(p-1/2)² = (2p-1)²/2
  have h2pq : 2 * (p - q) ^ 2 ≥ 2 * (p - 1/2) ^ 2 := by linarith
  have hrw : 2 * (p - 1/2) ^ 2 = (2 * p - 1) ^ 2 / 2 := by ring
  linarith

/-- Per-step error difference bound.
    e^ξ_t - e^μ_t ≤ A(e^μ_t + e^ξ_t) + B·s_t for suitable A, B > 0.

    From the proof: 2AB ≥ 1 is required.

    **Proof (Hutter 3.37-3.42)**:
    - When predictions agree: difference = 0 ≤ RHS
    - When predictions disagree: error sum = 1, and sqDistStep provides
      the leverage via AM-GM (am_gm_error_bound lemma) -/
theorem errorDiff_le_sqDist (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (A B : ℝ) (hAB : 2 * A * B ≥ 1) (hA : A > 0) (hB : B > 0) :
    universalErrorProb μ ξ x - optimalErrorProb μ x ≤
    A * (optimalErrorProb μ x + universalErrorProb μ ξ x) + B * sqDistStep μ ξ x := by
  -- First, establish that the RHS is non-negative regardless of predictions
  have hRHS_nonneg : 0 ≤ A * (optimalErrorProb μ x + universalErrorProb μ ξ x) + B * sqDistStep μ ξ x := by
    apply add_nonneg
    · apply mul_nonneg (le_of_lt hA)
      apply add_nonneg <;> exact errorProb_nonneg μ _ x
    · exact mul_nonneg (le_of_lt hB) (sqDistStep_nonneg μ ξ x)
  -- Case split: do predictions agree?
  by_cases h_agree : universalPrediction ξ x = optimalPrediction μ x
  · -- Predictions agree: difference = 0, RHS is non-negative
    have heq := error_eq_when_predictions_agree μ ξ x h_agree
    rw [heq]
    have hLHS : optimalErrorProb μ x - optimalErrorProb μ x = 0 := sub_self _
    rw [hLHS]
    -- Need to show 0 ≤ A * (optimalErrorProb + optimalErrorProb) + B * sqDistStep
    apply add_nonneg
    · apply mul_nonneg (le_of_lt hA)
      apply add_nonneg <;> exact errorProb_nonneg μ _ x
    · exact mul_nonneg (le_of_lt hB) (sqDistStep_nonneg μ ξ x)
  · -- Predictions disagree: need the AM-GM argument
    -- Handle μ x = 0 case separately
    by_cases hμx : μ x = 0
    · -- When μ x = 0, both condProb values are 0, so both error probs are 1
      -- Hence universalErrorProb = optimalErrorProb = 1, difference = 0
      have hpt0 : FiniteHorizon.condProb μ.toSemimeasure x true = 0 := by
        simp only [FiniteHorizon.condProb, conditionalENN]; simp [hμx]
      have hpf0 : FiniteHorizon.condProb μ.toSemimeasure x false = 0 := by
        simp only [FiniteHorizon.condProb, conditionalENN]; simp [hμx]
      have h_eμ : optimalErrorProb μ x = 1 := by
        unfold optimalErrorProb optimalPrediction errorProb
        have : (decide (FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1/2)) = false := by
          simp only [decide_eq_false_iff_not, not_le]; simp [hpt0]
        rw [this, hpf0]; norm_num
      have h_eξ : universalErrorProb μ ξ x = 1 := by
        unfold universalErrorProb errorProb
        cases huniv : universalPrediction ξ x with
        | false => rw [hpf0]; norm_num
        | true => rw [hpt0]; norm_num
      rw [h_eμ, h_eξ, sub_self]
      -- Goal: 0 ≤ A * (1 + 1) + B * sqDistStep μ ξ x
      apply add_nonneg
      · apply mul_nonneg (le_of_lt hA)
        linarith
      · exact mul_nonneg (le_of_lt hB) (sqDistStep_nonneg μ ξ x)
    · -- When μ x ≠ 0, use the AM-GM argument
      -- Key facts:
      -- 1. error_sum = 1 (from error_sum_eq_one_when_disagree)
      -- 2. error_diff = |2p - 1| (from error_diff_eq_abs_two_p_minus_one)
      -- 3. sqDistStep ≥ (2p-1)²/2 (from sqDistStep_ge_error_diff_sq)
      have h_sum : optimalErrorProb μ x + universalErrorProb μ ξ x = 1 :=
        error_sum_eq_one_when_disagree μ ξ x hμx h_agree
      -- Get the error difference bound
      set p := FiniteHorizon.condProb μ.toSemimeasure x true
      set u := universalErrorProb μ ξ x - optimalErrorProb μ x
      -- From error_sum = 1, we have universalErrorProb = 1 - optimalErrorProb
      -- So u = (1 - optimalErrorProb) - optimalErrorProb = 1 - 2*optimalErrorProb
      -- And |u| = |2p - 1| (this comes from the error_diff lemma)
      -- First, show u ≤ 1 and |u| ≤ 1
      have hu_le_1 : u ≤ 1 := by
        have he1 : universalErrorProb μ ξ x ≤ 1 := by
          unfold universalErrorProb errorProb
          have hle := condProb_le_one' μ.toSemimeasure x (universalPrediction ξ x)
          have hge : 0 ≤ FiniteHorizon.condProb μ.toSemimeasure x (universalPrediction ξ x) := by
            unfold FiniteHorizon.condProb conditionalENN
            exact ENNReal.toReal_nonneg
          linarith
        have he2 : 0 ≤ optimalErrorProb μ x := errorProb_nonneg μ _ x
        linarith
      -- Show u ≥ 0 when predictions disagree in the "bad" direction
      -- Actually u could be positive or negative depending on which predictor is worse
      -- But we only need to bound u from above, so if u ≤ 0, we're done
      by_cases hu_neg : u ≤ 0
      · calc u ≤ 0 := hu_neg
          _ ≤ A * (optimalErrorProb μ x + universalErrorProb μ ξ x) + B * sqDistStep μ ξ x :=
            hRHS_nonneg
      · -- u > 0: need the full argument
        push_neg at hu_neg
        -- u > 0 and error_sum = 1, so u = |2p - 1| by the error_diff lemma
        have hu_abs : u = |2 * p - 1| := by
          -- From the error_diff_eq_abs_two_p_minus_one lemma, |u| = |2p - 1|
          -- Since u > 0, u = |u|
          have h_abs := error_diff_eq_abs_two_p_minus_one μ ξ x hμx h_agree
          have hu_pos : 0 < u := hu_neg
          rw [abs_of_pos hu_pos] at h_abs
          exact h_abs
        -- u = |2p - 1|, which is in [0, 1]
        have hu_01 : 0 ≤ |2 * p - 1| ∧ |2 * p - 1| ≤ 1 := by
          constructor
          · exact abs_nonneg _
          · have hp_le_1 := condProb_le_one' μ.toSemimeasure x true
            have hp_ge_0 : 0 ≤ p := by
              show 0 ≤ FiniteHorizon.condProb μ.toSemimeasure x true
              unfold FiniteHorizon.condProb conditionalENN
              exact ENNReal.toReal_nonneg
            rw [abs_le]
            constructor <;> linarith
        rw [hu_abs]
        -- Now use am_gm_error_bound with the error value
        have hsqDist_ge := sqDistStep_ge_error_diff_sq μ ξ x h_agree
        -- sqDistStep ≥ (2p - 1)² / 2 = |2p - 1|² / 2
        -- Since (a)² = |a|², we have (2p - 1)² / 2 = |2p - 1|² / 2
        have hsqDist_ge' : sqDistStep μ ξ x ≥ |2 * p - 1| ^ 2 / 2 := by
          have heq : (2 * p - 1) ^ 2 = |2 * p - 1| ^ 2 := (sq_abs _).symm
          calc sqDistStep μ ξ x ≥ (2 * p - 1) ^ 2 / 2 := hsqDist_ge
            _ = |2 * p - 1| ^ 2 / 2 := by rw [heq]
        -- By am_gm_error_bound: |2p-1| ≤ A + B * |2p-1|² / 2
        have ham_gm := am_gm_error_bound hAB hA hB hu_01.1 hu_01.2
        -- ham_gm has form |2p-1| ≤ A + B * |2p-1|² / 2, need to add parentheses
        have hAB_form : |2 * p - 1| ≤ A + B * (|2 * p - 1| ^ 2 / 2) := by
          have heq : B * |2 * p - 1| ^ 2 / 2 = B * (|2 * p - 1| ^ 2 / 2) := by ring
          rw [← heq]
          exact ham_gm
        -- Since sqDistStep ≥ |2p-1|²/2, we have B * sqDistStep ≥ B * |2p-1|²/2
        have hBsq : B * sqDistStep μ ξ x ≥ B * (|2 * p - 1| ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left hsqDist_ge' (le_of_lt hB)
        -- Combine with error_sum = 1: A * error_sum = A
        calc |2 * p - 1|
            ≤ A + B * (|2 * p - 1| ^ 2 / 2) := hAB_form
          _ ≤ A + B * sqDistStep μ ξ x := by linarith
          _ = A * 1 + B * sqDistStep μ ξ x := by ring
          _ = A * (optimalErrorProb μ x + universalErrorProb μ ξ x) + B * sqDistStep μ ξ x := by
              rw [h_sum]

/-- Helper: For any A, B > 0 with 2AB ≥ 1, the aggregated error bound holds.
    E^ξ - E^μ ≤ A*(E^μ + E^ξ) + B*S_n

    **Proof sketch**: Sum the per-step bounds from `errorDiff_le_sqDist` using
    linearity of expectation. The algebraic manipulation uses:
    - Finset.sum_le_sum to aggregate pointwise bounds
    - Finset.sum_add_distrib and Finset.mul_sum for distribution -/
lemma error_bound_AB (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ)
    (A B : ℝ) (hAB : 2 * A * B ≥ 1) (hA : A > 0) (hB : B > 0) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
    A * (expectedOptimalErrors μ n + expectedUniversalErrors μ ξ n) +
    B * totalSqDist μ ξ n := by
  -- The proof aggregates the per-step bounds from errorDiff_le_sqDist
  -- using linearity of expectation and sum distribution.
  unfold expectedUniversalErrors expectedOptimalErrors totalSqDist
  -- E^ξ - E^μ = Σ_k E_μ[e^ξ_k - e^μ_k] (difference of sums = sum of differences)
  rw [← Finset.sum_sub_distrib]
  -- For the RHS, distribute A and B into the sums using calc
  calc ∑ k ∈ Finset.range n, (expectPrefix μ k (universalErrorProb μ ξ) -
                               expectPrefix μ k (optimalErrorProb μ))
      ≤ ∑ k ∈ Finset.range n, (A * expectPrefix μ k (optimalErrorProb μ) +
                               A * expectPrefix μ k (universalErrorProb μ ξ) +
                               B * expectPrefix μ k (sqDistStep μ ξ)) := by
        apply Finset.sum_le_sum
        intro k _hk
        unfold expectPrefix
        rw [← Finset.sum_sub_distrib]
        have hrhs2 : A * ∑ x : Fin k → Bool, (prefixPMF μ k x).toReal * optimalErrorProb μ (List.ofFn x) +
                     A * ∑ x : Fin k → Bool, (prefixPMF μ k x).toReal * universalErrorProb μ ξ (List.ofFn x) +
                     B * ∑ x : Fin k → Bool, (prefixPMF μ k x).toReal * sqDistStep μ ξ (List.ofFn x) =
                     ∑ x : Fin k → Bool, (A * ((prefixPMF μ k x).toReal * optimalErrorProb μ (List.ofFn x)) +
                                          A * ((prefixPMF μ k x).toReal * universalErrorProb μ ξ (List.ofFn x)) +
                                          B * ((prefixPMF μ k x).toReal * sqDistStep μ ξ (List.ofFn x))) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        rw [hrhs2]
        apply Finset.sum_le_sum
        intro f _hf
        have hstep := errorDiff_le_sqDist μ ξ (List.ofFn f) A B hAB hA hB
        have hμ_nonneg : 0 ≤ (prefixPMF μ k f).toReal := ENNReal.toReal_nonneg
        calc (prefixPMF μ k f).toReal * universalErrorProb μ ξ (List.ofFn f) -
               (prefixPMF μ k f).toReal * optimalErrorProb μ (List.ofFn f)
            = (prefixPMF μ k f).toReal * (universalErrorProb μ ξ (List.ofFn f) - optimalErrorProb μ (List.ofFn f)) := by ring
          _ ≤ (prefixPMF μ k f).toReal *
              (A * (optimalErrorProb μ (List.ofFn f) + universalErrorProb μ ξ (List.ofFn f)) +
               B * sqDistStep μ ξ (List.ofFn f)) := by
              apply mul_le_mul_of_nonneg_left hstep hμ_nonneg
          _ = A * ((prefixPMF μ k f).toReal * optimalErrorProb μ (List.ofFn f)) +
              A * ((prefixPMF μ k f).toReal * universalErrorProb μ ξ (List.ofFn f)) +
              B * ((prefixPMF μ k f).toReal * sqDistStep μ ξ (List.ofFn f)) := by ring
    _ = A * (∑ k ∈ Finset.range n, expectPrefix μ k (optimalErrorProb μ) +
             ∑ k ∈ Finset.range n, expectPrefix μ k (universalErrorProb μ ξ)) +
        B * ∑ k ∈ Finset.range n, expectPrefix μ k (sqDistStep μ ξ) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- Helper: Expected errors are non-negative -/
lemma expectedOptimalErrors_nonneg (μ : PrefixMeasure) (n : ℕ) :
    0 ≤ expectedOptimalErrors μ n := by
  unfold expectedOptimalErrors expectPrefix
  apply Finset.sum_nonneg; intro k _; apply Finset.sum_nonneg; intro f _
  apply mul_nonneg ENNReal.toReal_nonneg; exact errorProb_nonneg μ _ _

lemma expectedUniversalErrors_nonneg (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    0 ≤ expectedUniversalErrors μ ξ n := by
  unfold expectedUniversalErrors expectPrefix
  apply Finset.sum_nonneg; intro k _; apply Finset.sum_nonneg; intro f _
  apply mul_nonneg ENNReal.toReal_nonneg; exact errorProb_nonneg μ _ _

lemma totalSqDist_nonneg (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    0 ≤ totalSqDist μ ξ n := by
  unfold totalSqDist expectPrefix
  apply Finset.sum_nonneg; intro k _; apply Finset.sum_nonneg; intro f _
  apply mul_nonneg ENNReal.toReal_nonneg; exact sqDistStep_nonneg μ ξ _

/-- Main bound from Theorem 3.36 (first form):
    E^ξ - E^μ ≤ √(2(E^μ + E^ξ)·S_n)

    Proof: Apply error_bound_AB with optimal A, B:
    - A = √(S_n / (2*(E^μ + E^ξ))), B = √((E^μ + E^ξ) / (2*S_n))
    - Then 2AB = 1 and A*X + B*S = √(2*X*S) where X = E^μ + E^ξ

    **Note**: This theorem aggregates the per-step error bounds from `errorDiff_le_sqDist`.
    The algebraic optimization proof is straightforward but tedious in Lean. -/
theorem error_bound_sqrt (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
    Real.sqrt (2 * (expectedOptimalErrors μ n + expectedUniversalErrors μ ξ n) *
      totalSqDist μ ξ n) := by
  set X := expectedOptimalErrors μ n + expectedUniversalErrors μ ξ n with hX_def
  set S := totalSqDist μ ξ n with hS_def
  have hEμ_nonneg := expectedOptimalErrors_nonneg μ n
  have hEξ_nonneg := expectedUniversalErrors_nonneg μ ξ n
  have hS_nonneg := totalSqDist_nonneg μ ξ n
  have hX_nonneg : 0 ≤ X := add_nonneg hEμ_nonneg hEξ_nonneg
  -- Edge cases: X = 0 or S = 0
  by_cases hX : X = 0
  · -- X = 0 means both errors are 0, so difference is 0
    have hEμ : expectedOptimalErrors μ n = 0 := by linarith
    have hEξ : expectedUniversalErrors μ ξ n = 0 := by linarith
    simp only [hEμ, hEξ, sub_self]
    exact Real.sqrt_nonneg _
  by_cases hS : S = 0
  · -- S = 0, so √(2*X*0) = 0. Need to show difference ≤ 0.
    simp only [hS, mul_zero, Real.sqrt_zero]
    -- When S = 0, sqDistStep = 0 everywhere, so predictions agree.
    -- By limit argument with error_bound_AB: for any ε > 0, diff ≤ ε*X + 0 → diff ≤ 0.
    have h_ge : expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≥ 0 := by
      linarith [expectedOptimalErrors_le_universal μ ξ n]
    have hX_pos : X > 0 := by
      rcases lt_or_eq_of_le hX_nonneg with hlt | heq
      · exact hlt
      · exact absurd heq.symm hX
    -- For any ε > 0, error_bound_AB gives diff ≤ ε*X + (1/(2ε))*0 = ε*X
    -- As ε → 0, diff ≤ 0
    have h_le : expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤ 0 := by
      by_contra h_neg
      push_neg at h_neg
      set δ := expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n
      have hδ_pos : δ > 0 := h_neg
      have hε : δ / (2 * X) > 0 := div_pos hδ_pos (mul_pos (by norm_num : (0:ℝ) < 2) hX_pos)
      have hB : 1 / (2 * (δ / (2 * X))) > 0 := by
        rw [one_div]; apply inv_pos_of_pos; apply mul_pos (by norm_num : (0:ℝ) < 2) hε
      have hAB : 2 * (δ / (2 * X)) * (1 / (2 * (δ / (2 * X)))) = 1 := by field_simp
      have hAB_ge : 2 * (δ / (2 * X)) * (1 / (2 * (δ / (2 * X)))) ≥ 1 := le_of_eq hAB.symm
      have hbound := error_bound_AB μ ξ n (δ / (2 * X)) (1 / (2 * (δ / (2 * X)))) hAB_ge hε hB
      simp only [hS_def.symm, hS, mul_zero, add_zero] at hbound
      have h_calc : (δ / (2 * X)) * X = δ / 2 := by field_simp
      linarith [hbound, h_calc]
    linarith
  · -- Main case: X > 0 and S > 0
    have hX_pos : 0 < X := lt_of_le_of_ne hX_nonneg (Ne.symm hX)
    have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS)
    -- Define optimal A = √(S/(2X)), B = √(X/(2S))
    set A := Real.sqrt (S / (2 * X)) with hA_def
    set B := Real.sqrt (X / (2 * S)) with hB_def
    -- Show A > 0 and B > 0
    have hA_pos : A > 0 := by
      rw [hA_def]
      exact Real.sqrt_pos.mpr (div_pos hS_pos (mul_pos (by norm_num : (0:ℝ) < 2) hX_pos))
    have hB_pos : B > 0 := by
      rw [hB_def]
      exact Real.sqrt_pos.mpr (div_pos hX_pos (mul_pos (by norm_num : (0:ℝ) < 2) hS_pos))
    -- Show 2AB = 1
    have hS2X_nonneg : 0 ≤ S / (2 * X) := div_nonneg (le_of_lt hS_pos) (by linarith)
    have hX2S_nonneg : 0 ≤ X / (2 * S) := div_nonneg (le_of_lt hX_pos) (by linarith)
    have h2AB : 2 * A * B = 1 := by
      rw [hA_def, hB_def]
      -- 2 * √(S/(2X)) * √(X/(2S)) = 2 * √((S/(2X)) * (X/(2S))) = 2 * √(1/4) = 1
      have hprod : S / (2 * X) * (X / (2 * S)) = 1 / 4 := by field_simp; ring
      have hsqrt14 : Real.sqrt (1 / 4) = 1 / 2 := by
        rw [show (1 : ℝ) / 4 = (1/2)^2 by norm_num]
        exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)
      have hsqrt_prod : Real.sqrt (S / (2 * X)) * Real.sqrt (X / (2 * S)) = 1 / 2 := by
        rw [← Real.sqrt_mul hS2X_nonneg, hprod, hsqrt14]
      calc 2 * Real.sqrt (S / (2 * X)) * Real.sqrt (X / (2 * S))
          = 2 * (Real.sqrt (S / (2 * X)) * Real.sqrt (X / (2 * S))) := by ring
        _ = 2 * (1 / 2) := by rw [hsqrt_prod]
        _ = 1 := by ring
    have h2AB_ge : 2 * A * B ≥ 1 := le_of_eq h2AB.symm
    -- Apply error_bound_AB
    have hbound := error_bound_AB μ ξ n A B h2AB_ge hA_pos hB_pos
    -- Now show A*X + B*S = √(2*X*S)
    have hAX_BS_eq : A * X + B * S = Real.sqrt (2 * X * S) := by
      rw [hA_def, hB_def]
      -- Direct approach: prove (A*X + B*S)² = 2XS, then use sqrt properties
      have h2XS_nonneg : 0 ≤ 2 * X * S := mul_nonneg (mul_nonneg (by norm_num) hX_nonneg) hS_nonneg
      have hlhs_nonneg : 0 ≤ Real.sqrt (S / (2 * X)) * X + Real.sqrt (X / (2 * S)) * S := by
        apply add_nonneg
        · exact mul_nonneg (Real.sqrt_nonneg _) hX_nonneg
        · exact mul_nonneg (Real.sqrt_nonneg _) hS_nonneg
      -- Use: √x = y ↔ x = y^2 when 0 ≤ x and 0 ≤ y
      symm
      rw [Real.sqrt_eq_iff_eq_sq h2XS_nonneg hlhs_nonneg]
      -- Show (√(S/(2X))*X + √(X/(2S))*S)² = 2XS
      have hsqS2X : (Real.sqrt (S / (2 * X))) ^ 2 = S / (2 * X) := Real.sq_sqrt hS2X_nonneg
      have hsqX2S : (Real.sqrt (X / (2 * S))) ^ 2 = X / (2 * S) := Real.sq_sqrt hX2S_nonneg
      -- (√a * b + √c * d)² = a*b² + c*d² + 2*√a*b*√c*d = a*b² + c*d² + 2*√(ac)*bd
      -- = SX/2 + XS/2 + 2*X*S*(1/2) = XS + XS = 2XS ✓
      have hprod14 : S / (2 * X) * (X / (2 * S)) = 1 / 4 := by field_simp; ring
      have hsqrt14 : Real.sqrt (1 / 4) = 1 / 2 := by
        rw [show (1 : ℝ) / 4 = (1/2)^2 by norm_num]
        exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)
      have hsqrt_prod : Real.sqrt (S / (2 * X)) * Real.sqrt (X / (2 * S)) = 1 / 2 := by
        rw [← Real.sqrt_mul hS2X_nonneg, hprod14, hsqrt14]
      have hX_ne : X ≠ 0 := ne_of_gt hX_pos
      have hS_ne : S ≠ 0 := ne_of_gt hS_pos
      -- Goal after rw is: 2 * X * S = (√(S/(2X))*X + √(X/(2S))*S)^2
      -- Start from the expanded form and work backwards
      have hexpand : (Real.sqrt (S / (2 * X)) * X + Real.sqrt (X / (2 * S)) * S) ^ 2 =
          (Real.sqrt (S / (2 * X))) ^ 2 * X ^ 2 +
          (Real.sqrt (X / (2 * S))) ^ 2 * S ^ 2 +
          2 * (Real.sqrt (S / (2 * X)) * X) * (Real.sqrt (X / (2 * S)) * S) := by ring
      have hsimp1 : (Real.sqrt (S / (2 * X))) ^ 2 * X ^ 2 = S * X / 2 := by
        rw [hsqS2X]; field_simp
      have hsimp2 : (Real.sqrt (X / (2 * S))) ^ 2 * S ^ 2 = X * S / 2 := by
        rw [hsqX2S]; field_simp
      have hsimp3 : 2 * (Real.sqrt (S / (2 * X)) * X) * (Real.sqrt (X / (2 * S)) * S) =
          2 * (Real.sqrt (S / (2 * X)) * Real.sqrt (X / (2 * S))) * X * S := by ring
      calc 2 * X * S
          = S * X / 2 + X * S / 2 + X * S := by ring
        _ = (Real.sqrt (S / (2 * X))) ^ 2 * X ^ 2 +
            (Real.sqrt (X / (2 * S))) ^ 2 * S ^ 2 +
            2 * (1 / 2) * X * S := by rw [hsimp1, hsimp2]; ring
        _ = (Real.sqrt (S / (2 * X))) ^ 2 * X ^ 2 +
            (Real.sqrt (X / (2 * S))) ^ 2 * S ^ 2 +
            2 * (Real.sqrt (S / (2 * X)) * Real.sqrt (X / (2 * S))) * X * S := by rw [hsqrt_prod]
        _ = (Real.sqrt (S / (2 * X))) ^ 2 * X ^ 2 +
            (Real.sqrt (X / (2 * S))) ^ 2 * S ^ 2 +
            2 * (Real.sqrt (S / (2 * X)) * X) * (Real.sqrt (X / (2 * S)) * S) := by rw [hsimp3]
        _ = (Real.sqrt (S / (2 * X)) * X + Real.sqrt (X / (2 * S)) * S) ^ 2 := by rw [hexpand]
    -- From error_bound_AB: diff ≤ A*(X) + B*S = A*X + B*S
    -- Since expectedOptimalErrors + expectedUniversalErrors = X
    calc expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n
        ≤ A * (expectedOptimalErrors μ n + expectedUniversalErrors μ ξ n) +
          B * totalSqDist μ ξ n := hbound
      _ = A * X + B * S := by rfl
      _ = Real.sqrt (2 * X * S) := hAX_BS_eq
      _ = Real.sqrt (2 * (expectedOptimalErrors μ n + expectedUniversalErrors μ ξ n) *
            totalSqDist μ ξ n) := by rfl

/-- Main bound from Theorem 3.36 (second form):
    E^ξ - E^μ ≤ √(4·E^μ·S_n) + 2·S_n

    Derived from error_bound_sqrt by solving for E^ξ - E^μ:
    1. From error_bound_sqrt: E^ξ - E^μ ≤ √(2(E^μ + E^ξ)·S_n)
    2. Let δ = E^ξ - E^μ. Then δ ≤ √(2(2E^μ + δ)·S_n)
    3. Square: δ² ≤ 4E^μ·S_n + 2δ·S_n
    4. Rearrange: δ² - 2δ·S_n - 4E^μ·S_n ≤ 0
    5. By quadratic formula: δ ≤ S_n + √(S_n² + 4E^μ·S_n)
    6. Using √(a+b) ≤ √a + √b: √(S_n² + 4E^μ·S_n) ≤ S_n + √(4E^μ·S_n)
    7. Therefore: δ ≤ 2·S_n + √(4E^μ·S_n)

    **Note**: The coefficient 2 on S_n is tight for this derivation method.
    Hutter (2005) Theorem 3.36 claims coefficient 1, which may require
    a different approach or additional assumptions. -/
theorem error_bound_main (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
    Real.sqrt (4 * expectedOptimalErrors μ n * totalSqDist μ ξ n) +
    2 * totalSqDist μ ξ n := by
  set δ := expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n with hδ_def
  set E := expectedOptimalErrors μ n with hE_def
  set S := totalSqDist μ ξ n with hS_def
  have hE_nonneg := expectedOptimalErrors_nonneg μ n
  have hS_nonneg := totalSqDist_nonneg μ ξ n
  -- From error_bound_sqrt: δ ≤ √(2(E + E^ξ)S) = √(2(2E + δ)S)
  have hsqrt := error_bound_sqrt μ ξ n
  rw [← hδ_def, ← hE_def, ← hS_def] at hsqrt
  have hEξ : expectedUniversalErrors μ ξ n = E + δ := by
    rw [hδ_def, hE_def]; ring
  rw [hEξ] at hsqrt
  -- hsqrt: δ ≤ √(2(E + (E + δ))S) = √(2(2E + δ)S)
  have hsqrt' : δ ≤ Real.sqrt (2 * (2 * E + δ) * S) := by
    convert hsqrt using 2; ring
  -- Edge case: S = 0
  by_cases hS0 : S = 0
  · -- When S = 0, from error_bound_sqrt we have δ ≤ √0 = 0
    have h : δ ≤ Real.sqrt 0 := by
      calc δ ≤ Real.sqrt (2 * (2 * E + δ) * S) := hsqrt'
        _ = Real.sqrt (2 * (2 * E + δ) * 0) := by rw [hS0]
        _ = Real.sqrt 0 := by ring_nf
    simp only [Real.sqrt_zero] at h
    simp only [hS0, mul_zero, Real.sqrt_zero, add_zero]
    exact h
  have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS0)
  -- Edge case: δ ≤ 0 (trivial)
  by_cases hδ_nonpos : δ ≤ 0
  · calc δ ≤ 0 := hδ_nonpos
      _ ≤ Real.sqrt (4 * E * S) + 2 * S := by
          apply add_nonneg (Real.sqrt_nonneg _)
          linarith
  push_neg at hδ_nonpos
  have hδ_pos : 0 < δ := hδ_nonpos
  -- Square the inequality: δ² ≤ 2(2E + δ)S = 4ES + 2δS
  have h2E_δ_nonneg : 0 ≤ 2 * E + δ := by linarith
  have hsqrt_sq : δ ^ 2 ≤ 2 * (2 * E + δ) * S := by
    have hrhs_nonneg : 0 ≤ 2 * (2 * E + δ) * S := by positivity
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
    calc δ ^ 2 = δ * δ := by ring
      _ ≤ Real.sqrt (2 * (2 * E + δ) * S) * Real.sqrt (2 * (2 * E + δ) * S) := by
          apply mul_le_mul hsqrt' hsqrt' hδ_nonneg (Real.sqrt_nonneg _)
      _ = (Real.sqrt (2 * (2 * E + δ) * S)) ^ 2 := by ring
      _ = 2 * (2 * E + δ) * S := Real.sq_sqrt hrhs_nonneg
  -- Expand: δ² ≤ 4ES + 2δS
  have hquad : δ ^ 2 - 2 * δ * S - 4 * E * S ≤ 0 := by linarith [hsqrt_sq]
  -- Use quadratic bound: δ ≤ S + √(S² + 4ES)
  -- Define the discriminant and root
  have hdisc_nonneg : 0 ≤ S ^ 2 + 4 * E * S := by positivity
  have hroot := S + Real.sqrt (S ^ 2 + 4 * E * S)
  -- Show δ ≤ hroot via the quadratic formula argument
  -- For quadratic aδ² + bδ + c ≤ 0 with a > 0, δ ≤ (-b + √(b² - 4ac))/(2a)
  -- Here: δ² - 2Sδ - 4ES ≤ 0, so a=1, b=-2S, c=-4ES
  -- Root = (2S + √(4S² + 16ES))/2 = S + √(S² + 4ES)
  have hδ_le_root : δ ≤ S + Real.sqrt (S ^ 2 + 4 * E * S) := by
    -- Quadratic: (δ - S)² ≤ S² + 4ES
    have hcomplete : (δ - S) ^ 2 ≤ S ^ 2 + 4 * E * S := by linarith [hquad]
    -- Use abs_le_of_sq_le_sq: |a| ≤ b given a² ≤ b² and 0 ≤ b
    have habs : |δ - S| ≤ Real.sqrt (S ^ 2 + 4 * E * S) := by
      apply abs_le_of_sq_le_sq _ (Real.sqrt_nonneg _)
      rw [Real.sq_sqrt hdisc_nonneg]
      exact hcomplete
    rw [abs_le] at habs
    linarith [habs.2]
  -- Now bound √(S² + 4ES) ≤ S + √(4ES) using √(a+b) ≤ √a + √b
  -- Proof: (√a + √b)² = a + b + 2√(ab) ≥ a + b
  have h4ES_nonneg : 0 ≤ 4 * E * S := by positivity
  have hS2_nonneg : 0 ≤ S ^ 2 := sq_nonneg _
  have hsqrt_triangle : Real.sqrt (S ^ 2 + 4 * E * S) ≤ S + Real.sqrt (4 * E * S) := by
    have hS_nonneg' : 0 ≤ S := le_of_lt hS_pos
    have hrhs_nonneg : 0 ≤ S + Real.sqrt (4 * E * S) := by
      apply add_nonneg hS_nonneg' (Real.sqrt_nonneg _)
    -- Use: √x ≤ y ↔ 0 ≤ y ∧ x ≤ y²
    rw [Real.sqrt_le_iff]
    constructor
    · exact hrhs_nonneg
    -- Need: S² + 4ES ≤ (S + √(4ES))²
    -- (S + √(4ES))² = S² + 2S√(4ES) + (√(4ES))² = S² + 2S√(4ES) + 4ES
    have hsq4ES : Real.sqrt (4 * E * S) ^ 2 = 4 * E * S := Real.sq_sqrt h4ES_nonneg
    calc S ^ 2 + 4 * E * S
        = S ^ 2 + 4 * E * S + 0 := by ring
      _ ≤ S ^ 2 + 4 * E * S + 2 * S * Real.sqrt (4 * E * S) := by
          apply add_le_add_right
          apply mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hS_nonneg') (Real.sqrt_nonneg _)
      _ = S ^ 2 + 2 * S * Real.sqrt (4 * E * S) + Real.sqrt (4 * E * S) ^ 2 := by
          rw [hsq4ES]
          ring
      _ = (S + Real.sqrt (4 * E * S)) ^ 2 := by ring
  -- Combine: δ ≤ S + √(S² + 4ES) ≤ S + S + √(4ES) = 2S + √(4ES)
  calc δ ≤ S + Real.sqrt (S ^ 2 + 4 * E * S) := hδ_le_root
    _ ≤ S + (S + Real.sqrt (4 * E * S)) := add_le_add_right hsqrt_triangle S
    _ = Real.sqrt (4 * E * S) + 2 * S := by ring

/-- Corollary: Under dominance, error regret is bounded by log(1/c).
    E^ξ - E^μ ≤ √(4·E^μ·log(1/c)) + 2·log(1/c) -/
theorem error_bound_dominance (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (n : ℕ)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
    Real.sqrt (4 * expectedOptimalErrors μ n * Real.log (1 / c.toReal)) +
    2 * Real.log (1 / c.toReal) := by
  have hSn := convergence_bound μ ξ hdom hc0 n h_cond_true h_cond_false
  have hMain := error_bound_main μ ξ n
  have hEμ_nonneg : 0 ≤ expectedOptimalErrors μ n := by
    unfold expectedOptimalErrors expectPrefix
    apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro f _
    apply mul_nonneg ENNReal.toReal_nonneg
    exact errorProb_nonneg μ _ _
  calc expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n
      ≤ Real.sqrt (4 * expectedOptimalErrors μ n * totalSqDist μ ξ n) +
        2 * totalSqDist μ ξ n := hMain
    _ ≤ Real.sqrt (4 * expectedOptimalErrors μ n * Real.log (1 / c.toReal)) +
        2 * Real.log (1 / c.toReal) := by
      apply add_le_add
      · apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left hSn
        apply mul_nonneg (by linarith) hEμ_nonneg
      · apply mul_le_mul_of_nonneg_left hSn (by norm_num : (0:ℝ) ≤ 2)

/-- For deterministic environments, the universal predictor makes only finitely many errors.

    **Hypothesis**: The environment μ is deterministic, i.e., expectedOptimalErrors μ n = 0 for all n.
    This means at each step, μ assigns probability 1 to the true outcome.

    Under this condition: E^ξ ≤ 2·log(1/c) for all n.

    The proof:
    1. From error_bound_dominance: E^ξ - E^μ ≤ √(4·E^μ·log(1/c)) + 2·log(1/c)
    2. With E^μ = 0: E^ξ ≤ √(0) + 2·log(1/c) = 2·log(1/c)
    3. Therefore E^ξ is uniformly bounded by 2·log(1/c). -/
theorem finite_errors_deterministic (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false)
    (h_deterministic : ∀ n, expectedOptimalErrors μ n = 0) :
    ∃ B : ℝ, ∀ n, expectedUniversalErrors μ ξ n ≤ B := by
  use 2 * Real.log (1 / c.toReal) + 1
  intro n
  have hbound := error_bound_dominance μ ξ hdom hc0 n h_cond_true h_cond_false
  rw [h_deterministic n] at hbound
  -- Simplify: √(4 * 0 * log(1/c)) = √0 = 0
  have hsimpl : Real.sqrt (4 * 0 * Real.log (1 / c.toReal)) = 0 := by
    simp only [mul_zero, zero_mul, Real.sqrt_zero]
  rw [hsimpl] at hbound
  simp only [zero_add, sub_zero] at hbound
  calc expectedUniversalErrors μ ξ n
      ≤ 2 * Real.log (1 / c.toReal) := hbound
    _ ≤ 2 * Real.log (1 / c.toReal) + 1 := by linarith

end ErrorBounds

end Mettapedia.Logic.UniversalPrediction
