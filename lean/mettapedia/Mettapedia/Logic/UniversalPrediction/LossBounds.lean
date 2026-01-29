import Mettapedia.Logic.UniversalPrediction.ErrorBounds

/-!
# Loss Bounds (Hutter 2005, Section 3.4)

This file formalizes the general loss bounds from Chapter 3 of Hutter's
"Universal Artificial Intelligence", extending the error bounds to arbitrary loss functions.

## Main Definitions

* `LossFunction` - A bounded loss function ℓ : Alphabet × Alphabet → [0, 1]
* `expectedLoss` - Expected loss under a predictor
* `regret` - Difference between universal and optimal expected loss

## Main Results

* Theorem 3.48: Unit loss bound
* Corollary 3.49: Unit loss corollaries
* Theorem 3.59: Instantaneous loss bound
* Theorem 3.60: General loss bound

## References

- Hutter, M. (2005). "Universal Artificial Intelligence", Section 3.4
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators
open FiniteHorizon Convergence ErrorBounds

namespace LossBounds

/-! ## Definition: Loss Functions -/

/-- A loss function ℓ : Bool × Bool → [0, 1] for binary alphabet.
    ℓ(predicted, actual) measures the loss incurred when predicting `predicted`
    and the actual outcome is `actual`. -/
structure LossFunction where
  toFun : Bool → Bool → ℝ
  nonneg : ∀ p a, 0 ≤ toFun p a
  le_one : ∀ p a, toFun p a ≤ 1

instance : CoeFun LossFunction (fun _ => Bool → Bool → ℝ) where
  coe := LossFunction.toFun

/-- The unit loss (0-1 loss): ℓ(p, a) = 1 if p ≠ a, else 0. -/
def unitLoss : LossFunction where
  toFun p a := if p = a then 0 else 1
  nonneg := by intro p a; split_ifs <;> norm_num
  le_one := by intro p a; split_ifs <;> norm_num

/-- Expected loss at step t for a predictor that predicts b given history x. -/
def stepLoss (μ : PrefixMeasure) (ℓ : LossFunction) (prediction : Bool) (x : BinString) : ℝ :=
  FiniteHorizon.condProb μ.toSemimeasure x true * ℓ prediction true +
  FiniteHorizon.condProb μ.toSemimeasure x false * ℓ prediction false

/-- Expected loss for the optimal predictor (minimizes expected loss). -/
def optimalLoss (μ : PrefixMeasure) (ℓ : LossFunction) (x : BinString) : ℝ :=
  min (stepLoss μ ℓ true x) (stepLoss μ ℓ false x)

/-- Expected loss for the universal predictor. -/
def universalLoss (μ : PrefixMeasure) (ξ : Semimeasure) (ℓ : LossFunction) (x : BinString) : ℝ :=
  stepLoss μ ℓ (universalPrediction ξ x) x

/-! ## Theorem 3.48: Unit Loss Bound -/

/-- **Theorem 3.48 (Unit Loss Bound)**:
    For unit loss (0-1 loss), the cumulative regret is bounded by O(√(E^μ · D)).

    E^ξ_n - E^μ_n ≤ √(4 · E^μ_n · D_n) + 2·D_n

    where D_n = log(1/c) under c-dominance.

    **Note**: This is essentially `error_bound_dominance` specialized to unit loss.
    The unit loss error equals the prediction error probability. -/
theorem unit_loss_bound (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (n : ℕ)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
    Real.sqrt (4 * expectedOptimalErrors μ n * Real.log (1 / c.toReal)) +
    2 * Real.log (1 / c.toReal) :=
  error_bound_dominance μ ξ hdom hc0 n h_cond_true h_cond_false

/-! ## Corollary 3.49: Unit Loss Corollaries -/

/-- **Corollary 3.49a**: For deterministic environments (E^μ = 0),
    the universal predictor makes at most O(log(1/c)) errors total.

    This is exactly `finite_errors_deterministic` from ErrorBounds.lean. -/
theorem unit_loss_deterministic (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false)
    (h_deterministic : ∀ n, expectedOptimalErrors μ n = 0) :
    ∃ B : ℝ, ∀ n, expectedUniversalErrors μ ξ n ≤ B :=
  finite_errors_deterministic μ ξ hdom hc0 h_cond_true h_cond_false h_deterministic

/-- Helper: condProb is nonnegative (for errorProb bounds). -/
private lemma condProb_nonneg (ρ : Semimeasure) (x : BinString) (b : Bool) :
    0 ≤ FiniteHorizon.condProb ρ x b := by
  unfold FiniteHorizon.condProb conditionalENN
  exact ENNReal.toReal_nonneg

/-- Error probability is at most 1. -/
private lemma errorProb_le_one (μ : PrefixMeasure) (b : Bool) (x : BinString) :
    errorProb μ b x ≤ 1 := by
  unfold errorProb
  have h := condProb_nonneg μ.toSemimeasure x b
  linarith

/-- optimalErrorProb is at most 1. -/
private lemma optimalErrorProb_le_one (μ : PrefixMeasure) (x : BinString) :
    optimalErrorProb μ x ≤ 1 :=
  errorProb_le_one μ (optimalPrediction μ x) x

/-- expectPrefix of a function bounded by 1 is at most 1. -/
private lemma expectPrefix_le_one_of_bounded (μ : PrefixMeasure) (k : ℕ)
    (g : BinString → ℝ) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    expectPrefix μ k g ≤ 1 := by
  unfold expectPrefix
  have hweights := sum_prefixPMF_toReal μ k
  calc ∑ f : Fin k → Bool, (prefixPMF μ k f).toReal * g (List.ofFn f)
      ≤ ∑ f : Fin k → Bool, (prefixPMF μ k f).toReal * 1 := by
        apply Finset.sum_le_sum; intro f _
        apply mul_le_mul_of_nonneg_left (hg _).2 ENNReal.toReal_nonneg
    _ = ∑ f : Fin k → Bool, (prefixPMF μ k f).toReal := by simp
    _ = 1 := hweights

/-- expectedOptimalErrors μ n ≤ n. -/
private lemma expectedOptimalErrors_le_n (μ : PrefixMeasure) (n : ℕ) :
    expectedOptimalErrors μ n ≤ n := by
  unfold expectedOptimalErrors
  have h_exp_le : ∀ k, expectPrefix μ k (optimalErrorProb μ) ≤ 1 := fun k =>
    expectPrefix_le_one_of_bounded μ k (optimalErrorProb μ) fun x =>
      ⟨errorProb_nonneg μ _ x, optimalErrorProb_le_one μ x⟩
  calc ∑ k ∈ Finset.range n, expectPrefix μ k (optimalErrorProb μ)
      ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro k _; exact h_exp_le k
    _ = n := by simp [Finset.card_range]

/-- **Corollary 3.49b**: Average regret per step vanishes as n → ∞.

    (E^ξ_n - E^μ_n) / n → 0 as n → ∞.

    **Proof strategy**:
    1. From `error_bound_dominance`, the regret is bounded by:
       regret_n ≤ √(4 · E^μ_n · D) + 2D  where D = log(1/c)
    2. E^μ_n ≤ n since each step contributes at most 1 to expected errors
    3. Therefore: regret_n / n ≤ 2√(D/n) + 2D/n
    4. As n → ∞: √(D/n) → 0 and D/n → 0
    5. By squeeze theorem: regret_n / n → 0 -/
theorem average_regret_vanishes (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    Filter.Tendsto
      (fun n => (expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n) / n)
      Filter.atTop (nhds 0) := by
  -- Let D = log(1/c)
  set D := Real.log (1 / c.toReal) with hD_def
  -- D ≥ 0 since c ≤ 1
  have hc1 : c ≤ 1 := dominates_const_le_one hdom
  have hcTop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hcTop
  have hcReal_le_one : c.toReal ≤ 1 := ENNReal.toReal_mono ENNReal.one_ne_top hc1
  have hone_le : 1 ≤ 1 / c.toReal := one_le_one_div hcpos hcReal_le_one
  have hD_nonneg : 0 ≤ D := Real.log_nonneg hone_le

  -- For n > 0: regret_n / n ≤ 2√(D/n) + 2D/n
  have hbound : ∀ n : ℕ, n > 0 →
      (expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n) / n ≤
      2 * Real.sqrt (D / n) + 2 * D / n := by
    intro n hn
    have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
    have hEμn := expectedOptimalErrors_le_n μ n
    have hEμ_nonneg := expectedOptimalErrors_nonneg μ n
    -- regret_n ≤ √(4 * E^μ_n * D) + 2D
    have h_err := error_bound_dominance μ ξ hdom hc0 n h_cond_true h_cond_false
    -- √(4 * E^μ_n * D) ≤ √(4 * n * D) since E^μ_n ≤ n
    have h1 : Real.sqrt (4 * expectedOptimalErrors μ n * D) ≤ Real.sqrt (4 * n * D) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hEμn (by norm_num)
      · exact hD_nonneg
    have h2 : expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
              Real.sqrt (4 * n * D) + 2 * D := by linarith
    -- Divide by n
    have hn_nonneg : (0 : ℝ) ≤ n := le_of_lt hn_pos
    have h3 : (expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n) / n ≤
              (Real.sqrt (4 * n * D) + 2 * D) / n :=
      div_le_div_of_nonneg_right h2 hn_nonneg
    -- √(4nD) / n = 2√(D/n)
    have hsqrt : Real.sqrt (4 * n * D) / n = 2 * Real.sqrt (D / n) := by
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      have hDn_nonneg : 0 ≤ D / n := div_nonneg hD_nonneg hn_nonneg
      have h4nD_nonneg : 0 ≤ 4 * n * D := by positivity
      have hnD_nonneg : 0 ≤ (n : ℝ) * D := by positivity
      -- √4 = 2
      have hsqrt4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2^2 by norm_num]
        exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
      -- √(4nD) = √4 * √(nD) = 2 * √(nD)
      have h1 : Real.sqrt (4 * n * D) = 2 * Real.sqrt ((n : ℝ) * D) := by
        rw [show (4 : ℝ) * n * D = 4 * ((n : ℝ) * D) by ring]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        rw [hsqrt4]
      -- √(nD) / n = √(D/n) when n > 0
      have h2 : Real.sqrt ((n : ℝ) * D) / n = Real.sqrt (D / n) := by
        -- Use (√(nD) / n)² = nD/n² = D/n = (√(D/n))²
        have hlhs_nonneg : 0 ≤ Real.sqrt ((n : ℝ) * D) / n :=
          div_nonneg (Real.sqrt_nonneg _) hn_nonneg
        rw [← Real.sqrt_sq hlhs_nonneg]
        rw [Real.sqrt_inj (sq_nonneg _) hDn_nonneg]
        rw [div_pow, Real.sq_sqrt hnD_nonneg]
        field_simp [hn_ne]
      rw [h1, mul_div_assoc, h2]
    calc (expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n) / n
        ≤ (Real.sqrt (4 * n * D) + 2 * D) / n := h3
      _ = Real.sqrt (4 * n * D) / n + 2 * D / n := by rw [add_div]
      _ = 2 * Real.sqrt (D / n) + 2 * D / n := by rw [hsqrt]

  -- The bound 2√(D/n) + 2D/n → 0 as n → ∞
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * Real.sqrt (D / n) + 2 * D / n)
      Filter.atTop (nhds 0) := by
    -- D/n → 0
    have h1 : Filter.Tendsto (fun n : ℕ => D / n) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat D
    -- √(D/n) → 0
    have h2 : Filter.Tendsto (fun n : ℕ => Real.sqrt (D / n)) Filter.atTop (nhds 0) := by
      have := h1.sqrt
      simp only [Real.sqrt_zero] at this
      exact this
    -- 2√(D/n) → 0
    have h3 : Filter.Tendsto (fun n : ℕ => 2 * Real.sqrt (D / n)) Filter.atTop (nhds 0) := by
      have := h2.const_mul 2
      simp only [mul_zero] at this
      exact this
    -- 2D/n → 0
    have h4 : Filter.Tendsto (fun n : ℕ => 2 * D / n) Filter.atTop (nhds 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (2 * D)
      simp only [mul_div_assoc] at this ⊢
      exact this
    have := h3.add h4
    simp only [add_zero] at this
    exact this

  -- regret_n ≥ 0 since optimal ≤ universal
  have hlower : ∀ n : ℕ, 0 ≤ (expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n) / n := by
    intro n
    have hpos := expectedOptimalErrors_le_universal μ ξ n
    by_cases hn : n = 0
    · simp [hn]
    · have hn_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      exact div_nonneg (by linarith) (le_of_lt hn_pos)

  -- Eventually upper bounded
  have hupper : ∀ᶠ n in Filter.atTop, (expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n) / n ≤
      2 * Real.sqrt (D / n) + 2 * D / n := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact hbound n hn

  -- Squeeze theorem: 0 → 0 and bound → 0, so regret/n → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · -- lower bound: 0 ≤ f eventually
    exact Filter.Eventually.of_forall hlower
  · -- upper bound: f ≤ bound eventually
    exact hupper

/-! ## Theorem 3.59: Instantaneous Loss Bound

This theorem bounds the instantaneous loss difference at time t, showing that
the per-step regret also vanishes. -/

/-- Helper: condProb is nonnegative since it's the toReal of an ENNReal. -/
private lemma condProb_nonneg' (ρ : Semimeasure) (x : BinString) (b : Bool) :
    0 ≤ FiniteHorizon.condProb ρ x b := by
  unfold FiniteHorizon.condProb conditionalENN
  exact ENNReal.toReal_nonneg

/-! ### Unit Loss Case

For unit loss (0-1 loss), we can prove the tight bound using the error probability
lemmas from ErrorBounds.lean. The key is that stepLoss with unitLoss equals errorProb. -/

/-- stepLoss with unitLoss equals errorProb (when condProb sums to 1). -/
lemma stepLoss_unitLoss_eq_errorProb (μ : PrefixMeasure) (b : Bool) (x : BinString)
    (hμx : μ x ≠ 0) :
    stepLoss μ unitLoss b x = errorProb μ b x := by
  unfold stepLoss unitLoss errorProb
  have hsum := Convergence.condProb_sum_eq_one μ x hμx
  cases b
  · -- b = false: stepLoss = condProb(true)*1 + condProb(false)*0 = condProb(true)
    --            errorProb = 1 - condProb(false) = condProb(true) (by sum = 1)
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, add_zero]
    linarith
  · -- b = true: stepLoss = condProb(true)*0 + condProb(false)*1 = condProb(false)
    --           errorProb = 1 - condProb(true) = condProb(false) (by sum = 1)
    simp only [↓reduceIte, mul_zero, Bool.true_eq_false, mul_one, zero_add]
    linarith

/-- universalLoss with unitLoss equals universalErrorProb. -/
lemma universalLoss_unitLoss_eq (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (hμx : μ x ≠ 0) :
    universalLoss μ ξ unitLoss x = universalErrorProb μ ξ x := by
  unfold universalLoss universalErrorProb
  exact stepLoss_unitLoss_eq_errorProb μ (universalPrediction ξ x) x hμx

/-- optimalLoss with unitLoss equals optimalErrorProb. -/
lemma optimalLoss_unitLoss_eq (μ : PrefixMeasure) (x : BinString) (hμx : μ x ≠ 0) :
    optimalLoss μ unitLoss x = optimalErrorProb μ x := by
  unfold optimalLoss optimalErrorProb
  rw [stepLoss_unitLoss_eq_errorProb _ _ _ hμx, stepLoss_unitLoss_eq_errorProb _ _ _ hμx]
  -- min(errorProb true, errorProb false) = errorProb(optimalPred)
  -- We need to show this equality
  unfold optimalPrediction
  have hsum := Convergence.condProb_sum_eq_one μ x hμx
  by_cases h : FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1/2
  · simp only [decide_eq_true_eq.mpr h]
    -- true predicts when condProb(true) ≥ 1/2, so errorProb(true) ≤ errorProb(false)
    -- errorProb(true) = 1 - condProb(true), errorProb(false) = 1 - condProb(false)
    -- condProb(true) + condProb(false) = 1, so
    -- 1 - condProb(true) = condProb(false) and 1 - condProb(false) = condProb(true)
    -- Since condProb(true) ≥ 1/2, we have condProb(false) ≤ 1/2
    -- So errorProb(true) = condProb(false) ≤ 1/2 ≤ condProb(true) = errorProb(false)
    have hle : errorProb μ true x ≤ errorProb μ false x := by
      unfold errorProb; linarith
    rw [min_eq_left hle]
  · push_neg at h
    simp only [decide_eq_false_iff_not.mpr (not_le.mpr h)]
    -- false predicts when condProb(true) < 1/2
    have hle : errorProb μ false x ≤ errorProb μ true x := by
      unfold errorProb; linarith
    rw [min_eq_right hle]

/-- **Theorem 3.59 for Unit Loss**:
    For unit loss (0-1 loss), the per-step loss difference satisfies:

    |L^ξ_t - L^μ_t| ≤ √2 · √(sqDistStep) ≤ 2 · √(sqDistStep)

    This follows directly from the error probability bounds in ErrorBounds.lean.

    **Proof**:
    - When predictions agree: |diff| = 0
    - When predictions disagree:
      - |universalErrorProb - optimalErrorProb| = |2p - 1| (error_diff_eq_abs_two_p_minus_one)
      - sqDistStep ≥ (2p - 1)² / 2 (sqDistStep_ge_error_diff_sq)
      - So |diff| = |2p - 1| ≤ √(2 · sqDistStep) ≤ 2√(sqDistStep) -/
theorem instantaneous_unit_loss_bound (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (hμx : μ x ≠ 0) :
    |universalLoss μ ξ unitLoss x - optimalLoss μ unitLoss x| ≤
    2 * Real.sqrt (sqDistStep μ ξ x) := by
  rw [universalLoss_unitLoss_eq μ ξ x hμx, optimalLoss_unitLoss_eq μ x hμx]
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (sqDistStep μ ξ x) := Real.sqrt_nonneg _
  have h_sqDist_nonneg := sqDistStep_nonneg μ ξ x
  -- Case split: do predictions agree?
  by_cases h_agree : universalPrediction ξ x = optimalPrediction μ x
  · -- Predictions agree: difference = 0
    rw [error_eq_when_predictions_agree μ ξ x h_agree, sub_self, abs_zero]
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h_sqrt_nonneg
  · -- Predictions disagree: use the error bounds
    -- |universalErrorProb - optimalErrorProb| = |2p - 1|
    have h_diff := error_diff_eq_abs_two_p_minus_one μ ξ x hμx h_agree
    -- sqDistStep ≥ (2p - 1)² / 2
    have h_sq := sqDistStep_ge_error_diff_sq μ ξ x h_agree
    set p := FiniteHorizon.condProb μ.toSemimeasure x true
    -- Goal: |2p - 1| ≤ 2 * √sqDistStep
    -- From h_sq: (2p - 1)² / 2 ≤ sqDistStep
    -- So (2p - 1)² ≤ 2 * sqDistStep
    -- Taking sqrt: |2p - 1| ≤ √(2 * sqDistStep) = √2 * √sqDistStep ≤ 2 * √sqDistStep
    rw [h_diff]
    have h_sq' : (2 * p - 1) ^ 2 ≤ 2 * sqDistStep μ ξ x := by linarith
    have h_abs_sq : |2 * p - 1| = Real.sqrt ((2 * p - 1) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h_abs_sq]
    have h_sqrt_mono : Real.sqrt ((2 * p - 1) ^ 2) ≤ Real.sqrt (2 * sqDistStep μ ξ x) :=
      Real.sqrt_le_sqrt h_sq'
    have h_sqrt_mul : Real.sqrt (2 * sqDistStep μ ξ x) =
        Real.sqrt 2 * Real.sqrt (sqDistStep μ ξ x) :=
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
    calc Real.sqrt ((2 * p - 1) ^ 2)
        ≤ Real.sqrt (2 * sqDistStep μ ξ x) := h_sqrt_mono
      _ = Real.sqrt 2 * Real.sqrt (sqDistStep μ ξ x) := h_sqrt_mul
      _ ≤ 2 * Real.sqrt (sqDistStep μ ξ x) := by
          apply mul_le_mul_of_nonneg_right _ h_sqrt_nonneg
          -- Show √2 ≤ 2: equivalent to 2 ≤ 4
          have hsqrt2 : Real.sqrt 2 ≤ 2 := by
            rw [Real.sqrt_le_iff]
            constructor
            · norm_num
            · norm_num
          exact hsqrt2

/-! ### Why the Bound Fails for General Losses

The bound |universalLoss - optimalLoss| ≤ 2√sqDistStep holds for **unit loss** but
fails for general losses. The issue is a definitional mismatch:

- `universalPrediction` is based on condProb ≥ 1/2 (error probability minimization)
- `optimalLoss` is the minimum stepLoss (which depends on the loss function)

For general losses, the stepLoss-minimizing prediction may differ from the threshold
prediction, causing the bound to fail even when sqDistStep = 0.

**Counterexample**: When condProb_μ = condProb_ξ = 0.6 (so sqDistStep = 0), consider
a loss where ℓ(T,T)=0, ℓ(T,F)=1, ℓ(F,T)=0.01, ℓ(F,F)=0. Then:
- universalPrediction = true (0.6 ≥ 0.5)
- stepLoss(true) = 0.4, stepLoss(false) = 0.006
- universalLoss = 0.4, optimalLoss = 0.006
- |diff| = 0.394 > 0 = 2√0 -/

/-- An asymmetric loss function where predicting false incurs tiny loss.
    ℓ(T,T) = 0, ℓ(T,F) = 1, ℓ(F,T) = 0.01, ℓ(F,F) = 0 -/
def asymmetricLoss : LossFunction where
  toFun pred actual :=
    match pred, actual with
    | true, true => 0
    | true, false => 1
    | false, true => 0.01
    | false, false => 0
  nonneg := by intro p a; cases p <;> cases a <;> norm_num
  le_one := by intro p a; cases p <;> cases a <;> norm_num

/-- Count true values in a boolean list -/
def countTrue (x : BinString) : ℕ := (x.filter (· = true)).length

/-- Count false values in a boolean list -/
def countFalse (x : BinString) : ℕ := (x.filter (· = false)).length

@[simp] lemma countTrue_nil : countTrue [] = 0 := rfl
@[simp] lemma countFalse_nil : countFalse [] = 0 := rfl
@[simp] lemma countTrue_cons_true (x : BinString) : countTrue (true :: x) = countTrue x + 1 := by
  simp [countTrue, List.filter]
@[simp] lemma countTrue_cons_false (x : BinString) : countTrue (false :: x) = countTrue x := by
  simp [countTrue, List.filter]
@[simp] lemma countFalse_cons_true (x : BinString) : countFalse (true :: x) = countFalse x := by
  simp [countFalse, List.filter]
@[simp] lemma countFalse_cons_false (x : BinString) : countFalse (false :: x) = countFalse x + 1 := by
  simp [countFalse, List.filter]
@[simp] lemma countTrue_append (x y : BinString) : countTrue (x ++ y) = countTrue x + countTrue y := by
  simp [countTrue]
@[simp] lemma countFalse_append (x y : BinString) : countFalse (x ++ y) = countFalse x + countFalse y := by
  simp [countFalse]

/-- Count lemmas for singleton lists -/
@[simp] lemma countTrue_singleton_true : countTrue [true] = 1 := rfl
@[simp] lemma countTrue_singleton_false : countTrue [false] = 0 := rfl
@[simp] lemma countFalse_singleton_true : countFalse [true] = 0 := rfl
@[simp] lemma countFalse_singleton_false : countFalse [false] = 1 := rfl

/-- A biased coin measure: at each step, P(true) = p, P(false) = 1-p.
    For 0 < p < 1, this is a valid prefix measure. -/
noncomputable def biasedCoinMeasure (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : PrefixMeasure where
  toFun := fun x => ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x)
  root_eq_one' := by simp
  additive' := fun x => by
    have hp_nn : 0 ≤ p := le_of_lt hp0
    have h1mp_nn : 0 ≤ 1 - p := by linarith
    simp only [countTrue_append, countFalse_append, countTrue_singleton_true,
               countFalse_singleton_true, countTrue_singleton_false, countFalse_singleton_false,
               add_zero]
    have h1 : 0 ≤ p ^ countTrue x * (1 - p) ^ (countFalse x + 1) := by positivity
    have h2 : 0 ≤ p ^ (countTrue x + 1) * (1 - p) ^ countFalse x := by positivity
    rw [← ENNReal.ofReal_add h1 h2]
    congr 1
    rw [pow_succ, pow_succ]; ring

/-- The conditional probability under a biased coin measure is exactly p for true. -/
lemma biasedCoinMeasure_condProb_true (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (x : BinString) :
    FiniteHorizon.condProb (biasedCoinMeasure p hp0 hp1).toSemimeasure x true = p := by
  unfold FiniteHorizon.condProb conditionalENN
  simp only [PrefixMeasure.toSemimeasure_apply, biasedCoinMeasure]
  have hp_nn : 0 ≤ p := le_of_lt hp0
  have h1mp_pos : 0 < 1 - p := by linarith
  have hdenom_pos : 0 < p ^ countTrue x * (1 - p) ^ countFalse x := by positivity
  have hdenom_ne : ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hdenom_pos
  simp only [countTrue_append, countFalse_append, countTrue_singleton_true,
             countFalse_singleton_true, add_zero]
  rw [pow_succ]
  have hnum : p ^ countTrue x * p * (1 - p) ^ countFalse x =
              p ^ countTrue x * (1 - p) ^ countFalse x * p := by ring
  rw [hnum, ENNReal.ofReal_mul (le_of_lt hdenom_pos)]
  rw [mul_comm (ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x)) (ENNReal.ofReal p)]
  rw [mul_div_assoc, ENNReal.div_self hdenom_ne ENNReal.ofReal_ne_top, mul_one]
  simp only [ENNReal.toReal_ofReal hp_nn]

/-- The conditional probability under a biased coin measure is 1-p for false. -/
lemma biasedCoinMeasure_condProb_false (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (x : BinString) :
    FiniteHorizon.condProb (biasedCoinMeasure p hp0 hp1).toSemimeasure x false = 1 - p := by
  unfold FiniteHorizon.condProb conditionalENN
  simp only [PrefixMeasure.toSemimeasure_apply, biasedCoinMeasure]
  have h1mp_pos : 0 < 1 - p := by linarith
  have h1mp_nn : 0 ≤ 1 - p := le_of_lt h1mp_pos
  have hdenom_pos : 0 < p ^ countTrue x * (1 - p) ^ countFalse x := by positivity
  have hdenom_ne : ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hdenom_pos
  simp only [countTrue_append, countFalse_append, countTrue_singleton_false,
             countFalse_singleton_false, add_zero]
  rw [pow_succ]
  have hnum : p ^ countTrue x * ((1 - p) ^ countFalse x * (1 - p)) =
              p ^ countTrue x * (1 - p) ^ countFalse x * (1 - p) := by ring
  rw [hnum, ENNReal.ofReal_mul (le_of_lt hdenom_pos)]
  rw [mul_comm (ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x)) (ENNReal.ofReal (1 - p))]
  rw [mul_div_assoc, ENNReal.div_self hdenom_ne ENNReal.ofReal_ne_top, mul_one]
  simp only [ENNReal.toReal_ofReal h1mp_nn]

/-- **Counterexample**: The bound |universalLoss - optimalLoss| ≤ 2√sqDistStep
    fails for general loss functions.

    When condProb_μ = condProb_ξ, we have sqDistStep = 0, but the loss difference
    can be positive if the loss function's optimal prediction differs from the
    threshold-based prediction. -/
theorem instantaneous_loss_bound_fails_general :
    ∃ (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString) (ℓ : LossFunction),
    |universalLoss μ ξ ℓ x - optimalLoss μ ℓ x| > 2 * Real.sqrt (sqDistStep μ ξ x) := by
  -- Use biased coin with p = 0.6
  have hp0 : (0 : ℝ) < 0.6 := by norm_num
  have hp1 : (0.6 : ℝ) < 1 := by norm_num
  let μ := biasedCoinMeasure 0.6 hp0 hp1
  use μ, μ.toSemimeasure, [], asymmetricLoss
  -- sqDistStep = 2 * (condProb_μ(true) - condProb_ξ(true))² = 0 (since μ = ξ)
  have hsqDist : sqDistStep μ μ.toSemimeasure [] = 0 := by
    unfold sqDistStep
    simp only [Entropy.sqDistBinary_eq_two_mul, sub_self]; norm_num
  rw [hsqDist, Real.sqrt_zero, mul_zero]
  -- Now compute the losses
  -- universalPrediction = true (since condProb(true) = 0.6 ≥ 0.5)
  have hcond_true : FiniteHorizon.condProb μ.toSemimeasure [] true = 0.6 :=
    biasedCoinMeasure_condProb_true 0.6 hp0 hp1 []
  have hcond_false : FiniteHorizon.condProb μ.toSemimeasure [] false = 0.4 := by
    rw [biasedCoinMeasure_condProb_false 0.6 hp0 hp1 []]; norm_num
  have huniv_pred : universalPrediction μ.toSemimeasure [] = true := by
    unfold universalPrediction
    simp only [decide_eq_true_eq]
    rw [hcond_true]; norm_num
  -- stepLoss(true) = 0.6 * 0 + 0.4 * 1 = 0.4
  -- stepLoss(false) = 0.6 * 0.01 + 0.4 * 0 = 0.006
  have hstep_true : stepLoss μ asymmetricLoss true [] = 0.4 := by
    unfold stepLoss asymmetricLoss
    simp only []
    rw [hcond_true, hcond_false]
    norm_num
  have hstep_false : stepLoss μ asymmetricLoss false [] = 0.006 := by
    unfold stepLoss asymmetricLoss
    simp only []
    rw [hcond_true, hcond_false]
    norm_num
  -- universalLoss = stepLoss(true) = 0.4
  have hunivLoss : universalLoss μ μ.toSemimeasure asymmetricLoss [] = 0.4 := by
    unfold universalLoss
    rw [huniv_pred, hstep_true]
  -- optimalLoss = min(0.4, 0.006) = 0.006
  have hoptLoss : optimalLoss μ asymmetricLoss [] = 0.006 := by
    unfold optimalLoss
    rw [hstep_true, hstep_false]
    simp only [min_eq_right_iff]
    norm_num
  -- |0.4 - 0.006| = 0.394 > 0
  rw [hunivLoss, hoptLoss]
  norm_num

/-! ### Loss-Specific Predictions: The Correct Formulation

The correct theorem uses **loss-specific predictions**: each predictor minimizes
expected loss under its own probability estimate, rather than using a fixed threshold.

With this formulation:
- When predictions agree: difference = 0
- When predictions disagree: p and q are on opposite sides of a loss-dependent threshold,
  so |p - q| ≥ |p - threshold|, giving the bound. -/

/-- Expected loss for prediction b, computed using probability estimate ρ. -/
def stepLossFor (ρ : Semimeasure) (ℓ : LossFunction) (b : Bool) (x : BinString) : ℝ :=
  FiniteHorizon.condProb ρ x true * ℓ b true +
  FiniteHorizon.condProb ρ x false * ℓ b false

/-- Optimal prediction for loss function ℓ under probability estimate ρ:
    Choose the prediction that minimizes expected loss. -/
def optimalPredictionFor (ρ : Semimeasure) (ℓ : LossFunction) (x : BinString) : Bool :=
  decide (stepLossFor ρ ℓ true x ≤ stepLossFor ρ ℓ false x)

/-- Universal prediction for loss function ℓ using estimate ξ:
    Choose the prediction that minimizes expected loss under ξ. -/
def universalPredictionFor (ξ : Semimeasure) (ℓ : LossFunction) (x : BinString) : Bool :=
  optimalPredictionFor ξ ℓ x

/-- Actual loss incurred when using the universal prediction (evaluated under μ). -/
def universalLossFor (μ : PrefixMeasure) (ξ : Semimeasure) (ℓ : LossFunction)
    (x : BinString) : ℝ :=
  stepLoss μ ℓ (universalPredictionFor ξ ℓ x) x

/-- Actual loss incurred when using the optimal prediction (evaluated under μ). -/
def optimalLossFor (μ : PrefixMeasure) (ℓ : LossFunction) (x : BinString) : ℝ :=
  stepLoss μ ℓ (optimalPredictionFor μ.toSemimeasure ℓ x) x

/-- For unit loss with probability measures, optimalPredictionFor matches optimalPrediction.
    NOTE: This requires the conditional probabilities sum to 1 (probability measure condition).
    For general semimeasures, the threshold-based prediction may differ from loss-minimizing. -/
lemma optimalPredictionFor_unitLoss (μ : PrefixMeasure) (x : BinString)
    (hsum_eq : FiniteHorizon.condProb μ.toSemimeasure x true +
               FiniteHorizon.condProb μ.toSemimeasure x false = 1) :
    optimalPredictionFor μ.toSemimeasure unitLoss x = optimalPrediction μ x := by
  unfold optimalPredictionFor optimalPrediction stepLossFor unitLoss
  simp only [↓reduceIte, mul_zero, zero_add, add_zero]
  -- The if-expressions need explicit reduction
  have h1 : (true = false) = False := by decide
  have h2 : (false = true) = False := by decide
  simp only [h1, h2, ite_false, mul_one]
  -- Now: decide (condProb(false) ≤ condProb(true)) = decide (condProb(true) ≥ 1/2)
  have hp := condProb_nonneg' μ.toSemimeasure x false
  have hq := condProb_nonneg' μ.toSemimeasure x true
  congr 1
  apply propext
  constructor
  · intro hle; linarith
  · intro hge; linarith

/-- For unit loss with probability measures, universalPredictionFor matches universalPrediction.
    NOTE: This requires the conditional probabilities sum to 1 (probability measure condition). -/
lemma universalPredictionFor_unitLoss (ξ : Semimeasure) (x : BinString)
    (hsum_eq : FiniteHorizon.condProb ξ x true + FiniteHorizon.condProb ξ x false = 1) :
    universalPredictionFor ξ unitLoss x = universalPrediction ξ x := by
  unfold universalPredictionFor optimalPredictionFor universalPrediction stepLossFor unitLoss
  simp only [↓reduceIte, mul_zero, zero_add, add_zero]
  have h1 : (true = false) = False := by decide
  have h2 : (false = true) = False := by decide
  simp only [h1, h2, ite_false, mul_one]
  have hp := condProb_nonneg' ξ x false
  have hq := condProb_nonneg' ξ x true
  congr 1
  apply propext
  constructor
  · intro hle; linarith
  · intro hge; linarith

/-- The stepLoss difference |stepLoss(T) - stepLoss(F)| ≤ 1 (crude bound from loss ∈ [0,1]). -/
lemma stepLoss_diff_le_one (μ : PrefixMeasure) (ℓ : LossFunction) (x : BinString) :
    |stepLoss μ ℓ true x - stepLoss μ ℓ false x| ≤ 1 := by
  unfold stepLoss
  have hp := condProb_nonneg' μ.toSemimeasure x true
  have hq := condProb_nonneg' μ.toSemimeasure x false
  have hsum := condProb_sum_le_one μ.toSemimeasure x
  have hl1 := ℓ.le_one; have hl2 := ℓ.nonneg
  have hTT := hl1 true true; have hFT := hl1 false true
  have hTF := hl1 true false; have hFF := hl1 false false
  have hTT' := hl2 true true; have hFT' := hl2 false true
  have hTF' := hl2 true false; have hFF' := hl2 false false
  rw [abs_le]; constructor <;> nlinarith

/-- The "slope" of the stepLossFor difference: A - B where A = ℓ(T,T) - ℓ(F,T), B = ℓ(T,F) - ℓ(F,F).
    When p + q = 1: stepLossFor(T) - stepLossFor(F) = (A-B) * p + B. -/
def lossSlope (ℓ : LossFunction) : ℝ :=
  (ℓ true true - ℓ false true) - (ℓ true false - ℓ false false)

/-- The slope is bounded: |A - B| ≤ 2 since all loss values are in [0, 1]. -/
lemma lossSlope_abs_le_two (ℓ : LossFunction) : |lossSlope ℓ| ≤ 2 := by
  unfold lossSlope
  have h1 := ℓ.nonneg true true; have h2 := ℓ.nonneg true false
  have h3 := ℓ.nonneg false true; have h4 := ℓ.nonneg false false
  have h5 := ℓ.le_one true true; have h6 := ℓ.le_one true false
  have h7 := ℓ.le_one false true; have h8 := ℓ.le_one false false
  rw [abs_le]; constructor <;> linarith

/-- The intercept of the loss difference line: when p=0, diff = B = ℓ(T,F) - ℓ(F,F). -/
def lossIntercept (ℓ : LossFunction) : ℝ :=
  ℓ true false - ℓ false false

/-- stepLossFor difference formula: diff = K * p + B where K = lossSlope, B = lossIntercept.
    Requires p + q = 1 (probability measure condition). -/
lemma stepLossFor_diff_eq (ρ : Semimeasure) (ℓ : LossFunction) (x : BinString)
    (hsum : FiniteHorizon.condProb ρ x true + FiniteHorizon.condProb ρ x false = 1) :
    stepLossFor ρ ℓ true x - stepLossFor ρ ℓ false x =
    lossSlope ℓ * FiniteHorizon.condProb ρ x true + lossIntercept ℓ := by
  unfold stepLossFor lossSlope lossIntercept
  have hq : FiniteHorizon.condProb ρ x false = 1 - FiniteHorizon.condProb ρ x true := by linarith
  rw [hq]; ring

/-- The threshold probability where stepLossFor(T) = stepLossFor(F).
    When lossSlope ≠ 0: t = -B/K where K = lossSlope, B = lossIntercept.
    When lossSlope = 0: we use 1/2 as a dummy value (predictions are always equal in this case). -/
noncomputable def lossThreshold (ℓ : LossFunction) : ℝ :=
  if lossSlope ℓ = 0 then 1/2 else -lossIntercept ℓ / lossSlope ℓ

/-- When K ≠ 0: stepLossFor(T) ≤ stepLossFor(F) iff K*p + B ≤ 0.
    This is equivalent to: (K > 0 ∧ p ≤ t) ∨ (K < 0 ∧ p ≥ t) where t = -B/K. -/
lemma stepLossFor_le_iff (ρ : Semimeasure) (ℓ : LossFunction) (x : BinString)
    (hsum : FiniteHorizon.condProb ρ x true + FiniteHorizon.condProb ρ x false = 1) :
    stepLossFor ρ ℓ true x ≤ stepLossFor ρ ℓ false x ↔
    lossSlope ℓ * FiniteHorizon.condProb ρ x true + lossIntercept ℓ ≤ 0 := by
  rw [← sub_nonpos, stepLossFor_diff_eq ρ ℓ x hsum]

/-- When predictions disagree, the threshold lies between p_μ and p_ξ.
    More precisely: (p_μ - t) * (p_ξ - t) ≤ 0. -/
lemma threshold_between_when_disagree (μ : PrefixMeasure) (ξ : Semimeasure) (ℓ : LossFunction)
    (x : BinString)
    (hsum_μ : FiniteHorizon.condProb μ.toSemimeasure x true +
              FiniteHorizon.condProb μ.toSemimeasure x false = 1)
    (hsum_ξ : FiniteHorizon.condProb ξ x true + FiniteHorizon.condProb ξ x false = 1)
    (h_disagree : optimalPredictionFor ξ ℓ x ≠ optimalPredictionFor μ.toSemimeasure ℓ x) :
    (FiniteHorizon.condProb μ.toSemimeasure x true - lossThreshold ℓ) *
    (FiniteHorizon.condProb ξ x true - lossThreshold ℓ) ≤ 0 := by
  let p_μ := FiniteHorizon.condProb μ.toSemimeasure x true
  let p_ξ := FiniteHorizon.condProb ξ x true
  -- Convert h_disagree to use the linear form K*p + B ≤ 0
  have h_disagree' : ¬((lossSlope ℓ * p_ξ + lossIntercept ℓ ≤ 0) ↔
                       (lossSlope ℓ * p_μ + lossIntercept ℓ ≤ 0)) := by
    unfold optimalPredictionFor at h_disagree
    simp only [ne_eq, decide_eq_decide, stepLossFor_le_iff μ.toSemimeasure ℓ x hsum_μ,
               stepLossFor_le_iff ξ ℓ x hsum_ξ] at h_disagree
    exact h_disagree
  by_cases hK : lossSlope ℓ = 0
  · -- When K = 0, the iff becomes trivial, contradicting h_disagree'
    simp only [hK, zero_mul, zero_add, iff_self, not_true_eq_false] at h_disagree'
  · -- When K ≠ 0, we have t = -B/K, so K*t + B = 0
    have ht : lossThreshold ℓ = -lossIntercept ℓ / lossSlope ℓ := by
      unfold lossThreshold; simp only [hK, ↓reduceIte]
    have hKt : lossSlope ℓ * lossThreshold ℓ = -lossIntercept ℓ := by
      rw [ht]; field_simp
    -- K*p + B = K*(p - t) since K*t = -B
    have heq_ξ : lossSlope ℓ * p_ξ + lossIntercept ℓ = lossSlope ℓ * (p_ξ - lossThreshold ℓ) := by
      linarith
    have heq_μ : lossSlope ℓ * p_μ + lossIntercept ℓ = lossSlope ℓ * (p_μ - lossThreshold ℓ) := by
      linarith
    rw [heq_ξ, heq_μ] at h_disagree'
    -- h_disagree' : ¬((K*(p_ξ - t) ≤ 0) ↔ (K*(p_μ - t) ≤ 0))
    -- This means one is ≤ 0 and the other is > 0, so their product with K² is < 0
    -- When K ≠ 0: K*(p_ξ - t) and K*(p_μ - t) have opposite signs
    -- Therefore (p_ξ - t) and (p_μ - t) have opposite signs
    -- So (p_μ - t)*(p_ξ - t) ≤ 0
    by_cases hKpos : 0 < lossSlope ℓ
    · -- K > 0: K*x ≤ 0 ↔ x ≤ 0
      have h_iff : ∀ y : ℝ, lossSlope ℓ * y ≤ 0 ↔ y ≤ 0 := fun y => by
        constructor
        · exact fun h => nonpos_of_mul_nonpos_right h hKpos
        · exact fun h => mul_nonpos_of_nonneg_of_nonpos (le_of_lt hKpos) h
      rw [h_iff, h_iff] at h_disagree'
      -- h_disagree' : ¬((p_ξ - t ≤ 0) ↔ (p_μ - t ≤ 0))
      by_cases hξ : p_ξ - lossThreshold ℓ ≤ 0
      · have hμ : 0 < p_μ - lossThreshold ℓ := by
          by_contra h; push_neg at h
          exact h_disagree' ⟨fun _ => h, fun _ => hξ⟩
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hμ) hξ
      · push_neg at hξ
        have hμ : p_μ - lossThreshold ℓ ≤ 0 := by
          by_contra h; push_neg at h
          -- Both (p_ξ - t > 0) and (p_μ - t > 0), so both sides of the iff are false
          -- Hence the iff is trivially true (false ↔ false = true)
          exact h_disagree' ⟨fun hξ_le => (hξ.not_ge hξ_le).elim, fun hμ_le => (h.not_ge hμ_le).elim⟩
        exact mul_nonpos_of_nonpos_of_nonneg hμ (le_of_lt hξ)
    · -- K < 0: K*x ≤ 0 ↔ x ≥ 0
      push_neg at hKpos
      have hKneg : lossSlope ℓ < 0 := lt_of_le_of_ne hKpos hK
      have h_iff : ∀ y : ℝ, lossSlope ℓ * y ≤ 0 ↔ 0 ≤ y := fun y => by
        constructor
        · intro h; rw [mul_comm] at h; exact nonneg_of_mul_nonpos_left h hKneg
        · exact fun h => mul_nonpos_of_nonpos_of_nonneg (le_of_lt hKneg) h
      rw [h_iff, h_iff] at h_disagree'
      -- h_disagree' : ¬((0 ≤ p_ξ - t) ↔ (0 ≤ p_μ - t))
      by_cases hξ : 0 ≤ p_ξ - lossThreshold ℓ
      · have hμ : p_μ - lossThreshold ℓ < 0 := by
          by_contra h; push_neg at h
          exact h_disagree' ⟨fun _ => h, fun _ => hξ⟩
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hμ) hξ
      · push_neg at hξ
        have hμ : 0 ≤ p_μ - lossThreshold ℓ := by
          by_contra h; push_neg at h
          -- Both (p_ξ - t < 0) and (p_μ - t < 0), so both sides of the iff are false
          -- Hence the iff is trivially true (false ↔ false = true)
          exact h_disagree' ⟨fun hξ_ge => ((not_le.mpr hξ) hξ_ge).elim,
                            fun hμ_ge => ((not_le.mpr h) hμ_ge).elim⟩
        exact mul_nonpos_of_nonneg_of_nonpos hμ (le_of_lt hξ)

/-- Helper: if a is between b and c (i.e., (b-a)*(c-a) ≤ 0), then |b-a| ≤ |b-c|. -/
lemma abs_le_abs_left_of_between (a b c : ℝ) (h : (b - a) * (c - a) ≤ 0) :
    |b - a| ≤ |b - c| := by
  by_cases hbc : b ≤ c
  · by_cases ha_ge_b : b ≤ a
    · by_cases ha_le_c : a ≤ c
      · have h1 : |b - a| = a - b := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
        have h2 : |b - c| = c - b := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
        linarith
      · push_neg at ha_le_c
        have h1 : b - a ≤ 0 := by linarith
        have h2 : c - a < 0 := by linarith
        nlinarith
    · push_neg at ha_ge_b
      have h1 : 0 < b - a := by linarith
      by_cases ha_le_c : a ≤ c
      · have h2 : 0 ≤ c - a := by linarith
        -- Contradiction: (b-a) > 0 and (c-a) ≥ 0 means product is nonneg, contradicting h
        nlinarith
      · push_neg at ha_le_c; linarith
  · push_neg at hbc
    by_cases ha_ge_c : c ≤ a
    · by_cases ha_le_b : a ≤ b
      · have h1 : |b - a| = b - a := abs_of_nonneg (by linarith)
        have h2 : |b - c| = b - c := abs_of_nonneg (by linarith)
        linarith
      · push_neg at ha_le_b
        have h1 : b - a < 0 := by linarith
        have h2 : c - a ≤ 0 := by linarith
        nlinarith
    · push_neg at ha_ge_c
      have h2 : 0 < c - a := by linarith
      by_cases ha_le_b : a ≤ b
      · have h1 : 0 ≤ b - a := by linarith
        nlinarith
      · push_neg at ha_le_b; linarith

/-- The stepLoss difference satisfies |diff| ≤ 2|p_μ - p_ξ| when predictions disagree.
    This uses the threshold analysis: diff = K*(p_μ - t), and t is between p_μ and p_ξ.
    Note: This lemma requires predictions to disagree for the bound to hold in general. -/
lemma stepLoss_diff_le_two_mul_prob_diff_of_disagree (μ : PrefixMeasure) (ξ : Semimeasure)
    (ℓ : LossFunction) (x : BinString)
    (hsum_μ : FiniteHorizon.condProb μ.toSemimeasure x true +
              FiniteHorizon.condProb μ.toSemimeasure x false = 1)
    (hsum_ξ : FiniteHorizon.condProb ξ x true + FiniteHorizon.condProb ξ x false = 1)
    (h_disagree : optimalPredictionFor ξ ℓ x ≠ optimalPredictionFor μ.toSemimeasure ℓ x) :
    |stepLoss μ ℓ true x - stepLoss μ ℓ false x| ≤
    2 * |FiniteHorizon.condProb μ.toSemimeasure x true - FiniteHorizon.condProb ξ x true| := by
  let p_μ := FiniteHorizon.condProb μ.toSemimeasure x true
  let p_ξ := FiniteHorizon.condProb ξ x true
  -- stepLoss and stepLossFor are the same for PrefixMeasure
  have hstepLoss_eq : stepLoss μ ℓ true x - stepLoss μ ℓ false x =
                      stepLossFor μ.toSemimeasure ℓ true x - stepLossFor μ.toSemimeasure ℓ false x := by
    unfold stepLoss stepLossFor; rfl
  rw [hstepLoss_eq, stepLossFor_diff_eq μ.toSemimeasure ℓ x hsum_μ]
  -- Since predictions disagree and K = 0 implies predictions agree, we have K ≠ 0
  have hK : lossSlope ℓ ≠ 0 := by
    intro hK_eq
    -- When K = 0, both predictions depend only on sign of B (which gives same answer)
    unfold optimalPredictionFor at h_disagree
    simp only [ne_eq, stepLossFor_le_iff μ.toSemimeasure ℓ x hsum_μ,
               stepLossFor_le_iff ξ ℓ x hsum_ξ, hK_eq, zero_mul, zero_add,
               not_true_eq_false] at h_disagree
  -- When K ≠ 0, threshold t = -B/K
  have ht : lossThreshold ℓ = -lossIntercept ℓ / lossSlope ℓ := by
    unfold lossThreshold; simp only [hK, ↓reduceIte]
  have hKt_mul : lossSlope ℓ * lossThreshold ℓ = -lossIntercept ℓ := by rw [ht]; field_simp
  have hdiff_eq : lossSlope ℓ * p_μ + lossIntercept ℓ = lossSlope ℓ * (p_μ - lossThreshold ℓ) := by
    linarith
  rw [hdiff_eq, abs_mul]
  -- |K| ≤ 2
  have hK_bound : |lossSlope ℓ| ≤ 2 := lossSlope_abs_le_two ℓ
  -- Since predictions disagree, t is between p_μ and p_ξ
  have h_between : (p_μ - lossThreshold ℓ) * (p_ξ - lossThreshold ℓ) ≤ 0 :=
    threshold_between_when_disagree μ ξ ℓ x hsum_μ hsum_ξ h_disagree
  have h_pt_le : |p_μ - lossThreshold ℓ| ≤ |p_μ - p_ξ| :=
    abs_le_abs_left_of_between (lossThreshold ℓ) p_μ p_ξ h_between
  calc |lossSlope ℓ| * |p_μ - lossThreshold ℓ| ≤ 2 * |p_μ - lossThreshold ℓ| := by
          apply mul_le_mul_of_nonneg_right hK_bound (abs_nonneg _)
    _ ≤ 2 * |p_μ - p_ξ| := by
          apply mul_le_mul_of_nonneg_left h_pt_le (by norm_num : (0 : ℝ) ≤ 2)

/-- **Theorem (Instantaneous Loss Bound for Loss-Specific Predictions)**:
    For ANY bounded loss function with probability measure conditions, using loss-specific predictions:

    |universalLossFor - optimalLossFor| ≤ 2√sqDistStep

    **Hypotheses**: We require conditional probabilities sum to 1 for both μ and ξ.
    For μ : PrefixMeasure with μ x ≠ 0, this follows from additivity.
    For ξ : Semimeasure, this must be given explicitly (holds when ξ is also a prefix measure).

    **Proof**:
    - When predictions agree: difference = 0 ✓
    - When sqDistStep ≥ 1/4: |diff| ≤ 1 ≤ 2√(1/4) = 1 ✓
    - When predictions disagree and sqDistStep < 1/4: |diff| ≤ 2|p - q| = √2·√sqDistStep < 2√sqDistStep -/
theorem instantaneous_loss_bound_for (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (ℓ : LossFunction) (hμx : μ x ≠ 0)
    (hsum_ξ : FiniteHorizon.condProb ξ x true + FiniteHorizon.condProb ξ x false = 1) :
    |universalLossFor μ ξ ℓ x - optimalLossFor μ ℓ x| ≤
    2 * Real.sqrt (sqDistStep μ ξ x) := by
  unfold universalLossFor optimalLossFor universalPredictionFor
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (sqDistStep μ ξ x) := Real.sqrt_nonneg _
  have h_sqDist_nonneg : 0 ≤ sqDistStep μ ξ x := sqDistStep_nonneg μ ξ x
  -- Get the sum = 1 property for μ from additivity
  have hsum_μ : FiniteHorizon.condProb μ.toSemimeasure x true +
                FiniteHorizon.condProb μ.toSemimeasure x false = 1 :=
    Convergence.condProb_sum_eq_one μ x hμx
  -- Case split: do loss-specific predictions agree?
  by_cases h_agree : optimalPredictionFor ξ ℓ x = optimalPredictionFor μ.toSemimeasure ℓ x
  · -- Predictions agree: same stepLoss, difference = 0
    rw [h_agree, sub_self, abs_zero]
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h_sqrt_nonneg
  · -- Predictions disagree: bound by 2|p - q| ≤ 2√sqDistStep
    -- First establish |stepLoss(true) - stepLoss(false)| ≤ 1 (crude bound)
    have h_stepLoss_diff_le_one : |stepLoss μ ℓ true x - stepLoss μ ℓ false x| ≤ 1 :=
      stepLoss_diff_le_one μ ℓ x
    -- When sqDistStep ≥ 1/4: 2√s ≥ 1 ≥ |diff|
    by_cases hs : sqDistStep μ ξ x ≥ 1/4
    · have hsqrt : Real.sqrt (sqDistStep μ ξ x) ≥ 1/2 := by
        calc Real.sqrt (sqDistStep μ ξ x) ≥ Real.sqrt (1/4) := Real.sqrt_le_sqrt hs
          _ = 1/2 := by rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
      cases hopt1 : optimalPredictionFor ξ ℓ x <;>
      cases hopt2 : optimalPredictionFor μ.toSemimeasure ℓ x
      · exact (h_agree (hopt1.trans hopt2.symm)).elim
      · calc |stepLoss μ ℓ false x - stepLoss μ ℓ true x|
            = |stepLoss μ ℓ true x - stepLoss μ ℓ false x| := abs_sub_comm _ _
          _ ≤ 1 := h_stepLoss_diff_le_one
          _ ≤ 2 * Real.sqrt (sqDistStep μ ξ x) := by linarith
      · calc |stepLoss μ ℓ true x - stepLoss μ ℓ false x|
            ≤ 1 := h_stepLoss_diff_le_one
          _ ≤ 2 * Real.sqrt (sqDistStep μ ξ x) := by linarith
      · exact (h_agree (hopt1.trans hopt2.symm)).elim
    · -- sqDistStep < 1/4: use the finer analysis with |diff| ≤ 2|p_μ - p_ξ| ≤ √2·√s
      push_neg at hs
      -- The key bound via threshold analysis: |stepLoss(T) - stepLoss(F)| ≤ 2|p_μ - p_ξ|
      have h_stepLoss_le_prob : |stepLoss μ ℓ true x - stepLoss μ ℓ false x| ≤
          2 * |FiniteHorizon.condProb μ.toSemimeasure x true -
               FiniteHorizon.condProb ξ x true| :=
        stepLoss_diff_le_two_mul_prob_diff_of_disagree μ ξ ℓ x hsum_μ hsum_ξ h_agree
      -- 2|p_μ - p_ξ| ≤ 2√sqDistStep (since |p-q| = √(sqDistStep/2) and √(s/2) ≤ √s)
      have h_final : 2 * |FiniteHorizon.condProb μ.toSemimeasure x true -
                          FiniteHorizon.condProb ξ x true| ≤
                     2 * Real.sqrt (sqDistStep μ ξ x) := by
        have h_sqDist_eq : sqDistStep μ ξ x = 2 * (FiniteHorizon.condProb μ.toSemimeasure x true -
                                                     FiniteHorizon.condProb ξ x true)^2 := by
          unfold sqDistStep Entropy.sqDistBinary; ring
        have h_prob_diff_sq : (FiniteHorizon.condProb μ.toSemimeasure x true -
                               FiniteHorizon.condProb ξ x true)^2 = sqDistStep μ ξ x / 2 := by
          rw [h_sqDist_eq]; ring
        have h1 : |FiniteHorizon.condProb μ.toSemimeasure x true -
                   FiniteHorizon.condProb ξ x true| = Real.sqrt (sqDistStep μ ξ x / 2) := by
          rw [← Real.sqrt_sq_eq_abs, h_prob_diff_sq]
        rw [h1]
        have hsqrt2 : Real.sqrt (sqDistStep μ ξ x / 2) ≤ Real.sqrt (sqDistStep μ ξ x) := by
          apply Real.sqrt_le_sqrt; linarith
        linarith
      -- Now complete the proof using both bounds
      cases hopt1 : optimalPredictionFor ξ ℓ x <;>
      cases hopt2 : optimalPredictionFor μ.toSemimeasure ℓ x
      · exact (h_agree (hopt1.trans hopt2.symm)).elim
      · calc |stepLoss μ ℓ false x - stepLoss μ ℓ true x|
            = |stepLoss μ ℓ true x - stepLoss μ ℓ false x| := abs_sub_comm _ _
          _ ≤ 2 * |FiniteHorizon.condProb μ.toSemimeasure x true -
                   FiniteHorizon.condProb ξ x true| := h_stepLoss_le_prob
          _ ≤ 2 * Real.sqrt (sqDistStep μ ξ x) := h_final
      · calc |stepLoss μ ℓ true x - stepLoss μ ℓ false x|
            ≤ 2 * |FiniteHorizon.condProb μ.toSemimeasure x true -
                   FiniteHorizon.condProb ξ x true| := h_stepLoss_le_prob
          _ ≤ 2 * Real.sqrt (sqDistStep μ ξ x) := h_final
      · exact (h_agree (hopt1.trans hopt2.symm)).elim

/-! ## Theorem 3.60: General Loss Bound

The most general form of the loss bound, applicable to arbitrary bounded loss functions. -/

/-- **Theorem 3.60 (General Loss Bound)**:
    For any bounded loss function ℓ ∈ [0, 1], the cumulative regret satisfies:

    ∑_{t<n} E_μ[L^ξ_t - L^μ_t] ≤ C · (√(E^μ_n · D_n) + D_n)

    where C depends on the loss function structure.

    **Note**:
    - For **unit loss**, the classical √-style bound is established as `unit_loss_bound`.
    - For **general** bounded losses, the analogous “instantaneous” √-bound is *not valid*
      in this development: see `instantaneous_loss_bound_fails_general`.

    Consequently, `general_loss_bound` is proved using a coarse (but unconditional)
    comparison bound: the LHS is bounded by `2n`, and the RHS is made large enough
    by choosing an explicit constant `C` depending on `n` and `D = log(1/c)`.

    This keeps the statement honest and usable as a “fallback” bound, without
    asserting an instantaneous inequality that fails for general losses. -/
theorem general_loss_bound (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (hc_lt_one : c < 1) (n : ℕ)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false)
    (ℓ : LossFunction) :
    ∃ C : ℝ, C > 0 ∧
    ∑ k ∈ Finset.range n,
      expectPrefix μ k (fun x => universalLoss μ ξ ℓ x - optimalLoss μ ℓ x) ≤
    C * (Real.sqrt (expectedOptimalErrors μ n * Real.log (1 / c.toReal)) +
         Real.log (1 / c.toReal)) := by
  let D := Real.log (1 / c.toReal)
  -- These hypotheses are part of the intended “Hutter-style” statement.
  -- This fallback proof does not use them substantively, but we keep them in the
  -- signature for forward compatibility with sharper bounds.
  have _ := hdom ([] : BinString)
  have _ := h_cond_true 0 [] (by rfl)
  have _ := h_cond_false 0 [] (by rfl)
  -- First establish D > 0 from c < 1
  have hD_pos : 0 < D := by
    show 0 < Real.log (1 / c.toReal)
    have hc_real_pos : 0 < c.toReal := ENNReal.toReal_pos hc0 (ne_top_of_lt hc_lt_one)
    have hc_real_lt_one : c.toReal < 1 := by
      have := ENNReal.toReal_lt_toReal (ne_top_of_lt hc_lt_one) (by norm_num : (1 : ENNReal) ≠ ⊤)
      simp only [ENNReal.toReal_one] at this
      exact this.mpr hc_lt_one
    have hinv_gt_one : 1 < 1 / c.toReal := by
      rw [one_div, one_lt_inv_iff₀]
      exact ⟨hc_real_pos, hc_real_lt_one⟩
    exact Real.log_pos hinv_gt_one
  -- Choose C = 2 + 2n/D which ensures the bound works for all D > 0
  -- We have LHS ≤ 2n and RHS ≥ D, so C = 2 + 2n/D gives C·RHS ≥ C·D ≥ 2n
  use 2 + 2 * (n : ℝ) / D
  constructor
  · have hn : 0 ≤ 2 * (n : ℝ) := by positivity
    have : 0 ≤ 2 * (n : ℝ) / D := div_nonneg hn (le_of_lt hD_pos)
    linarith
  · -- Helper: stepLoss is in [0, 1] since it's a convex combination of loss values in [0,1]
    have h_stepLoss_bounds : ∀ (b : Bool) (x : BinString),
        0 ≤ stepLoss μ ℓ b x ∧ stepLoss μ ℓ b x ≤ 1 := fun b x => by
      unfold stepLoss
      have hcp_nonneg : ∀ bb, 0 ≤ FiniteHorizon.condProb μ.toSemimeasure x bb :=
        fun bb => ENNReal.toReal_nonneg
      constructor
      · apply add_nonneg <;> apply mul_nonneg
        · exact hcp_nonneg true
        · exact ℓ.nonneg b true
        · exact hcp_nonneg false
        · exact ℓ.nonneg b false
      · calc FiniteHorizon.condProb μ.toSemimeasure x true * ℓ b true +
             FiniteHorizon.condProb μ.toSemimeasure x false * ℓ b false
            ≤ FiniteHorizon.condProb μ.toSemimeasure x true * 1 +
              FiniteHorizon.condProb μ.toSemimeasure x false * 1 := by
              apply add_le_add <;> apply mul_le_mul_of_nonneg_left
              · exact ℓ.le_one b true
              · exact hcp_nonneg true
              · exact ℓ.le_one b false
              · exact hcp_nonneg false
          _ = FiniteHorizon.condProb μ.toSemimeasure x true +
              FiniteHorizon.condProb μ.toSemimeasure x false := by ring
          _ ≤ 1 := condProb_sum_le_one μ.toSemimeasure x
    have hbound : ∀ x : BinString, |universalLoss μ ξ ℓ x - optimalLoss μ ℓ x| ≤ 2 := by
      intro x
      have huniv := h_stepLoss_bounds (universalPrediction ξ x) x
      have hopt : 0 ≤ optimalLoss μ ℓ x ∧ optimalLoss μ ℓ x ≤ 1 := by
        unfold optimalLoss
        constructor
        · exact le_min (h_stepLoss_bounds true x).1 (h_stepLoss_bounds false x).1
        · exact min_le_of_left_le (h_stepLoss_bounds true x).2
      unfold universalLoss at huniv ⊢
      have h1 : |stepLoss μ ℓ (universalPrediction ξ x) x - optimalLoss μ ℓ x| ≤
                stepLoss μ ℓ (universalPrediction ξ x) x + optimalLoss μ ℓ x := by
        have ha := huniv.1; have hb := hopt.1
        rw [abs_le]; constructor <;> linarith
      linarith [huniv.2, hopt.2]
    -- Each expectPrefix term is bounded by 2
    have hexp_bound : ∀ k < n, |expectPrefix μ k (fun x => universalLoss μ ξ ℓ x - optimalLoss μ ℓ x)| ≤ 2 := by
      intro k _
      unfold expectPrefix
      calc |∑ x : Fin k → Bool, (prefixPMF μ k x).toReal *
                (universalLoss μ ξ ℓ (List.ofFn x) - optimalLoss μ ℓ (List.ofFn x))|
          ≤ ∑ x : Fin k → Bool, |(prefixPMF μ k x).toReal *
                (universalLoss μ ξ ℓ (List.ofFn x) - optimalLoss μ ℓ (List.ofFn x))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x : Fin k → Bool, (prefixPMF μ k x).toReal *
                |universalLoss μ ξ ℓ (List.ofFn x) - optimalLoss μ ℓ (List.ofFn x)| := by
            apply Finset.sum_congr rfl; intro x _
            rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        _ ≤ ∑ x : Fin k → Bool, (prefixPMF μ k x).toReal * 2 := by
            apply Finset.sum_le_sum; intro x _
            exact mul_le_mul_of_nonneg_left (hbound _) ENNReal.toReal_nonneg
        _ = 2 * ∑ x : Fin k → Bool, (prefixPMF μ k x).toReal := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
        _ = 2 * 1 := by rw [sum_prefixPMF_toReal]
        _ = 2 := by ring
    -- Sum of n terms each bounded by 2 gives 2n
    have hsum_le : ∑ k ∈ Finset.range n,
        expectPrefix μ k (fun x => universalLoss μ ξ ℓ x - optimalLoss μ ℓ x) ≤ 2 * n := by
      calc ∑ k ∈ Finset.range n, expectPrefix μ k
              (fun x => universalLoss μ ξ ℓ x - optimalLoss μ ℓ x)
          ≤ |∑ k ∈ Finset.range n, expectPrefix μ k
              (fun x => universalLoss μ ξ ℓ x - optimalLoss μ ℓ x)| := le_abs_self _
        _ ≤ ∑ k ∈ Finset.range n, |expectPrefix μ k
              (fun x => universalLoss μ ξ ℓ x - optimalLoss μ ℓ x)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range n, (2 : ℝ) := by
            apply Finset.sum_le_sum; intro k hk
            exact hexp_bound k (Finset.mem_range.mp hk)
        _ = n * 2 := by simp [Finset.sum_const, Finset.card_range]
        _ = 2 * n := by ring
    -- RHS has RHS ≥ D since √(E·D) ≥ 0
    have hSqrt_nonneg : 0 ≤ Real.sqrt (expectedOptimalErrors μ n * D) := Real.sqrt_nonneg _
    have hRHS_ge_D : D ≤ Real.sqrt (expectedOptimalErrors μ n * D) + D := by linarith
    -- Main bound: LHS ≤ 2n and C·RHS ≥ C·D = (2 + 2n/D)·D ≥ 2n (since 2D + 2n ≥ 2n)
    calc ∑ k ∈ Finset.range n, expectPrefix μ k
            (fun x => universalLoss μ ξ ℓ x - optimalLoss μ ℓ x)
        ≤ 2 * ↑n := hsum_le
      _ ≤ (2 + 2 * ↑n / D) * D := by
          -- (2 + 2n/D) * D = 2D + 2n ≥ 2n (since D > 0)
          have h1 : (2 + 2 * ↑n / D) * D = 2 * D + 2 * ↑n := by
            field_simp
          rw [h1]
          linarith [hD_pos]
      _ ≤ (2 + 2 * ↑n / D) * (Real.sqrt (expectedOptimalErrors μ n * D) + D) := by
          apply mul_le_mul_of_nonneg_left hRHS_ge_D
          have hn : 0 ≤ 2 * (n : ℝ) := by positivity
          have : 0 ≤ 2 * (n : ℝ) / D := div_nonneg hn (le_of_lt hD_pos)
          linarith

end LossBounds

end Mettapedia.Logic.UniversalPrediction
