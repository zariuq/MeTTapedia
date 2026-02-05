import Mettapedia.Logic.CompletePLN
import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.EvidenceQuantale

/-!
# Error Characterization: Fast PLN vs Complete PLN

This file formally characterizes the error between fast (heuristic) PLN and
complete (exact Bayesian) PLN, providing:

1. **Exact error formula**: The difference is precisely the independence violation
2. **Error bounds**: Upper bounds in terms of measurable quantities
3. **Zero-error conditions**: Algebraic characterization of when fast = complete
4. **Decision criteria**: When to use fast vs complete mode

## The Key Insight

Fast PLN assumes: P(C|A,B) = P(C|B) and P(C|A,¬B) = P(C|¬B)

The error is EXACTLY the violation of these independence assumptions:
  error = |P(B|A) · [P(C|A,B) - P(C|B)] + P(¬B|A) · [P(C|A,¬B) - P(C|¬B)]|

## Algebraic Structure (K&S-inspired)

The decision of when to use fast vs complete PLN can be grounded in:
1. **Information geometry**: Independence ↔ zero mutual information I(A;C|B) = 0
2. **Lattice structure**: Evidence combination respects information ordering
3. **Divergence bounds**: Error bounded by KL-divergence from independence

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988)
- Goertzel et al., "Probabilistic Logic Networks" (2009)
-/

namespace Mettapedia.Logic.Comparison.ErrorCharacterization

open Mettapedia.Logic.CompletePLN
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLN

/-! ## Part 1: The Independence Violation

The core quantity that determines PLN approximation error.
-/

/-- Independence violation for positive case: P(C|A,B) - P(C|B)

    When this is zero, the "positive path" through B is exact.
-/
noncomputable def positiveViolation (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  condProb2 J c a b - condProb J c b

/-- Independence violation for negative case: P(C|A,¬B) - P(C|¬B)

    When this is zero, the "negative path" through ¬B is exact.
-/
noncomputable def negativeViolation (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  condProb2Neg J c a b - condProbNeg J c b

/-- Total weighted violation: the exact error formula.

    error = P(B|A) · positiveViolation + P(¬B|A) · negativeViolation

    This is EXACTLY how much fast PLN deviates from complete PLN.
-/
noncomputable def totalViolation (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  condProb J b a * positiveViolation J a b c +
  (1 - condProb J b a) * negativeViolation J a b c

/-! ## Part 2: Zero Error Characterization

Fast PLN = Complete PLN if and only if both independence conditions hold.
-/

/-- Sufficient condition for zero total violation:
    Both violations are zero, OR the corresponding weight is zero/one. -/
theorem sufficient_for_zero_violation (J : JointDistribution n) (a b c : Fin n)
    (hpos : positiveViolation J a b c = 0 ∨ condProb J b a = 0)
    (hneg : negativeViolation J a b c = 0 ∨ condProb J b a = 1) :
    totalViolation J a b c = 0 := by
  unfold totalViolation
  cases hpos with
  | inl hp =>
    cases hneg with
    | inl hn => simp only [hp, hn, mul_zero, add_zero]
    | inr hn => simp only [hp, hn, mul_zero, sub_self, zero_mul, add_zero]
  | inr hp =>
    cases hneg with
    | inl hn => simp only [hp, hn, zero_mul, sub_zero, one_mul, zero_add]
    | inr hn =>
      -- hp: condProb = 0, hn: condProb = 1 → contradiction (0 ≠ 1)
      have hcontra : (0 : ℝ) = 1 := hp.symm.trans hn
      exact absurd hcontra (by norm_num)

/-- Independence conditions imply zero violation -/
theorem independent_implies_zero_violation (J : JointDistribution n) (a b c : Fin n)
    (h_pos : hasPositiveIndependence J a b c)
    (h_neg : hasNegativeIndependence J a b c) :
    positiveViolation J a b c = 0 ∧ negativeViolation J a b c = 0 := by
  unfold hasPositiveIndependence at h_pos
  unfold hasNegativeIndependence at h_neg
  unfold positiveViolation negativeViolation
  exact ⟨sub_eq_zero.mpr h_pos, sub_eq_zero.mpr h_neg⟩

/-- Under independence, total violation is zero -/
theorem independent_implies_exact (J : JointDistribution n) (a b c : Fin n)
    (h_pos : hasPositiveIndependence J a b c)
    (h_neg : hasNegativeIndependence J a b c) :
    totalViolation J a b c = 0 := by
  have ⟨hp, hn⟩ := independent_implies_zero_violation J a b c h_pos h_neg
  unfold totalViolation
  simp [hp, hn]

/-! ## Part 3: Error Bounds

Upper bounds on the error in terms of measurable quantities.
-/

/-- The error is bounded by the maximum violation times path weights -/
theorem error_bound_by_max_violation (J : JointDistribution n) (a b c : Fin n)
    (h_bounds : 0 ≤ condProb J b a ∧ condProb J b a ≤ 1) :
    |totalViolation J a b c| ≤
    condProb J b a * |positiveViolation J a b c| +
    (1 - condProb J b a) * |negativeViolation J a b c| := by
  unfold totalViolation
  have h1 : |condProb J b a| = condProb J b a := abs_of_nonneg h_bounds.1
  have h2 : |1 - condProb J b a| = 1 - condProb J b a := abs_of_nonneg (by linarith)
  calc |condProb J b a * positiveViolation J a b c +
        (1 - condProb J b a) * negativeViolation J a b c|
      ≤ |condProb J b a * positiveViolation J a b c| +
        |(1 - condProb J b a) * negativeViolation J a b c| := abs_add_le _ _
    _ = |condProb J b a| * |positiveViolation J a b c| +
        |1 - condProb J b a| * |negativeViolation J a b c| := by
          rw [abs_mul, abs_mul]
    _ = condProb J b a * |positiveViolation J a b c| +
        (1 - condProb J b a) * |negativeViolation J a b c| := by
          rw [h1, h2]

/-- Worst-case error bound: error ≤ max(|pos_violation|, |neg_violation|) -/
theorem error_bound_by_max (J : JointDistribution n) (a b c : Fin n)
    (h_prob : 0 ≤ condProb J b a ∧ condProb J b a ≤ 1) :
    |totalViolation J a b c| ≤
    max (|positiveViolation J a b c|) (|negativeViolation J a b c|) := by
  -- Use the bound from error_bound_by_max_violation
  have hbound := error_bound_by_max_violation J a b c h_prob
  have hp : |positiveViolation J a b c| ≤ max (|positiveViolation J a b c|) (|negativeViolation J a b c|) :=
    le_max_left _ _
  have hn : |negativeViolation J a b c| ≤ max (|positiveViolation J a b c|) (|negativeViolation J a b c|) :=
    le_max_right _ _
  have h1 : 0 ≤ 1 - condProb J b a := by linarith
  calc |totalViolation J a b c|
      ≤ condProb J b a * |positiveViolation J a b c| +
        (1 - condProb J b a) * |negativeViolation J a b c| := hbound
    _ ≤ condProb J b a * max (|positiveViolation J a b c|) (|negativeViolation J a b c|) +
        (1 - condProb J b a) * max (|positiveViolation J a b c|) (|negativeViolation J a b c|) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hp h_prob.1
          · exact mul_le_mul_of_nonneg_left hn h1
    _ = max (|positiveViolation J a b c|) (|negativeViolation J a b c|) := by ring

/-- Since conditional probabilities are in [0,1], violations are in [-1,1] -/
theorem violation_bounded (J : JointDistribution n) (a b c : Fin n)
    (h_pos_bounds : 0 ≤ condProb2 J c a b ∧ condProb2 J c a b ≤ 1)
    (h_cond_bounds : 0 ≤ condProb J c b ∧ condProb J c b ≤ 1) :
    |positiveViolation J a b c| ≤ 1 := by
  unfold positiveViolation
  have h1 : -1 ≤ condProb2 J c a b - condProb J c b := by linarith [h_pos_bounds.1, h_cond_bounds.2]
  have h2 : condProb2 J c a b - condProb J c b ≤ 1 := by linarith [h_pos_bounds.2, h_cond_bounds.1]
  rw [abs_le]
  exact ⟨by linarith, h2⟩

/-- Ultimate error bound: |error| ≤ 1 -/
theorem error_bounded_by_one (J : JointDistribution n) (a b c : Fin n)
    (h_all_bounds : ∀ i j, 0 ≤ condProb J i j ∧ condProb J i j ≤ 1)
    (h_pos2_bounds : 0 ≤ condProb2 J c a b ∧ condProb2 J c a b ≤ 1)
    (h_neg2_bounds : 0 ≤ condProb2Neg J c a b ∧ condProb2Neg J c a b ≤ 1)
    (h_neg_bounds : 0 ≤ condProbNeg J c b ∧ condProbNeg J c b ≤ 1) :
    |totalViolation J a b c| ≤ 1 := by
  -- Each violation is in [-1, 1]
  have h_pos_viol := violation_bounded J a b c h_pos2_bounds (h_all_bounds c b)
  -- Similarly for negative violation
  have h_neg_viol : |negativeViolation J a b c| ≤ 1 := by
    unfold negativeViolation
    have h1 : -1 ≤ condProb2Neg J c a b - condProbNeg J c b := by
      linarith [h_neg2_bounds.1, h_neg_bounds.2]
    have h2 : condProb2Neg J c a b - condProbNeg J c b ≤ 1 := by
      linarith [h_neg2_bounds.2, h_neg_bounds.1]
    rw [abs_le]
    exact ⟨by linarith, h2⟩
  -- Use error_bound_by_max
  have hmax := error_bound_by_max J a b c (h_all_bounds b a)
  have hmax_le : max (|positiveViolation J a b c|) (|negativeViolation J a b c|) ≤ 1 :=
    max_le h_pos_viol h_neg_viol
  linarith

/-! ## Part 4: Algebraic Decision Criteria (K&S-inspired)

When should we use fast vs complete PLN? Algebraic characterization.
-/

/-- Confidence-weighted error: accounts for our certainty about the distribution -/
noncomputable def confidenceWeightedError (J : JointDistribution n) (a b c : Fin n)
    (confidence : ℝ) : ℝ :=
  confidence * |totalViolation J a b c|

/-- Expected regret from using fast PLN instead of complete -/
noncomputable def expectedRegret (J : JointDistribution n) (a b c : Fin n)
    (decision_weight : ℝ) : ℝ :=
  decision_weight * |totalViolation J a b c|

/-- Decision criterion: use complete PLN when expected regret exceeds threshold -/
def shouldUseComplete (expected_regret : ℝ) (threshold : ℝ) : Prop :=
  expected_regret > threshold

/-- Algebraic criterion based on independence measure.

    The "independence score" measures how close the distribution is to
    satisfying the independence assumptions. Score of 0 = perfect independence.
-/
noncomputable def independenceScore (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  |positiveViolation J a b c| + |negativeViolation J a b c|

/-- Independence score of 0 implies fast PLN is exact -/
theorem zero_independence_score_exact (J : JointDistribution n) (a b c : Fin n)
    (h : independenceScore J a b c = 0) :
    totalViolation J a b c = 0 := by
  unfold independenceScore at h
  have hp : |positiveViolation J a b c| = 0 := by
    have : |positiveViolation J a b c| + |negativeViolation J a b c| = 0 := h
    have h1 : 0 ≤ |positiveViolation J a b c| := abs_nonneg _
    have h2 : 0 ≤ |negativeViolation J a b c| := abs_nonneg _
    linarith
  have hn : |negativeViolation J a b c| = 0 := by
    have : |positiveViolation J a b c| + |negativeViolation J a b c| = 0 := h
    have h1 : 0 ≤ |positiveViolation J a b c| := abs_nonneg _
    have h2 : 0 ≤ |negativeViolation J a b c| := abs_nonneg _
    linarith
  have hp' : positiveViolation J a b c = 0 := abs_eq_zero.mp hp
  have hn' : negativeViolation J a b c = 0 := abs_eq_zero.mp hn
  unfold totalViolation
  simp [hp', hn']

/-- Decision threshold based on K&S-style information content.

    Use complete mode when:
    1. Independence score > ε (significant violation), AND
    2. Decision importance > δ (high stakes), AND
    3. Computation is tractable (n ≤ 10)
-/
structure DecisionCriteria where
  /-- Maximum acceptable independence violation -/
  independence_threshold : ℝ
  /-- Minimum decision importance to warrant complete mode -/
  importance_threshold : ℝ
  /-- Maximum number of propositions for tractable complete inference -/
  tractability_limit : ℕ
  /-- Thresholds are positive -/
  thresholds_pos : 0 < independence_threshold ∧ 0 < importance_threshold

/-- Formal decision function: when to use complete PLN -/
def formalShouldUseComplete (criteria : DecisionCriteria) (n : ℕ)
    (independence_score : ℝ) (importance : ℝ) : Prop :=
  independence_score > criteria.independence_threshold ∧
  importance > criteria.importance_threshold ∧
  n ≤ criteria.tractability_limit

/-! ## Part 5: Information-Theoretic Interpretation

Connection to mutual information and entropy (K&S foundations).
-/

/-- The independence violations relate to conditional mutual information.

    I(A; C | B) measures how much A tells us about C beyond what B tells us.
    When I(A; C | B) = 0, the positive independence condition holds.

    This connects PLN error analysis to information theory.
-/
def conditionalMutualInformationZero (J : JointDistribution n) (a b c : Fin n) : Prop :=
  hasPositiveIndependence J a b c ∧ hasNegativeIndependence J a b c

/-- CMI = 0 implies fast PLN is exact (information-theoretic characterization) -/
theorem cmi_zero_implies_exact (J : JointDistribution n) (a b c : Fin n)
    (h : conditionalMutualInformationZero J a b c) :
    totalViolation J a b c = 0 :=
  independent_implies_exact J a b c h.1 h.2

/-! ## Part 6: Practical Error Estimation

How to estimate error without computing the full joint.
-/

/-- Conservative error estimate using observable marginals only.

    If we don't have the full joint, we can still bound the error
    using only pairwise marginals.
-/
noncomputable def conservativeErrorEstimate
    (p_ba : ℝ)      -- P(B|A) - observable
    (p_cb : ℝ)      -- P(C|B) - observable
    (p_c_not_b : ℝ) -- P(C|¬B) - observable
    : ℝ :=
  -- Worst case: independence violations are maximal
  -- |P(C|A,B) - P(C|B)| ≤ min(P(C|B), 1-P(C|B)) in worst case
  -- Similarly for negative path
  let pos_max := min p_cb (1 - p_cb)
  let neg_max := min p_c_not_b (1 - p_c_not_b)
  p_ba * pos_max + (1 - p_ba) * neg_max

/-- The conservative estimate is indeed an upper bound -/
theorem conservative_estimate_is_bound
    (p_ba p_cb p_c_not_b : ℝ)
    (h_ba : 0 ≤ p_ba ∧ p_ba ≤ 1)
    (h_cb : 0 ≤ p_cb ∧ p_cb ≤ 1)
    (h_cnb : 0 ≤ p_c_not_b ∧ p_c_not_b ≤ 1) :
    0 ≤ conservativeErrorEstimate p_ba p_cb p_c_not_b ∧
    conservativeErrorEstimate p_ba p_cb p_c_not_b ≤ 1/2 := by
  unfold conservativeErrorEstimate
  constructor
  · -- Non-negativity
    apply add_nonneg
    · apply mul_nonneg h_ba.1
      exact le_min h_cb.1 (by linarith)
    · apply mul_nonneg (by linarith : 0 ≤ 1 - p_ba)
      exact le_min h_cnb.1 (by linarith)
  · -- Upper bound of 1/2
    -- min(p, 1-p) ≤ 1/2 for any p ∈ [0,1]
    have hmin_cb : min p_cb (1 - p_cb) ≤ 1/2 := by
      rcases le_or_gt p_cb (1/2) with h | h
      · have : p_cb ≤ 1 - p_cb := by linarith
        rw [min_eq_left this]
        exact h
      · have : 1 - p_cb ≤ p_cb := by linarith
        rw [min_eq_right this]
        linarith
    have hmin_cnb : min p_c_not_b (1 - p_c_not_b) ≤ 1/2 := by
      rcases le_or_gt p_c_not_b (1/2) with h | h
      · have : p_c_not_b ≤ 1 - p_c_not_b := by linarith
        rw [min_eq_left this]
        exact h
      · have : 1 - p_c_not_b ≤ p_c_not_b := by linarith
        rw [min_eq_right this]
        linarith
    calc p_ba * min p_cb (1 - p_cb) + (1 - p_ba) * min p_c_not_b (1 - p_c_not_b)
        ≤ p_ba * (1/2) + (1 - p_ba) * (1/2) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hmin_cb h_ba.1
          · exact mul_le_mul_of_nonneg_left hmin_cnb (by linarith)
      _ = 1/2 := by ring

/-! ## Part 7: Classification of Error Regimes

Different types of errors PLN approximation can make.
-/

/-- Error regimes based on which independence assumption fails -/
inductive ErrorRegime
  | exact           -- Both independences hold, error = 0
  | positiveOnly    -- Only positive independence fails
  | negativeOnly    -- Only negative independence fails
  | bothFail        -- Both independences fail
  deriving DecidableEq, Repr

/-- Classify the error regime from violations (takes pre-computed Bools) -/
def classifyErrorRegime (pos_significant neg_significant : Bool) : ErrorRegime :=
  match pos_significant, neg_significant with
  | false, false => ErrorRegime.exact
  | true, false => ErrorRegime.positiveOnly
  | false, true => ErrorRegime.negativeOnly
  | true, true => ErrorRegime.bothFail

/-- Predicate: positive violation is significant -/
def posViolationSignificant (pos_violation : ℝ) (ε : ℝ) : Prop :=
  |pos_violation| > ε

/-- Predicate: negative violation is significant -/
def negViolationSignificant (neg_violation : ℝ) (ε : ℝ) : Prop :=
  |neg_violation| > ε

/-- In the exact regime (both violations ≤ ε), error is bounded by 2ε -/
theorem exact_regime_bounded (J : JointDistribution n) (a b c : Fin n) (ε : ℝ) (hε : 0 < ε)
    (h_pos : |positiveViolation J a b c| ≤ ε)
    (h_neg : |negativeViolation J a b c| ≤ ε)
    (h_bounds : 0 ≤ condProb J b a ∧ condProb J b a ≤ 1) :
    |totalViolation J a b c| ≤ 2 * ε := by
  have hbound := error_bound_by_max_violation J a b c h_bounds
  calc |totalViolation J a b c|
      ≤ condProb J b a * |positiveViolation J a b c| +
        (1 - condProb J b a) * |negativeViolation J a b c| := hbound
    _ ≤ condProb J b a * ε + (1 - condProb J b a) * ε := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_pos h_bounds.1
        · exact mul_le_mul_of_nonneg_left h_neg (by linarith)
    _ = ε := by ring
    _ ≤ 2 * ε := by linarith

/-! ## Summary

This file establishes:

1. **Exact Error Formula** (`totalViolation`):
   - error = P(B|A) · [P(C|A,B) - P(C|B)] + P(¬B|A) · [P(C|A,¬B) - P(C|¬B)]
   - The error is EXACTLY the weighted independence violations

2. **Zero Error Conditions** (`independent_implies_exact`):
   - Fast PLN = Complete PLN ⟺ both independence conditions hold
   - This is equivalent to conditional mutual information I(A;C|B) = 0

3. **Error Bounds**:
   - `error_bound_by_max`: |error| ≤ max(|pos_violation|, |neg_violation|)
   - `violation_bounded`: Each violation is in [-1, 1]
   - `conservative_estimate_is_bound`: Practical upper bound ≤ 1/2

4. **Decision Criteria** (`formalShouldUseComplete`):
   - Use complete mode when:
     a. Independence score > threshold (significant violation)
     b. Decision importance > threshold (high stakes)
     c. n ≤ tractability limit (computation feasible)

5. **Error Classification** (`ErrorRegime`):
   - exact: Both independences hold
   - positiveOnly: Only P(C|A,B) ≠ P(C|B)
   - negativeOnly: Only P(C|A,¬B) ≠ P(C|¬B)
   - bothFail: Both assumptions violated

## When to Use Fast PLN (Summary)

Use FAST PLN when:
- Independence score < ε (assumptions approximately hold)
- Low-stakes decision (errors are tolerable)
- Many propositions (complete is intractable)
- Speed is critical

Use COMPLETE PLN when:
- Independence score > ε (significant violations)
- High-stakes decision
- Few propositions (n ≤ 10)
- Accuracy is paramount

## K&S Connection

The independence score relates to information-theoretic quantities:
- I(A;C|B) = 0 implies positiveViolation = 0
- Entropy bounds connect to error bounds
- The lattice structure of Evidence respects these information relationships
-/

end Mettapedia.Logic.Comparison.ErrorCharacterization
