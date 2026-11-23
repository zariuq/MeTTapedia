import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Binary decisions under posterior uncertainty

Acting incurs a fixed cost. Waiting incurs the stakes if the event occurs.
The interval laws apply to sound posterior bounds at any inference budget.
The value of a signal averages over its possible results before it is read.
-/

set_option autoImplicit false

namespace Mettapedia.DecisionTheory.ThresholdDecision

open scoped BigOperators

structure Spec where
  threshold : ℚ
  stakes : ℚ
  nonneg : 0 ≤ stakes

def Spec.act (s : Spec) (p : ℚ) : Bool := decide (s.threshold < p)

def Spec.risk (s : Spec) (p : ℚ) (act : Bool) : ℚ :=
  s.stakes * (if act then s.threshold else p)

def Spec.bayesRisk (s : Spec) (p : ℚ) : ℚ := s.stakes * min s.threshold p

def Spec.regret (s : Spec) (p : ℚ) (act : Bool) : ℚ := s.risk p act - s.bayesRisk p

theorem Spec.risk_at_act (s : Spec) (p : ℚ) : s.risk p (s.act p) = s.bayesRisk p := by
  by_cases h : s.threshold < p
  · simp [act, risk, bayesRisk, h, min_eq_left h.le]
  · simp [act, risk, bayesRisk, h, min_eq_right (le_of_not_gt h)]

theorem Spec.regret_true (s : Spec) (p : ℚ) :
    s.regret p true = s.stakes * max 0 (s.threshold - p) := by
  by_cases h : s.threshold ≤ p
  · simp [regret, risk, bayesRisk, min_eq_left h, max_eq_left (sub_nonpos.mpr h)]
  · rw [regret, risk, bayesRisk, min_eq_right (le_of_not_ge h),
      max_eq_right (sub_nonneg.mpr (le_of_not_ge h))]
    simp [mul_sub]

theorem Spec.regret_false (s : Spec) (p : ℚ) :
    s.regret p false = s.stakes * max 0 (p - s.threshold) := by
  by_cases h : p ≤ s.threshold
  · simp [regret, risk, bayesRisk, min_eq_right h, max_eq_left (sub_nonpos.mpr h)]
  · rw [regret, risk, bayesRisk, min_eq_left (le_of_not_ge h),
      max_eq_right (sub_nonneg.mpr (le_of_not_ge h))]
    simp [mul_sub]

theorem Spec.regret_nonneg (s : Spec) (p : ℚ) (action : Bool) : 0 ≤ s.regret p action := by
  cases action
  · rw [s.regret_false]
    exact mul_nonneg s.nonneg (le_max_left _ _)
  · rw [s.regret_true]
    exact mul_nonneg s.nonneg (le_max_left _ _)

/-- Two forecasts that induce the same action have zero decision regret. -/
theorem Spec.point_regret (s : Spec) (p forecast : ℚ) :
    s.regret p (s.act forecast) =
      if s.act forecast = s.act p then 0 else s.stakes * |p - s.threshold| := by
  by_cases same : s.act forecast = s.act p
  · rw [if_pos same, same, regret, s.risk_at_act, sub_self]
  · rw [if_neg same]
    cases choice : s.act forecast
    · have chooses : s.act p = true := by cases h : s.act p <;> simp_all
      have above : s.threshold < p := of_decide_eq_true chooses
      rw [s.regret_false, max_eq_right (sub_nonneg.mpr above.le),
        abs_of_nonneg (sub_nonneg.mpr above.le)]
    · have chooses : s.act p = false := by cases h : s.act p <;> simp_all
      have below : p ≤ s.threshold := le_of_not_gt (of_decide_eq_false chooses)
      rw [s.regret_true, max_eq_right (sub_nonneg.mpr below),
        abs_of_nonpos (sub_nonpos.mpr below), neg_sub]

/-- A sound interval gives a worst-case loss bound for either deterministic action. -/
def Spec.worstRegret (s : Spec) (lo hi : ℚ) (action : Bool) : ℚ :=
  s.regret (if action then lo else hi) action

theorem Spec.regret_le_worst (s : Spec) {lo hi p : ℚ} (lower : lo ≤ p) (upper : p ≤ hi)
    (action : Bool) : s.regret p action ≤ s.worstRegret lo hi action := by
  cases action
  · simp only [worstRegret, Bool.false_eq_true, if_false, regret_false]
    exact mul_le_mul_of_nonneg_left (max_le_max_left _ (sub_le_sub_right upper _)) s.nonneg
  · simp only [worstRegret, if_true, regret_true]
    exact mul_le_mul_of_nonneg_left (max_le_max_left _ (sub_le_sub_left lower _)) s.nonneg

theorem Spec.worst_attained (s : Spec) {lo hi : ℚ} (ordered : lo ≤ hi) (action : Bool) :
    ∃ p, lo ≤ p ∧ p ≤ hi ∧ s.regret p action = s.worstRegret lo hi action := by
  cases action
  · exact ⟨hi, ordered, le_rfl, rfl⟩
  · exact ⟨lo, le_rfl, ordered, rfl⟩

def Spec.minimax (s : Spec) (lo hi : ℚ) : Bool :=
  decide (s.worstRegret lo hi true < s.worstRegret lo hi false)

theorem Spec.minimax_optimal (s : Spec) (lo hi : ℚ) (action : Bool) :
    s.worstRegret lo hi (s.minimax lo hi) ≤ s.worstRegret lo hi action := by
  by_cases h : s.worstRegret lo hi true < s.worstRegret lo hi false
  · cases action
    · simpa [minimax, h] using h.le
    · simp [minimax, h]
  · cases action
    · simp [minimax, h]
    · simpa [minimax, h] using le_of_not_gt h

theorem Spec.minimax_refines (s : Spec) {lo hi lo' hi' : ℚ} (lower : lo ≤ lo')
    (upper : hi' ≤ hi) (ordered : lo' ≤ hi') :
    s.worstRegret lo' hi' (s.minimax lo' hi') ≤ s.worstRegret lo hi (s.minimax lo hi) := by
  let previous := s.minimax lo hi
  obtain ⟨p, l, u, attained⟩ := s.worst_attained ordered previous
  exact (s.minimax_optimal lo' hi' previous).trans
    (attained ▸ s.regret_le_worst (lower.trans l) (u.trans upper) previous)

theorem Spec.settled_wait (s : Spec) {hi p : ℚ} (within : p ≤ hi) (settled : hi ≤ s.threshold) :
    s.regret p false = 0 := by
  rw [s.regret_false, max_eq_left (sub_nonpos.mpr (within.trans settled)), mul_zero]

theorem Spec.settled_act (s : Spec) {lo p : ℚ} (within : lo ≤ p) (settled : s.threshold ≤ lo) :
    s.regret p true = 0 := by
  rw [s.regret_true, max_eq_left (sub_nonpos.mpr (settled.trans within)), mul_zero]

variable {Signal : Type*} [Fintype Signal]

def mean (weight posterior : Signal → ℚ) : ℚ := ∑ x, weight x * posterior x

theorem Spec.average_risk (s : Spec) (weight posterior : Signal → ℚ)
    (normalized : ∑ x, weight x = 1) (action : Bool) :
    (∑ x, weight x * s.risk (posterior x) action) = s.risk (mean weight posterior) action := by
  cases action
  · simp only [risk, Bool.false_eq_true, if_false, mean, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  · simp only [risk, if_true, ← Finset.sum_mul, normalized, one_mul]

/-- The expected gain used by a scheduler that has to choose a probe
before its result arrives. -/
def Spec.valueOfSignal (s : Spec) (weight posterior : Signal → ℚ) : ℚ :=
  s.bayesRisk (mean weight posterior) - ∑ x, weight x * s.bayesRisk (posterior x)

theorem Spec.value_eq_expected_regret (s : Spec) (weight posterior : Signal → ℚ)
    (normalized : ∑ x, weight x = 1) :
    s.valueOfSignal weight posterior =
      ∑ x, weight x * s.regret (posterior x) (s.act (mean weight posterior)) := by
  simp only [valueOfSignal, regret, mul_sub, Finset.sum_sub_distrib,
    s.average_risk weight posterior normalized, s.risk_at_act]

theorem Spec.value_nonneg (s : Spec) (weight posterior : Signal → ℚ)
    (nonnegative : ∀ x, 0 ≤ weight x) (normalized : ∑ x, weight x = 1) :
    0 ≤ s.valueOfSignal weight posterior := by
  rw [s.value_eq_expected_regret weight posterior normalized]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (nonnegative x) (s.regret_nonneg _ _)

theorem Spec.value_zero_of_uniform_action (s : Spec) (weight posterior : Signal → ℚ)
    (normalized : ∑ x, weight x = 1) (action : Bool)
    (before : s.regret (mean weight posterior) action = 0)
    (after : ∀ x, s.regret (posterior x) action = 0) :
    s.valueOfSignal weight posterior = 0 := by
  have gap : s.valueOfSignal weight posterior = ∑ x, weight x * s.regret (posterior x) action := by
    simp only [valueOfSignal, regret, mul_sub, Finset.sum_sub_distrib,
      s.average_risk weight posterior normalized]
    unfold regret at before
    linarith
  simp only [gap, after, mul_zero, Finset.sum_const_zero]

end Mettapedia.DecisionTheory.ThresholdDecision
