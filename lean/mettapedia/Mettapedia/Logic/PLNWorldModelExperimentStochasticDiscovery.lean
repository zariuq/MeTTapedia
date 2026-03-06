import Mathlib.Analysis.SpecificLimits.Basic
import Mettapedia.Algebra.ReferenceClassQuality
import Mettapedia.Logic.PLNBayesNetInference
import Mettapedia.Logic.PLNWorldModelExperimentStochastic

/-!
# Stochastic Discovery from Persistent Exploration

This module lifts the bounded discovery story into the existing PMF-based
stochastic experiment layer.

Core ingredients:
- one-round Bernoulli discovery queries;
- repeated independent exploration accumulated via `probOr`;
- closed form `1 - (1 - s)^n`;
- failure probability tends to `0` and discovery probability tends to `1`
  when the per-round success rate `s` is strictly positive.

Conceptual note:
- This is a stack-native stochastic version of the "persistent exploration
  implies eventual escape/discovery" idea: if each round has a nonzero chance
  of discovering the latent transition, then repeated exploration converges to
  eventual discovery with probability `1`.
-/

namespace Mettapedia.Logic.PLNWorldModelExperimentStochasticDiscovery

open Filter
open Mettapedia.Algebra.ReferenceClassQuality
open Mettapedia.Logic.PLNWorldModelExperimentStochastic
open scoped ENNReal Topology

/-- One-round Bernoulli discovery query with success probability `s`. -/
noncomputable def bernoulliDiscoveryQuery
    (s : ℝ≥0∞) (hs : s ≤ 1) : StochasticExperimentQuery PUnit Bool :=
  { channel := fun _ => Mettapedia.Logic.PLNBayesNetInference.bernoulliPMF s hs
    outcome := fun b => b = true }

/-- The one-round event probability of the Bernoulli discovery query is exactly
its success parameter. -/
theorem eventProb_bernoulliDiscoveryQuery
    (s : ℝ≥0∞) (hs : s ≤ 1) :
    eventProb (bernoulliDiscoveryQuery s hs) PUnit.unit = s := by
  simp [bernoulliDiscoveryQuery, eventProb,
    Mettapedia.Logic.PLNBayesNetInference.bernoulliPMF]

/-- Cumulative discovery probability after `n` independent rounds with
per-round success rate `s`, accumulated via probabilistic OR. -/
noncomputable def repeatedDiscoveryProb (s : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => probOr (repeatedDiscoveryProb s n) s

@[simp]
theorem repeatedDiscoveryProb_zero (s : ℝ≥0∞) :
    repeatedDiscoveryProb s 0 = 0 := rfl

@[simp]
theorem repeatedDiscoveryProb_succ (s : ℝ≥0∞) (n : ℕ) :
    repeatedDiscoveryProb s (n + 1) = probOr (repeatedDiscoveryProb s n) s := rfl

/-- The cumulative discovery probability stays bounded by `1`. -/
theorem repeatedDiscoveryProb_le_one
    (s : ℝ≥0∞) (hs : s ≤ 1) :
    ∀ n, repeatedDiscoveryProb s n ≤ 1
  | 0 => by simp [repeatedDiscoveryProb]
  | n + 1 => by
      simp [repeatedDiscoveryProb]
      exact probOr_le_one _ _ (repeatedDiscoveryProb_le_one s hs n) hs

/-- Closed form for cumulative discovery after repeated independent attempts:
`1 - (1 - s)^n`. -/
theorem repeatedDiscoveryProb_eq_closed
    (s : ℝ≥0∞) (hs : s ≤ 1) :
    ∀ n, repeatedDiscoveryProb s n = 1 - (1 - s) ^ n
  | 0 => by simp [repeatedDiscoveryProb]
  | n + 1 => by
      have ih := repeatedDiscoveryProb_eq_closed s hs n
      have hbound : (1 - s) ^ n ≤ 1 := by
        calc
          (1 - s) ^ n ≤ (1 : ℝ≥0∞) ^ n := ENNReal.pow_le_pow_left (tsub_le_self : 1 - s ≤ 1)
          _ = 1 := one_pow n
      have hsub : 1 - (1 - (1 - s) ^ n) = (1 - s) ^ n := by
        exact ENNReal.sub_sub_cancel ENNReal.one_ne_top hbound
      rw [repeatedDiscoveryProb, ih, probOr]
      rw [hsub]
      simp [pow_succ, mul_comm]

/-- Failure probability after `n` rounds tends to `0` whenever the one-round
success rate is strictly positive. -/
theorem repeatedFailureProb_tendsto_zero
    {s : ℝ≥0∞} (hs0 : 0 < s) :
    Filter.Tendsto (fun n : ℕ => (1 - s) ^ n) Filter.atTop (𝓝 0) := by
  exact
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hs0.ne')

/-- Cumulative discovery probability tends to `1` for any strictly positive
one-round success rate. -/
theorem repeatedDiscoveryProb_tendsto_one_of_pos
    {s : ℝ≥0∞} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Filter.Tendsto (fun n : ℕ => repeatedDiscoveryProb s n) Filter.atTop (𝓝 1) := by
  have hclosed :
      (fun n : ℕ => repeatedDiscoveryProb s n) =
        fun n => 1 - (1 - s) ^ n := by
    funext n
    exact repeatedDiscoveryProb_eq_closed s hs1 n
  rw [hclosed]
  refine ENNReal.tendsto_nhds_of_Icc ?_
  intro ε hε
  have hfail :
      ∀ᶠ n : ℕ in Filter.atTop, (1 - s) ^ n ≤ ε :=
    (ENNReal.tendsto_nhds_zero.1 (repeatedFailureProb_tendsto_zero hs0)) ε hε
  filter_upwards [hfail] with n hn
  refine ⟨?_, ?_⟩
  · exact tsub_le_tsub le_rfl hn
  · exact (tsub_le_self : 1 - (1 - s) ^ n ≤ 1).trans (le_add_right le_rfl)

/-- One-round discovery query with attempt rate `p` and conditional success
rate `q`, so the total success rate is `p * q`. -/
noncomputable def attemptSuccessQuery
    (p q : ℝ≥0∞) (hp : p ≤ 1) (hq : q ≤ 1) :
    StochasticExperimentQuery PUnit Bool :=
  bernoulliDiscoveryQuery (p * q) (mul_le_one' hp hq)

/-- The one-round discovery probability of the attempt/success query is
exactly `p * q`. -/
theorem eventProb_attemptSuccessQuery_eq_mul
    (p q : ℝ≥0∞) (hp : p ≤ 1) (hq : q ≤ 1) :
    eventProb (attemptSuccessQuery p q hp hq) PUnit.unit = p * q := by
  simpa [attemptSuccessQuery] using
    eventProb_bernoulliDiscoveryQuery (p * q) (mul_le_one' hp hq)

/-- Closed form for cumulative discovery under repeated attempts with attempt
rate `p` and conditional success rate `q`. -/
theorem repeatedAttemptSuccess_discovery_eq_closed
    (p q : ℝ≥0∞) (hp : p ≤ 1) (hq : q ≤ 1) (n : ℕ) :
    repeatedDiscoveryProb (p * q) n = 1 - (1 - p * q) ^ n := by
  exact repeatedDiscoveryProb_eq_closed (p * q) (mul_le_one' hp hq) n

/-- If both the attempt rate and the conditional success rate are strictly
positive, repeated exploration converges to eventual discovery with
probability `1`. -/
theorem repeatedAttemptSuccess_discovery_tendsto_one
    {p q : ℝ≥0∞}
    (hp0 : 0 < p) (hq0 : 0 < q)
    (hp1 : p ≤ 1) (hq1 : q ≤ 1) :
    Filter.Tendsto (fun n : ℕ => repeatedDiscoveryProb (p * q) n)
      Filter.atTop (𝓝 1) := by
  have hs0 : 0 < p * q := ENNReal.mul_pos hp0.ne' hq0.ne'
  have hs1 : p * q ≤ 1 := mul_le_one' hp1 hq1
  exact repeatedDiscoveryProb_tendsto_one_of_pos hs0 hs1

end Mettapedia.Logic.PLNWorldModelExperimentStochasticDiscovery
