import Mettapedia.Cybernetics.ApproximateAdequacy.Coupling
import Mettapedia.InformationTheory.FiniteProbability

/-!
# Observation-contingent policies and predictive guarantees

An action produces both a next latent state and an observation. The next policy
branch depends on the observation. A coupling between two models must therefore
couple observations equally, as well as bound successor-state discrepancy.
Per-action agreement of latent-state marginals alone does not justify adaptive
planning. The finite stochastic carrier is shared with Bayesian inference.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy

universe uO uA

open Finset
open Mettapedia.InformationTheory

variable {S T O A : Type*} [Fintype S] [Fintype T] [Fintype O]

/-- A finite deterministic policy tree whose branches are selected by observations. -/
def ObservationPolicy (O : Type uO) (A : Type uA) : ℕ → Type (max uO uA)
  | 0 => PUnit
  | n + 1 => A × (O → ObservationPolicy O A n)

/-- Expected terminal reward under an observation-contingent policy. -/
noncomputable def adaptiveValue (kernel : A → S → Prob (S × O)) (terminal : S → ℝ) :
    {n : ℕ} → ObservationPolicy O A n → S → ℝ
  | 0, _, s => terminal s
  | n + 1, policy, s =>
      expect (kernel policy.1 s).1
        (fun next => adaptiveValue kernel terminal (n := n) (policy.2 next.2) next.1)

/-- The expectation guarantee for every finite adaptive policy, from compatible step couplings. -/
theorem abs_adaptiveValue_sub_le
    (first : A → S → Prob (S × O)) (second : A → T → Prob (T × O))
    (firstReward : S → ℝ) (secondReward : T → ℝ) (metric : S → T → ℝ)
    (reward_bound : ∀ s t, |firstReward s - secondReward t| ≤ metric s t)
    (step : ∀ a s t, ∃ coupling : Coupling (first a s).1 (second a t).1,
      (∀ x y, 0 < coupling.weight x y → x.2 = y.2) ∧
        coupling.cost (fun x y => metric x.1 y.1) ≤ metric s t)
    {n : ℕ} (policy : ObservationPolicy O A n) (s : S) (t : T) :
    |adaptiveValue first firstReward policy s - adaptiveValue second secondReward policy t| ≤
      metric s t := by
  induction n generalizing s t with
  | zero => exact reward_bound s t
  | succ n ih =>
      obtain ⟨coupling, observations, bounded⟩ := step policy.1 s t
      apply le_trans (coupling.abs_expect_sub_le_on_support (m := fun x y => metric x.1 y.1) ?_)
        bounded
      intro x y positive
      have same := observations x y positive
      change |adaptiveValue first firstReward (policy.2 x.2) x.1 -
          adaptiveValue second secondReward (policy.2 y.2) y.1| ≤ metric x.1 y.1
      rw [same]
      exact ih (policy.2 y.2) x.1 y.1

/-- A prior coupling lifts the statewise adaptive guarantee to a Bayesian decision score. -/
theorem abs_expected_adaptiveValue_sub_le
    (first : A → S → Prob (S × O)) (second : A → T → Prob (T × O))
    (firstReward : S → ℝ) (secondReward : T → ℝ) (metric : S → T → ℝ)
    (reward_bound : ∀ s t, |firstReward s - secondReward t| ≤ metric s t)
    (step : ∀ a s t, ∃ coupling : Coupling (first a s).1 (second a t).1,
      (∀ x y, 0 < coupling.weight x y → x.2 = y.2) ∧
        coupling.cost (fun x y => metric x.1 y.1) ≤ metric s t)
    (firstPrior : Prob S) (secondPrior : Prob T)
    (priorCoupling : Coupling firstPrior.1 secondPrior.1)
    {n : ℕ} (policy : ObservationPolicy O A n) :
    |expect firstPrior.1 (adaptiveValue first firstReward policy) -
      expect secondPrior.1 (adaptiveValue second secondReward policy)| ≤ priorCoupling.cost metric :=
  priorCoupling.abs_expect_sub_le (fun s t =>
    abs_adaptiveValue_sub_le first second firstReward secondReward metric reward_bound step policy s t)

/-- Expected rewards of bounded terminal functions remain bounded at every horizon. -/
theorem adaptiveValue_abs_le (kernel : A → S → Prob (S × O)) (reward : S → ℝ)
    (bound : ℝ) (bounded : ∀ s, |reward s| ≤ bound)
    {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    |adaptiveValue kernel reward policy s| ≤ bound := by
  induction n generalizing s with
  | zero => exact bounded s
  | succ n ih =>
      change |∑ next, (kernel policy.1 s).1 next *
        adaptiveValue kernel reward (policy.2 next.2) next.1| ≤ bound
      calc
        _ ≤ ∑ next, |(kernel policy.1 s).1 next *
            adaptiveValue kernel reward (policy.2 next.2) next.1| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ next, (kernel policy.1 s).1 next * bound := by
          apply Finset.sum_le_sum
          intro next _
          rw [abs_mul, abs_of_nonneg ((kernel policy.1 s).2.1 next)]
          exact mul_le_mul_of_nonneg_left (ih (policy.2 next.2) next.1)
            ((kernel policy.1 s).2.1 next)
        _ = bound := by rw [← Finset.sum_mul, (kernel policy.1 s).2.2, one_mul]

end Mettapedia.Cybernetics.ApproximateAdequacy
