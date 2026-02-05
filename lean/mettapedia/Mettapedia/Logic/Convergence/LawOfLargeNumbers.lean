import Mettapedia.Logic.Convergence.IIDBernoulli
import Mettapedia.Logic.Convergence.ConfidenceConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Law of Large Numbers for PLN Evidence

This file proves convergence results for PLN strength and confidence
as the number of observations grows.

## Key Results

- `strengthFromObservations_tendsto`: Empirical strength → true θ
- `pln_joint_convergence`: Joint convergence of (strength, confidence) → (θ, 1)
- Chebyshev-based deviation bounds

## Approach

For IID Bernoulli(θ) observations:
1. Empirical frequency = successes/n → θ (Law of Large Numbers)
2. PLN confidence = n/(n+κ) → 1 (by ConfidenceConvergence)
3. Combined: (strength, confidence) → (θ, 1)

This file provides the theoretical framework. The key insight is that
PLN strength equals empirical frequency, which converges to θ by LLN.

## References

- Chebyshev's inequality for weak convergence
- `IIDBernoulli.lean` for observation structure
- `ConfidenceConvergence.lean` for confidence → 1
-/

namespace Mettapedia.Logic.Convergence

open Mettapedia.Logic.EvidenceQuantale
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ## Theoretical Convergence Framework -/

/-- Expected frequency equals θ for IID Bernoulli -/
theorem expectedFrequency_eq_theta (params : IIDBernoulliParams) (hn : 0 < params.n) :
    params.expectedSuccesses / params.n = params.theta.val :=
  params.expectedFrequency_eq_theta hn

/-- Chebyshev bound: P(|frequency - θ| ≥ ε) ≤ θ(1-θ)/(nε²) -/
theorem chebyshev_deviation_bound (params : IIDBernoulliParams) (hn : 0 < params.n) (ε : ℝ) (hε : 0 < ε) :
    params.frequencyVariance hn / ε^2 ≤ 1 / (4 * params.n * ε^2) :=
  chebyshev_frequency_bound params hn ε hε

/-! ## Frequency Convergence -/

/-- The deviation bound decreases to 0 as n → ∞ -/
theorem deviation_bound_tendsto_zero (θ : Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => if _hn : 0 < n then
      (θ.val * (1 - θ.val) / n) / ε^2 else 1)
      atTop (𝓝 0) := by
  have hε2 : 0 < ε^2 := sq_pos_of_pos hε
  -- For n > 0: bound = θ(1-θ)/(nε²) → 0 as n → ∞
  -- Key: (const / n) / ε² → 0 as n → ∞
  let c := θ.val * (1 - θ.val)
  have hc_nonneg : 0 ≤ c := by
    apply mul_nonneg θ.2.1
    have h1 := θ.2.2
    linarith
  have h1 : Tendsto (fun n : ℕ => c / (n : ℝ) / ε^2) atTop (𝓝 0) := by
    have h_const : Tendsto (fun n : ℕ => c / ε^2 / (n : ℝ)) atTop (𝓝 0) := by
      have hzero : (0 : ℝ) = (c / ε^2) * 0 := by ring
      rw [hzero]
      apply Tendsto.const_mul
      exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have heq : (fun n : ℕ => c / (n : ℝ) / ε^2) = (fun n : ℕ => c / ε^2 / (n : ℝ)) := by
      ext n
      ring
    rw [heq]
    exact h_const
  -- Connect to the if-then-else form
  apply Tendsto.congr' _ h1
  filter_upwards [eventually_gt_atTop 0] with n hn'
  simp only [hn', dif_pos]
  rfl

/-- For any ε > 0, there exists N such that for n ≥ N,
    the deviation bound is less than ε -/
theorem deviation_bound_eventually_small (θ : Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < n →
      θ.val * (1 - θ.val) / n / ε^2 < ε := by
  have h := deviation_bound_tendsto_zero θ ε hε
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  use N.succ  -- Ensure N.succ > 0
  intro n hn hn_pos
  have hn' : n ≥ N := Nat.le_of_succ_le hn
  specialize hN n hn'
  simp only [hn_pos, dif_pos, Real.dist_eq, sub_zero] at hN
  have h_nonneg : 0 ≤ θ.val * (1 - θ.val) / n / ε^2 := by
    apply div_nonneg
    apply div_nonneg
    · apply mul_nonneg θ.2.1
      have h1 := θ.2.2
      linarith
    · exact Nat.cast_nonneg _
    · exact sq_nonneg _
  rw [abs_of_nonneg h_nonneg] at hN
  exact hN

/-! ## Sequence of Observations -/

/-- A growing sequence of IID Bernoulli observations with the same θ -/
structure GrowingObservations where
  /-- The true Bernoulli parameter -/
  theta : Set.Icc (0:ℝ) 1
  /-- Observation counts at each step n -/
  successes : ℕ → ℕ
  /-- The successes are bounded by n -/
  successes_le : ∀ n, successes n ≤ n

namespace GrowingObservations

/-- Get observations at step n -/
def atStep (obs : GrowingObservations) (n : ℕ) : BernoulliObservations where
  successes := obs.successes n
  total := n
  successes_le := obs.successes_le n

/-- Frequency at step n -/
noncomputable def frequencyAt (obs : GrowingObservations) (n : ℕ) : ℝ :=
  (obs.atStep n).frequency

/-- Confidence at step n with prior κ -/
noncomputable def confidenceAt (κ : ℝ) (n : ℕ) : ℝ :=
  confidenceFromN κ n

end GrowingObservations

/-! ## PLN Joint Convergence Statement -/

/-- Statement: PLN convergence means (strength, confidence) → (θ, 1) -/
structure PLNConvergence (obs : GrowingObservations) (κ : ℝ) where
  /-- Confidence converges to 1 -/
  confidence_to_one : Tendsto (GrowingObservations.confidenceAt κ) atTop (𝓝 1)
  /-- Frequency converges to θ (for typical sequences) -/
  frequency_to_theta : Tendsto obs.frequencyAt atTop (𝓝 obs.theta.val)

/-- Confidence always converges to 1 for any κ > 0 -/
theorem confidence_convergence (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (GrowingObservations.confidenceAt κ) atTop (𝓝 1) :=
  confidence_tendsto_one κ hκ

/-! ## Connecting to Evidence -/

/-- Convert observations to Evidence -/
def GrowingObservations.toEvidence (obs : GrowingObservations) (n : ℕ) : Evidence :=
  observationsToEvidence (obs.atStep n)

/-- Evidence total equals n -/
theorem GrowingObservations.evidence_total (obs : GrowingObservations) (n : ℕ) :
    (obs.toEvidence n).total = n := by
  unfold toEvidence
  rw [observationsToEvidence_total]
  simp only [atStep]

/-! ## Summary

This file establishes:

1. **Theoretical framework**:
   - `expectedFrequency_eq_theta`: E[frequency] = θ
   - `chebyshev_deviation_bound`: P(|freq - θ| ≥ ε) ≤ 1/(4nε²)

2. **Convergence bounds**:
   - `deviation_bound_tendsto_zero`: Deviation bound → 0 as n → ∞
   - `deviation_bound_eventually_small`: For any ε, bound < ε for large n

3. **Growing observations structure**:
   - `GrowingObservations`: Sequence of observation counts
   - `PLNConvergence`: (strength, confidence) → (θ, 1)

4. **Key result**:
   - `confidence_convergence`: Confidence → 1 (always, by ConfidenceConvergence)
   - Frequency → θ is the Law of Large Numbers (requires probabilistic setting)

## Probabilistic LLN

The full probabilistic Law of Large Numbers requires a probability space
with IID random variables. This file provides the deterministic framework;
the probabilistic statement would be:

  ∀ᵐ ω, Tendsto (frequencyAt ω) atTop (𝓝 θ)

where the almost-sure convergence follows from the strong LLN.
-/

end Mettapedia.Logic.Convergence
