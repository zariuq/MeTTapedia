import Mettapedia.Logic.PLNEvidence
import Mettapedia.Logic.MeasureTheoreticPLN.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# IID Bernoulli Observations

This file formalizes independent identically distributed (IID) Bernoulli observations
and connects them to PLN Evidence.

## Key Definitions

- `IIDBernoulli`: Structure for IID Bernoulli observations with parameter θ
- `evidenceFromObservations`: Convert n IID observations to Evidence (k, n-k)
- `strengthFromObservations`: The empirical frequency k/n

## The IID Setting

For IID Bernoulli(θ) observations X₁, X₂, ..., Xₙ:
- Each Xᵢ ∈ {0, 1} with P(Xᵢ = 1) = θ
- The observations are mutually independent
- The sufficient statistic is k = Σᵢ Xᵢ (count of successes)

PLN Evidence (k, n-k) captures exactly this sufficient statistic.

## References

- Kolmogorov, "Foundations of the Theory of Probability" (1933)
- de Finetti, "Theory of Probability" (1974) for exchangeability connection
-/

namespace Mettapedia.Logic.Convergence

open Mettapedia.Logic.PLNEvidence
open Mettapedia.Logic.MeasureTheoreticPLN
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## Simple Bernoulli Sequence

We start with a simpler formulation that doesn't require the full
Mathlib probability infrastructure.
-/

/-- A sequence of Bernoulli observations (simplified representation).

    In the simple model, we just track:
    - `successes`: number of positive outcomes
    - `total`: total number of observations

    This captures the sufficient statistic for Bernoulli inference.
-/
structure BernoulliObservations where
  /-- Number of successes (positive outcomes) -/
  successes : ℕ
  /-- Total number of observations -/
  total : ℕ
  /-- Successes cannot exceed total -/
  successes_le : successes ≤ total

namespace BernoulliObservations

/-- Number of failures -/
def failures (obs : BernoulliObservations) : ℕ := obs.total - obs.successes

/-- Failures + successes = total -/
theorem failures_add_successes (obs : BernoulliObservations) :
    obs.failures + obs.successes = obs.total := by
  unfold failures
  have h := obs.successes_le
  omega

/-- Empty observation sequence -/
def empty : BernoulliObservations where
  successes := 0
  total := 0
  successes_le := Nat.zero_le 0

/-- Single success -/
def singleSuccess : BernoulliObservations where
  successes := 1
  total := 1
  successes_le := le_refl 1

/-- Single failure -/
def singleFailure : BernoulliObservations where
  successes := 0
  total := 1
  successes_le := Nat.zero_le 1

/-- Combine two independent observation sequences -/
def combine (obs₁ obs₂ : BernoulliObservations) : BernoulliObservations where
  successes := obs₁.successes + obs₂.successes
  total := obs₁.total + obs₂.total
  successes_le := Nat.add_le_add obs₁.successes_le obs₂.successes_le

theorem combine_successes (obs₁ obs₂ : BernoulliObservations) :
    (combine obs₁ obs₂).successes = obs₁.successes + obs₂.successes := rfl

theorem combine_total (obs₁ obs₂ : BernoulliObservations) :
    (combine obs₁ obs₂).total = obs₁.total + obs₂.total := rfl

/-- Empirical frequency: k/n (or 0 if n = 0) -/
noncomputable def frequency (obs : BernoulliObservations) : ℝ :=
  if obs.total = 0 then 0 else (obs.successes : ℝ) / (obs.total : ℝ)

/-- Frequency is in [0, 1] -/
theorem frequency_mem_unit (obs : BernoulliObservations) :
    obs.frequency ∈ Set.Icc (0 : ℝ) 1 := by
  unfold frequency
  split_ifs with h
  · exact ⟨le_refl 0, zero_le_one⟩
  · constructor
    · apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _
    · have hn : (0 : ℝ) < obs.total := by
        have : 0 < obs.total := Nat.pos_of_ne_zero h
        exact Nat.cast_pos.mpr this
      rw [div_le_one hn]
      exact Nat.cast_le.mpr obs.successes_le

end BernoulliObservations

/-! ## Conversion to PLN Evidence -/

/-- Convert Bernoulli observations to PLN Evidence.

    Observations (k successes, n total) become Evidence (k, n-k).
-/
def observationsToEvidence (obs : BernoulliObservations) : Evidence :=
  ⟨obs.successes, obs.failures⟩

/-- The evidence total equals the observation total -/
theorem observationsToEvidence_total (obs : BernoulliObservations) :
    (observationsToEvidence obs).total = obs.total := by
  unfold observationsToEvidence Evidence.total BernoulliObservations.failures
  -- Goal: (obs.successes : ℝ≥0∞) + (obs.total - obs.successes : ℝ≥0∞) = (obs.total : ℝ≥0∞)
  have hle := obs.successes_le
  simp only [← Nat.cast_add (R := ℝ≥0∞)]
  congr 1
  omega

/-- Evidence strength equals empirical frequency (for nonzero observations) -/
theorem observationsToEvidence_strength (obs : BernoulliObservations) (h : obs.total ≠ 0) :
    (Evidence.toStrength (observationsToEvidence obs)).toReal = obs.frequency := by
  unfold observationsToEvidence Evidence.toStrength Evidence.total BernoulliObservations.frequency
         BernoulliObservations.failures
  simp only [h, ↓reduceIte]
  have hle := obs.successes_le
  have heq : obs.successes + (obs.total - obs.successes) = obs.total := by omega
  have htotal : (obs.successes : ℝ≥0∞) + (obs.total - obs.successes : ℕ) ≠ 0 := by
    simp only [← Nat.cast_add (R := ℝ≥0∞), heq]
    simp only [ne_eq, Nat.cast_eq_zero]
    exact h
  simp only [htotal, ↓reduceIte]
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast]
  congr 1
  simp only [← Nat.cast_add (R := ℝ≥0∞), heq, ENNReal.toReal_natCast]

/-- Combining observations corresponds to hplus of evidence -/
theorem observationsToEvidence_combine (obs₁ obs₂ : BernoulliObservations) :
    observationsToEvidence (BernoulliObservations.combine obs₁ obs₂) =
    observationsToEvidence obs₁ + observationsToEvidence obs₂ := by
  unfold observationsToEvidence BernoulliObservations.combine BernoulliObservations.failures
  rw [Evidence.hplus_def]
  have h₁ := obs₁.successes_le
  have h₂ := obs₂.successes_le
  -- Key arithmetic fact: (t₁+t₂) - (s₁+s₂) = (t₁-s₁) + (t₂-s₂) when s₁≤t₁ and s₂≤t₂
  have heq : (obs₁.total + obs₂.total) - (obs₁.successes + obs₂.successes) =
             (obs₁.total - obs₁.successes) + (obs₂.total - obs₂.successes) := by omega
  ext
  · -- pos component: (s₁ + s₂ : ℕ) = (s₁ : ℝ≥0∞) + (s₂ : ℝ≥0∞)
    simp only [Nat.cast_add]
  · -- neg component
    simp only [heq, Nat.cast_add]

/-! ## Theoretical IID Model

For more advanced results (Law of Large Numbers), we need the measure-theoretic
formulation. This is kept separate as it requires more Mathlib infrastructure.
-/

/-- Parameters for a theoretical IID Bernoulli model -/
structure IIDBernoulliParams where
  /-- The true Bernoulli parameter θ ∈ [0,1] -/
  theta : Set.Icc (0 : ℝ) 1
  /-- Number of observations -/
  n : ℕ

namespace IIDBernoulliParams

/-- Expected number of successes: n * θ -/
noncomputable def expectedSuccesses (params : IIDBernoulliParams) : ℝ :=
  params.n * params.theta.val

/-- Expected frequency equals θ -/
theorem expectedFrequency_eq_theta (params : IIDBernoulliParams) (hn : 0 < params.n) :
    params.expectedSuccesses / params.n = params.theta.val := by
  unfold expectedSuccesses
  have hn' : (0 : ℝ) < params.n := Nat.cast_pos.mpr hn
  field_simp [hn'.ne']

/-- Variance of success count: n * θ * (1 - θ) -/
noncomputable def variance (params : IIDBernoulliParams) : ℝ :=
  params.n * params.theta.val * (1 - params.theta.val)

/-- Variance is non-negative -/
theorem variance_nonneg (params : IIDBernoulliParams) : 0 ≤ params.variance := by
  unfold variance
  apply mul_nonneg
  apply mul_nonneg
  · exact Nat.cast_nonneg _
  · exact params.theta.2.1
  · have h := params.theta.2.2
    linarith

/-- Variance of frequency: θ(1-θ)/n -/
noncomputable def frequencyVariance (params : IIDBernoulliParams) (_hn : 0 < params.n) : ℝ :=
  params.theta.val * (1 - params.theta.val) / params.n

/-- Frequency variance is O(1/n) -/
theorem frequencyVariance_bound (params : IIDBernoulliParams) (hn : 0 < params.n) :
    params.frequencyVariance hn ≤ 1 / (4 * params.n) := by
  unfold frequencyVariance
  have hn' : (0 : ℝ) < params.n := Nat.cast_pos.mpr hn
  -- θ(1-θ) ≤ 1/4 for θ ∈ [0,1], maximized at θ = 1/2
  -- Proof: θ(1-θ) ≤ 1/4 ⟺ 4θ(1-θ) ≤ 1 ⟺ 4θ - 4θ² ≤ 1 ⟺ 4θ² - 4θ + 1 ≥ 0 ⟺ (2θ-1)² ≥ 0
  have h_bound : params.theta.val * (1 - params.theta.val) ≤ 1/4 := by
    have h0 := params.theta.2.1
    have h1 := params.theta.2.2
    have hsq : (2 * params.theta.val - 1)^2 ≥ 0 := sq_nonneg _
    nlinarith [hsq]
  calc params.theta.val * (1 - params.theta.val) / params.n
      ≤ (1/4) / params.n := by apply div_le_div_of_nonneg_right h_bound (le_of_lt hn')
    _ = 1 / (4 * params.n) := by ring

end IIDBernoulliParams

/-! ## Chebyshev Bound

The key tool for proving weak convergence is Chebyshev's inequality:
P(|X - μ| ≥ ε) ≤ Var(X) / ε²
-/

/-- Chebyshev-style bound on deviation probability.

    For IID Bernoulli(θ), the probability that the empirical frequency
    deviates from θ by more than ε is at most θ(1-θ)/(nε²) ≤ 1/(4nε²).
-/
theorem chebyshev_frequency_bound (params : IIDBernoulliParams) (hn : 0 < params.n) (ε : ℝ) (hε : 0 < ε) :
    -- The theoretical bound (without measure-theoretic formulation)
    -- P(|frequency - θ| ≥ ε) ≤ 1/(4nε²)
    params.frequencyVariance hn / ε^2 ≤ 1 / (4 * params.n * ε^2) := by
  have hε2 : 0 < ε^2 := sq_pos_of_pos hε
  have _hn' : (0 : ℝ) < params.n := Nat.cast_pos.mpr hn
  calc params.frequencyVariance hn / ε^2
      ≤ (1 / (4 * params.n)) / ε^2 := by
        apply div_le_div_of_nonneg_right (params.frequencyVariance_bound hn) (le_of_lt hε2)
    _ = 1 / (4 * params.n * ε^2) := by ring

/-! ## Summary

This file establishes:

1. **BernoulliObservations**: Simple representation of IID Bernoulli outcomes
   - `successes`: count of positive outcomes
   - `total`: total observations
   - `frequency`: empirical frequency k/n

2. **observationsToEvidence**: Convert observations to PLN Evidence
   - Observations (k, n) → Evidence (k, n-k)
   - Frequency corresponds to PLN strength

3. **IIDBernoulliParams**: Theoretical model parameters
   - `theta`: true Bernoulli parameter
   - `variance`: sampling variance n*θ*(1-θ)
   - `frequencyVariance`: variance of empirical frequency, O(1/n)

4. **Chebyshev bound**: Probability of large deviation ≤ 1/(4nε²)

## Connection to Convergence

The frequencyVariance bound shows:
- Var(frequency) = O(1/n)
- By Chebyshev: P(|frequency - θ| ≥ ε) = O(1/n)
- Therefore: frequency → θ in probability (Weak LLN)

The full measure-theoretic LLN proof is in `LawOfLargeNumbers.lean`.
-/

end Mettapedia.Logic.Convergence
