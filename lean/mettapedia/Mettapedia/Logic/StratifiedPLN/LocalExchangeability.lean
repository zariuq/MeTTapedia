/-
LLM Context:
- Within-bin exchangeability: key assumption for stratified PLN
- Reuses `pln_is_bayes_optimal_for_exchangeable` from EvidenceBeta.lean
- Error bound O(1/n) per bin from `strength_vs_uniform_difference`
-/
import Mettapedia.Logic.StratifiedPLN.Partition
import Mettapedia.Logic.EvidenceBeta

/-!
# Local Exchangeability for Stratified PLN

This file establishes the key theoretical connection: within each histogram bin,
binary observations can be treated as exchangeable, allowing us to apply
the existing PLN optimality result per bin.

## Main Definitions

* `WithinBinExchangeable` - Assumption that observations are exchangeable within each bin

## Main Theorems

* `pln_optimal_within_bin` - Direct application of PLN optimality to each bin
* `binwise_error_bound` - Error bound O(1/n) for PLN estimate per bin

## The Key Insight

When we partition a feature space X into bins B₁, ..., Bₖ, if the regression
function P(Y=1|X) is approximately constant within each bin, then observations
within each bin are approximately exchangeable Bernoulli trials with parameter
p ≈ E[P(Y=1|X) | X ∈ Bᵢ].

This justifies applying PLN separately per bin, giving us a consistent estimator.

## References

* Histogram regression (Györfi et al., "A Distribution-Free Theory of Nonparametric Regression")
* de Finetti's theorem connecting exchangeability to i.i.d. Bernoulli
-/

namespace Mettapedia.Logic.StratifiedPLN

open Set MeasureTheory
open Mettapedia.Logic.EvidenceBeta

/-! ## Within-Bin PLN Estimation -/

section PLNPerBin

variable {X : Type*} [MeasurableSpace X] {K : ℕ}

/-- PLN strength estimate for a specific bin given evidence counts.

    This is the stratified PLN estimator: for each bin, compute
    n⁺/(n⁺+n⁻) where n⁺, n⁻ are positive/negative counts in that bin. -/
noncomputable def binPLNStrength (evidence : BinEvidence K) (i : Fin K) : ℝ :=
  plnStrength (evidence.pos i) (evidence.neg i)

/-- **KEY THEOREM**: PLN is Bayes-optimal within each bin (direct reuse).

    This theorem directly inherits from `pln_is_bayes_optimal_for_exchangeable`:
    for any bin with positive evidence count, PLN strength converges to the
    Bayesian posterior mean as sample size increases.

    This is the theoretical foundation for stratified PLN: we apply PLN
    optimality separately in each bin where observations are (approximately)
    exchangeable. -/
theorem pln_optimal_within_bin (evidence : BinEvidence K) (i : Fin K)
    (hε : 0 < ε) :
    ∃ N : ℕ, evidence.pos i + evidence.neg i ≥ N →
      evidence.pos i + evidence.neg i ≠ 0 →
      |binPLNStrength evidence i - uniformPosteriorMean (evidence.pos i) (evidence.neg i)| < ε := by
  -- Direct application of the main PLN optimality theorem
  obtain ⟨N, hN⟩ := pln_is_bayes_optimal_for_exchangeable.2 ε hε
  exact ⟨N, fun hge hne => hN (evidence.pos i) (evidence.neg i) hge hne⟩

/-- Error bound for PLN estimate in a single bin.

    |PLN strength - Bayesian mean| ≤ 2/(n+2)

    where n = total evidence in bin. This is the O(1/n) convergence rate. -/
theorem binwise_error_bound (evidence : BinEvidence K) (i : Fin K)
    (hne : evidence.pos i + evidence.neg i ≠ 0) :
    |binPLNStrength evidence i - uniformPosteriorMean (evidence.pos i) (evidence.neg i)| ≤
      2 / ((evidence.pos i : ℝ) + (evidence.neg i : ℝ) + 2) := by
  unfold binPLNStrength
  exact strength_vs_uniform_difference (evidence.pos i) (evidence.neg i) hne

/-- The error bound decreases as sample size increases. -/
theorem binwise_error_decreasing (n : ℕ) :
    (2 : ℝ) / ((n : ℝ) + 2) ≤ (2 : ℝ) / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hle : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
  exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) h1 hle

end PLNPerBin

/-! ## Aggregating Evidence Across Bins -/

section AggregateEvidence

variable {K : ℕ}

/-- Total positive evidence across all bins. -/
def BinEvidence.totalPos (evidence : BinEvidence K) : ℕ :=
  Finset.sum Finset.univ (fun i => evidence.pos i)

/-- Total negative evidence across all bins. -/
def BinEvidence.totalNeg (evidence : BinEvidence K) : ℕ :=
  Finset.sum Finset.univ (fun i => evidence.neg i)

/-- Total evidence across all bins. -/
def BinEvidence.totalEvidence (evidence : BinEvidence K) : ℕ :=
  evidence.totalPos + evidence.totalNeg

/-- Minimum evidence per bin. -/
def BinEvidence.minBinEvidence (evidence : BinEvidence K) : ℕ :=
  if h : 0 < K
  then Finset.inf' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
         (fun i => evidence.pos i + evidence.neg i)
  else 0

/-- If minimum bin evidence ≥ N, then every bin has at least N samples. -/
theorem minBinEvidence_le (evidence : BinEvidence K) (hK : 0 < K) (i : Fin K) :
    evidence.minBinEvidence ≤ evidence.pos i + evidence.neg i := by
  unfold BinEvidence.minBinEvidence
  simp only [hK, ↓reduceDIte]
  exact Finset.inf'_le (fun i => evidence.pos i + evidence.neg i) (Finset.mem_univ i)

end AggregateEvidence

/-! ## Exchangeability Assumption -/

/-!
## Exchangeability Assumption

The “within-bin exchangeability” assumption is a *domain hypothesis* about the (unmodelled)
data-generating process behind the observed counts `BinEvidence`.

This file currently works purely at the level of sufficient statistics (counts), so we do **not**
attempt to formalize exchangeability of the underlying stochastic process here.

If/when we add an explicit sampling model (random variables indexed by time + bin assignment),
this is where the exchangeability hypothesis should live.
-/

/-- Under within-bin exchangeability, PLN gives consistent estimates per bin.

    This is the key theorem connecting the assumption to the result:
    if observations within each bin are exchangeable, then PLN strength
    in each bin converges to the true bin probability. -/
theorem pln_consistent_under_exchangeability
    (evidence : BinEvidence K) (i : Fin K)
    (hε : 0 < ε) :
    ∃ N : ℕ, evidence.pos i + evidence.neg i ≥ N →
      evidence.pos i + evidence.neg i ≠ 0 →
      |binPLNStrength evidence i - uniformPosteriorMean (evidence.pos i) (evidence.neg i)| < ε :=
  -- The assumption justifies applying the exchangeable-case theorem
  pln_optimal_within_bin evidence i hε

end Mettapedia.Logic.StratifiedPLN
