import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio
import KnuthSkilling.Information.InformationEntropy
import Mettapedia.InformationTheory.ShannonEntropy.Interface

/-!
# KL Divergence Bridge: UAI ↔ K&S ↔ Mathlib

This file connects the UAI likelihood ratio machinery to the K&S derived KL divergence
and mathlib's measure-theoretic `klDiv`.

## The Connection

The UAI theorem `conditional_stepLogLikelihood` proves:
```
∑ P(x) * log(Q(x)/P(x)) ≤ 0
```

This is exactly `-KL(P || Q) ≤ 0`, i.e., **Gibbs' inequality**.

The K&S development derives this from variational principles:
- `atomDivergence w u = u - w + w * log(w/u)` (Divergence.lean)
- `klDivergence P Q = ∑ p_i * log(p_i / q_i)` (InformationEntropy.lean)
- `klDivergence_nonneg'`: KL divergence is non-negative (Gibbs' inequality)

Mathlib provides the measure-theoretic generalization:
- `klDiv μ ν = ∫ log(dμ/dν) dμ` when `μ ≪ ν`
- DivergenceMathlib.lean proves: `klDiv = divergenceInfTop` for discrete measures

## Main Results

* `stepLogLikelihood_sum_eq_neg_klDivergence` - The UAI sum equals -KL divergence
* `conditional_stepLogLikelihood_via_gibbs` - Alternative proof using K&S Gibbs' inequality

## Architecture

```
UAI (LikelihoodRatio.lean)
  ↓ this file
K&S (InformationEntropy.lean)
  ↓ DivergenceMathlib.lean
Mathlib (InformationTheory.KullbackLeibler.Basic)
```

-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.KLDivergenceBridge

open MeasureTheory Real Finset
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio
open KnuthSkilling.Information.InformationEntropy

/-! ## The Key Connection: Step Log-Likelihood = -KL Divergence

The sum `∑ P(x) * log(Q(x)/P(x))` that appears in `conditional_stepLogLikelihood`
is exactly the negative of KL divergence `D(P || Q) = ∑ P(x) * log(P(x)/Q(x))`. -/

/-- The step log-likelihood sum equals the negative KL divergence.

This is the key identity connecting UAI's likelihood ratio to information theory:
```
∑ P(x) * log(Q(x)/P(x)) = -∑ P(x) * log(P(x)/Q(x)) = -KL(P || Q)
```
-/
theorem stepLogLikelihood_sum_eq_neg_klDivergence
    {n : ℕ} (P Q : Fin n → ℝ)
    (hP_nonneg : ∀ i, 0 ≤ P i) (_hQ_nonneg : ∀ i, 0 ≤ Q i)
    (_hP_sum : ∑ i, P i = 1)
    (hQ_pos : ∀ i, P i ≠ 0 → 0 < Q i) :
    ∑ i, P i * log (Q i / P i) = -(∑ i, P i * log (P i / Q i)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hPi : P i = 0
  · simp [hPi]
  · have hQi_pos : 0 < Q i := hQ_pos i hPi
    have hPi_pos : 0 < P i := (hP_nonneg i).lt_of_ne' hPi
    rw [log_div (ne_of_gt hQi_pos) (ne_of_gt hPi_pos)]
    rw [log_div (ne_of_gt hPi_pos) (ne_of_gt hQi_pos)]
    ring

/-- **Gibbs' inequality via K&S**: The step log-likelihood sum is non-positive.

This provides an alternative proof path using the K&S-derived Gibbs' inequality
(`klDivergence_nonneg'`) instead of proving it directly as in `conditional_stepLogLikelihood`.

The connection is:
```
∑ P(x) * log(Q(x)/P(x)) = -KL(P || Q) ≤ 0
```
since `KL(P || Q) ≥ 0` by Gibbs' inequality.
-/
theorem stepLogLikelihood_sum_nonpos_via_gibbs
    {n : ℕ} (_hn : 0 < n)
    (P Q : Fin n → ℝ)
    (hP_nonneg : ∀ i, 0 ≤ P i) (hQ_nonneg : ∀ i, 0 ≤ Q i)
    (hP_sum : ∑ i, P i = 1) (hQ_sum : ∑ i, Q i = 1)
    (hQ_pos : ∀ i, P i ≠ 0 → 0 < Q i) :
    ∑ i, P i * log (Q i / P i) ≤ 0 := by
  -- Construct ProbDist from P and Q
  let Pdist : ProbDist n := ⟨P, hP_nonneg, hP_sum⟩
  let Qdist : ProbDist n := ⟨Q, hQ_nonneg, hQ_sum⟩
  -- Use the identity: ∑ P * log(Q/P) = -∑ P * log(P/Q)
  have heq := stepLogLikelihood_sum_eq_neg_klDivergence P Q hP_nonneg hQ_nonneg hP_sum hQ_pos
  -- klDivergence Pdist Qdist = ∑ P * log(P/Q)
  have hkl_def : klDivergence Pdist Qdist hQ_pos = ∑ i, P i * log (P i / Q i) := rfl
  -- KL ≥ 0 (Gibbs' inequality from K&S)
  have hkl_nonneg : 0 ≤ klDivergence Pdist Qdist hQ_pos := klDivergence_nonneg' Pdist Qdist hQ_pos
  -- Combine: ∑ P * log(Q/P) = -KL ≤ 0
  calc ∑ i, P i * log (Q i / P i)
      = -(∑ i, P i * log (P i / Q i)) := heq
    _ = -klDivergence Pdist Qdist hQ_pos := by rw [← hkl_def]
    _ ≤ 0 := by linarith

/-! ## Summary: The Information-Theoretic View

The supermartingale property of the log-likelihood ratio has a beautiful
information-theoretic interpretation:

**Under the true environment ν*, observing more data can only decrease
our belief in a wrong environment ν (on average).**

Mathematically:
```
E_{ν*}[L_{t+1} - L_t | F_t] = -KL(ν* || ν | h_t) ≤ 0
```

This file shows that:
1. The UAI proof (`conditional_stepLogLikelihood`) directly proves `-KL ≤ 0`
2. This is equivalent to Gibbs' inequality `KL ≥ 0`
3. K&S derives Gibbs' inequality from variational principles
4. Mathlib generalizes to measure-theoretic KL divergence

The chain: **UAI ↔ K&S ↔ Mathlib** is now complete for KL divergence.
-/

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.KLDivergenceBridge
