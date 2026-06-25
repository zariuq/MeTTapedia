import Mettapedia.UniversalAI.UniversalPrediction.MarkovBetaPredictor
import Mettapedia.UniversalAI.UniversalPrediction.FiniteHorizon
import Mettapedia.UniversalAI.UniversalPrediction.CompetitorBounds

/-!
# Hyperprior Mixtures for Markov(1) Beta Predictors (Binary)

This file implements the **Hook B** pattern for the Markov(1) setting:

* pick a **countable family** of tractable Markov(1) predictors (here: symmetric Beta priors),
* put a **hyperprior** (a weight sequence summing to 1) on that family, and
* form the Bayesian mixture (a `PrefixMeasure`) which dominates each component by its weight.

This gives a theorem-grade, checkable statement that “choosing a prior” can itself be done by a
mixture (and then universal prediction competes with that mixture once it is shown LSC/enumerated).

For now we keep the family simple: one parameter `a > 0` used as `Beta(a,a)` for **both** transition
rows.  This is the binary special case of a per-row Dirichlet prior (Markov‑Dirichlet).
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction

open scoped Classical BigOperators

open FiniteHorizon
open Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge

/-! ## A countable symmetric Markov-Beta family -/

namespace MarkovHyperprior

open Mettapedia.UniversalAI.UniversalPrediction

/-- A simple countable positive grid of symmetric Beta parameters.

We use the half-integers `(n+1)/2`, so the family includes:
* `n = 0`  → `a = 1/2` (Jeffreys/KT),
* `n = 1`  → `a = 1`   (Laplace),
* `n = 2`  → `a = 3/2`, etc.
-/
def a (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ) / 2

lemma a_pos (n : ℕ) : 0 < a n := by
  unfold a
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by
    exact_mod_cast Nat.succ_pos n
  -- Divide by the positive constant 2.
  have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
  exact div_pos hn h2

/-- Symmetric Markov(1) predictor: `Beta(a,a)` priors for both transition rows. -/
noncomputable def markovSymmetric (n : ℕ) : PrefixMeasure :=
  markovBetaPrefixMeasure (α0 := a n) (β0 := a n) (α1 := a n) (β1 := a n)
    (a_pos n) (a_pos n) (a_pos n) (a_pos n)

/-! ## Hyperprior mixture over the family -/

/-- Hyperprior weight on the index `n`. We reuse the canonical self-delimiting weights
`2^{-(n+1)}` which sum to `1`. -/
noncomputable def w (n : ℕ) : ENNReal := geometricWeight n

theorem tsum_w : (∑' n : ℕ, w n) = 1 := by
  simpa [w] using (tsum_geometricWeight : (∑' n : ℕ, geometricWeight n) = 1)

/-- The hyperprior mixture predictor over the symmetric Markov(1) family. -/
noncomputable def mixture : PrefixMeasure :=
  xiPrefixMeasure (ν := fun n : ℕ => (markovSymmetric n)) (w := w) (hw := tsum_w)

/-! ## Componentwise dominance and the immediate KL bound -/

theorem dominates_component (n : ℕ) :
    Dominates mixture.toSemimeasure (markovSymmetric n) (w n) := by
  intro x
  -- Unfold the mixture: its underlying function is `xiFun`.
  unfold mixture xiPrefixMeasure PrefixMeasure.toSemimeasure
  -- Reduce to the generic “term ≤ tsum” lemma.
  simpa [xiFun, w] using
    (xi_dominates_index
      (ν := fun i : ℕ => (markovSymmetric i).toSemimeasure)
      (w := w) (i := n) (x := x))

theorem relEntropy_le_log_inv_component (n N : ℕ) :
    relEntropy (markovSymmetric n) mixture.toSemimeasure N ≤ Real.log (1 / (w n).toReal) := by
  have hdom : Dominates mixture.toSemimeasure (markovSymmetric n) (w n) :=
    dominates_component (n := n)
  have hw0 : w n ≠ 0 := by
    -- `geometricWeight n = 2^{-(n+1)}` is strictly positive in `ENNReal`.
    have hpos : 0 < w n := by
      -- Use `ENNReal.zpow_pos` (base `2` is neither `0` nor `∞`).
      have h2_0 : (2 : ENNReal) ≠ 0 := by norm_num
      have h2_top : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
      simpa [w, geometricWeight] using (ENNReal.zpow_pos (a := (2 : ENNReal)) h2_0 h2_top (-1 - (n : ℤ)))
    exact ne_of_gt hpos
  exact relEntropy_le_log_inv_of_dominates (μ := markovSymmetric n) (ξ := mixture.toSemimeasure)
    (hdom := hdom) (hc0 := hw0) N

/-! ## Best-expert bound (Hook B) -/

theorem markovSymmetric_ne_zero (n : ℕ) : ∀ xs : BinString, markovSymmetric n xs ≠ 0 := by
  intro xs
  -- `markovSymmetric n` is a Markov-Beta prefix-measure with strictly positive hyperparameters.
  simpa [markovSymmetric] using
    (markovBetaPrefixMeasure_ne_zero (α0 := a n) (β0 := a n) (α1 := a n) (β1 := a n)
      (a_pos n) (a_pos n) (a_pos n) (a_pos n) xs)

/-- **Hook B**: the mixture competes with every component on every environment `μ`.

This is the standard “best expert + log(1/w)” regret inequality derived directly from dominance.
-/
theorem relEntropy_le_component_add_log (μ : PrefixMeasure) (n N : ℕ) :
    relEntropy μ mixture.toSemimeasure N ≤
      relEntropy μ (markovSymmetric n).toSemimeasure N + Real.log (1 / (w n).toReal) := by
  have hdom : Dominates mixture.toSemimeasure (markovSymmetric n) (w n) :=
    dominates_component (n := n)
  have hw0 : w n ≠ 0 := by
    have hpos : 0 < w n := by
      have h2_0 : (2 : ENNReal) ≠ 0 := by norm_num
      have h2_top : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
      simpa [w, geometricWeight] using (ENNReal.zpow_pos (a := (2 : ENNReal)) h2_0 h2_top (-1 - (n : ℤ)))
    exact ne_of_gt hpos
  exact FiniteHorizon.relEntropy_le_add_log_inv_of_dominates_right
    (μ := μ) (ξ := mixture.toSemimeasure) (η := markovSymmetric n)
    (hdom := hdom) (hc0 := hw0) (hη0 := markovSymmetric_ne_zero (n := n)) N

/-- The hyperprior mixture assigns nonzero weight to every finite prefix. -/
theorem mixture_ne_zero : ∀ xs : BinString, mixture xs ≠ 0 := by
  intro xs
  have hdom : Dominates mixture.toSemimeasure (markovSymmetric 0) (w 0) :=
    dominates_component (n := 0)
  have hleft0 : w 0 * (markovSymmetric 0) xs ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · -- `w 0` is strictly positive.
      have hpos : 0 < w 0 := by
        have h2_0 : (2 : ENNReal) ≠ 0 := by norm_num
        have h2_top : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
        simpa [w, geometricWeight] using (ENNReal.zpow_pos (a := (2 : ENNReal)) h2_0 h2_top (-1 - (0 : ℤ)))
      exact ne_of_gt hpos
    · simpa using markovSymmetric_ne_zero (n := 0) xs
  intro hmix0
  have hle : w 0 * (markovSymmetric 0) xs ≤ mixture.toSemimeasure xs := hdom xs
  have : w 0 * (markovSymmetric 0) xs ≤ 0 := by simpa [hmix0] using hle
  have : w 0 * (markovSymmetric 0) xs = 0 := le_antisymm this (by simp)
  exact hleft0 this

/-! ## Solomonoff competitiveness (requires an LSC witness) -/

/-- If the hyperprior mixture is lower semicomputable, then the Solomonoff-style universal mixture
`M₃(U)` competes with it automatically.

This is the “third layer” in the semantics → Hook‑B mixture → Solomonoff story.
-/
theorem relEntropy_le_mixture_add_Kμ_log2_M₃
    (U : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine)
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM U]
    (μ : PrefixMeasure)
    (hη : Mettapedia.UniversalAI.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure mixture)
    (n : ℕ) :
    relEntropy μ (M₃ (U := U)) n ≤
      relEntropy μ mixture.toSemimeasure n +
        (HutterV3Kpf.Kμ (U := U) mixture : ℝ) * Real.log 2 := by
  simpa using
    (relEntropy_le_competitor_add_Kμ_log2_M₃ (U := U) (μ := μ) (η := mixture)
      (hη := hη) (hη0 := mixture_ne_zero) n)

end MarkovHyperprior

end Mettapedia.UniversalAI.UniversalPrediction
