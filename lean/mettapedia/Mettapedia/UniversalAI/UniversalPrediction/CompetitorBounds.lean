import Mettapedia.UniversalAI.UniversalPrediction.FiniteHorizon
import Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge

/-!
# Competitor Bounds (Hook B meets M₃)

This file packages the key composition step for **Hook B**:

* a universal predictor (here `M₃(U)`) dominates any lower-semicomputable competitor `η`, and
* dominance implies the standard “best expert + complexity” KL-regret bound

`Dₙ(μ‖M₃) ≤ Dₙ(μ‖η) + K(η) * log 2`.

The heavy lifting is split cleanly:
* `FiniteHorizon.relEntropy_le_add_log_inv_of_dominates_right` is the pure log-loss algebra;
* `SolomonoffBridge.dominates_M₃_of_LSC_Kμ` provides the `2^{-K}` dominance constant.
-/

namespace Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge

open scoped Classical BigOperators ENNReal

open FiniteHorizon
open Mettapedia.UniversalAI.SolomonoffPrior

/-- **Universal competitiveness** (Hutter-style):

If `η` is a lower-semicomputable (enumerable) predictor, then the universal mixture `M₃(U)`
incurs at most an additive `K(η) * log 2` KL-regret compared to `η` on any true environment `μ`.

This is the theorem-grade form that Hook B needs: pick a countable family of tractable predictors
(e.g. conjugate priors), take a mixture over them, and then apply this lemma to each component.
-/
theorem relEntropy_le_competitor_add_Kμ_log2_M₃
    (U : PrefixFreeMachine) [UniversalPFM U]
    (μ η : PrefixMeasure)
    (hη : Mettapedia.UniversalAI.UniversalPrediction.HutterEnumeration.LowerSemicomputablePrefixMeasure η)
    (hη0 : ∀ x : BinString, η x ≠ 0)
    (n : ℕ) :
    relEntropy μ (M₃ (U := U)) n ≤
      relEntropy μ η.toSemimeasure n + (HutterV3Kpf.Kμ (U := U) η : ℝ) * Real.log 2 := by
  have hdom :
      Dominates (M₃ (U := U)) η ((2 : ENNReal) ^ (-(HutterV3Kpf.Kμ (U := U) η : ℤ))) :=
    dominates_M₃_of_LSC_Kμ (U := U) (μ := η) hη
  have hc0 : ((2 : ENNReal) ^ (-(HutterV3Kpf.Kμ (U := U) η : ℤ))) ≠ 0 := by
    -- In `ENNReal`, a `zpow` of a finite, nonzero base is strictly positive.
    have h2_0 : (2 : ENNReal) ≠ 0 := by norm_num
    have h2_top : (2 : ENNReal) ≠ (⊤ : ENNReal) := by simp
    have hpos :
        0 < ((2 : ENNReal) ^ (-(HutterV3Kpf.Kμ (U := U) η : ℤ))) := by
      exact ENNReal.zpow_pos (a := (2 : ENNReal)) h2_0 h2_top (-(HutterV3Kpf.Kμ (U := U) η : ℤ))
    exact ne_of_gt hpos
  have h :=
    FiniteHorizon.relEntropy_le_add_log_inv_of_dominates_right
      (μ := μ) (ξ := M₃ (U := U)) (η := η) (hdom := hdom) (hc0 := hc0) (hη0 := hη0) n
  -- Rewrite the generic `log(1/c)` bound into the standard `K * log 2` form.
  -- Avoid `simp` rewriting `log (1 / c)` into `-log c` and shuffling terms.
  have hlog :
      Real.log (1 / ((2 : ENNReal) ^ (-(HutterV3Kpf.Kμ (U := U) η : ℤ))).toReal) =
        (HutterV3Kpf.Kμ (U := U) η : ℝ) * Real.log 2 :=
    log_inv_two_zpow_neg (K := HutterV3Kpf.Kμ (U := U) η)
  -- `h` is exactly `relEntropy μ M₃ ≤ relEntropy μ η + log(1/c)`.
  -- Replace the `log(1/c)` term with `K * log 2` without letting simp rearrange the inequality.
  calc
    relEntropy μ (M₃ (U := U)) n ≤
        relEntropy μ η.toSemimeasure n +
          Real.log (1 / ((2 : ENNReal) ^ (-(HutterV3Kpf.Kμ (U := U) η : ℤ))).toReal) := h
    _ = relEntropy μ η.toSemimeasure n + (HutterV3Kpf.Kμ (U := U) η : ℝ) * Real.log 2 := by
        rw [hlog]

end Mettapedia.UniversalAI.UniversalPrediction.SolomonoffBridge
