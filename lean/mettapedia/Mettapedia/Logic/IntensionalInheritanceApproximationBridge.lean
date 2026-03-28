import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mettapedia.Logic.IntensionalInheritanceSolomonoffBridge
import Mettapedia.Logic.UniversalPredictionConditionalApproximation

/-!
# Approximate Intensional Inheritance from Universal-Mixture Approximants

This file lifts the quantitative conditional approximation layer into the
intensional-inheritance bridge.

The key discipline is honest flooring:
- context-mass floors control conditional approximation error,
- conditional-value floors control logarithmic sensitivity.

Positive example:
- if both `P(W | x)` and `P(W | F,x)` stay bounded away from zero, then
  approximate intensional inheritance tracks the full universal-mixture score.

Negative example:
- if either conditional is extremely small, logarithmic amplification can
  dominate, so no uniform approximation theorem is claimed.
-/

namespace Mettapedia.Logic.IntensionalInheritance

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.SolomonoffPrior

/-- Prior term read from the `n`-step geometric universal-mixture approximant. -/
noncomputable def approxPriorFromXiGeom
    (ν : ℕ → Semimeasure) (n : ℕ) (x W : BinString) : ℝ :=
  priorFromConditional (xiGeomApproxSemimeasure ν n) x W

/-- Extensional inheritance term read from the `n`-step geometric universal-mixture approximant. -/
noncomputable def approxExtensionalFromXiGeom
    (ν : ℕ → Semimeasure) (n : ℕ) (x F W : BinString) : ℝ :=
  extensionalFromConditional (xiGeomApproxSemimeasure ν n) x F W

/-- Intensional inheritance score read from the `n`-step geometric universal-mixture approximant. -/
noncomputable def approxIntensionalFromXiGeom
    (ν : ℕ → Semimeasure) (n : ℕ) (x F W : BinString) : ℝ :=
  intensionalFromConditional (xiGeomApproxSemimeasure ν n) x F W

theorem approxIntensionalFromXiGeom_eq_log2_ratio
    (ν : ℕ → Semimeasure) (n : ℕ) (x F W : BinString)
    (hPrior : 0 < approxPriorFromXiGeom ν n x W)
    (hExt : 0 < approxExtensionalFromXiGeom ν n x F W) :
    approxIntensionalFromXiGeom ν n x F W =
      Real.log
        (approxExtensionalFromXiGeom ν n x F W /
          approxPriorFromXiGeom ν n x W) /
      Real.log 2 := by
  exact intensionalFromConditional_eq_log2_ratio
    (ξ := xiGeomApproxSemimeasure ν n) x F W hPrior hExt

/-- If two positive reals are bounded below by `δ`, their logarithms differ by
at most `|a-b| / δ`. -/
lemma abs_log_sub_le_div_floor_of_le
    {a b δ : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hδb : δ ≤ b) (hab : b ≤ a) :
    |Real.log a - Real.log b| ≤ |a - b| / δ := by
  have ha_pos : 0 < a := lt_of_lt_of_le hδ hδa
  have hb_pos : 0 < b := lt_of_lt_of_le hδ hδb
  have hlog : Real.log a - Real.log b = Real.log (a / b) := by
    rw [Real.log_div ha_pos.ne' hb_pos.ne']
  have hratio_ge : 1 ≤ a / b := (one_le_div₀ hb_pos).2 hab
  have hratio_pos : 0 < a / b := by positivity
  calc
    |Real.log a - Real.log b| = Real.log (a / b) := by
      rw [hlog, abs_of_nonneg (Real.log_nonneg hratio_ge)]
    _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos hratio_pos
    _ = (a - b) / b := by
      field_simp [hb_pos.ne']
    _ ≤ (a - b) / δ := by
      gcongr
      exact sub_nonneg.mpr hab
    _ = |a - b| / δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]

lemma abs_log_sub_le_div_floor
    {a b δ : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hδb : δ ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / δ := by
  by_cases hab : b ≤ a
  · exact abs_log_sub_le_div_floor_of_le hδ hδa hδb hab
  · have hba : a ≤ b := le_of_not_ge hab
    calc
      |Real.log a - Real.log b| = |Real.log b - Real.log a| := by
            rw [abs_sub_comm]
      _ ≤ |b - a| / δ := abs_log_sub_le_div_floor_of_le hδ hδb hδa hba
      _ = |a - b| / δ := by rw [abs_sub_comm]

theorem approxPriorFromXiGeom_abs_sub_le
    (ν : ℕ → Semimeasure) (n : ℕ) (x W : BinString)
    {δ : ENNReal}
    (hδ0 : δ ≠ 0) (hδTop : δ ≠ ⊤)
    (hfloor : δ ≤ (xiGeomApproxSemimeasure ν n) x) :
    |approxPriorFromXiGeom ν n x W -
        priorFromConditional (xiGeomSemimeasure ν) x W|
      ≤ 2 * (geomTailMass n).toReal / δ.toReal := by
  simpa [approxPriorFromXiGeom, priorFromConditional, abs_sub_comm] using
    geomConditionalENN_toReal_abs_sub_le ν n x W hδ0 hδTop hfloor

theorem approxExtensionalFromXiGeom_abs_sub_le
    (ν : ℕ → Semimeasure) (n : ℕ) (x F W : BinString)
    {δ : ENNReal}
    (hδ0 : δ ≠ 0) (hδTop : δ ≠ ⊤)
    (hfloor : δ ≤ (xiGeomApproxSemimeasure ν n) (x ++ F)) :
    |approxExtensionalFromXiGeom ν n x F W -
        extensionalFromConditional (xiGeomSemimeasure ν) x F W|
      ≤ 2 * (geomTailMass n).toReal / δ.toReal := by
  simpa [approxExtensionalFromXiGeom, extensionalFromConditional, abs_sub_comm] using
    geomConditionalENN_toReal_abs_sub_le ν n (x ++ F) W hδ0 hδTop hfloor

theorem approxIntensionalFromXiGeom_abs_sub_le
    (ν : ℕ → Semimeasure) (n : ℕ) (x F W : BinString)
    {δx δxF : ENNReal} {δPrior δExt : ℝ}
    (hδx0 : δx ≠ 0) (hδxTop : δx ≠ ⊤)
    (hδxF0 : δxF ≠ 0) (hδxFTop : δxF ≠ ⊤)
    (hδPrior : 0 < δPrior) (hδExt : 0 < δExt)
    (hCtxPrior : δx ≤ (xiGeomApproxSemimeasure ν n) x)
    (hCtxExt : δxF ≤ (xiGeomApproxSemimeasure ν n) (x ++ F))
    (hPriorApproxFloor : δPrior ≤ approxPriorFromXiGeom ν n x W)
    (hPriorFullFloor : δPrior ≤ priorFromConditional (xiGeomSemimeasure ν) x W)
    (hExtApproxFloor : δExt ≤ approxExtensionalFromXiGeom ν n x F W)
    (hExtFullFloor : δExt ≤ extensionalFromConditional (xiGeomSemimeasure ν) x F W) :
    |approxIntensionalFromXiGeom ν n x F W -
        intensionalFromConditional (xiGeomSemimeasure ν) x F W|
      ≤
        (2 * (geomTailMass n).toReal / (δxF.toReal * δExt) +
          2 * (geomTailMass n).toReal / (δx.toReal * δPrior)) /
        Real.log 2 := by
  have hPriorApproxPos : 0 < approxPriorFromXiGeom ν n x W :=
    lt_of_lt_of_le hδPrior hPriorApproxFloor
  have hPriorFullPos : 0 < priorFromConditional (xiGeomSemimeasure ν) x W :=
    lt_of_lt_of_le hδPrior hPriorFullFloor
  have hExtApproxPos : 0 < approxExtensionalFromXiGeom ν n x F W :=
    lt_of_lt_of_le hδExt hExtApproxFloor
  have hExtFullPos : 0 < extensionalFromConditional (xiGeomSemimeasure ν) x F W :=
    lt_of_lt_of_le hδExt hExtFullFloor
  have hPriorErr :
      |approxPriorFromXiGeom ν n x W -
          priorFromConditional (xiGeomSemimeasure ν) x W|
        ≤ 2 * (geomTailMass n).toReal / δx.toReal :=
    approxPriorFromXiGeom_abs_sub_le ν n x W hδx0 hδxTop hCtxPrior
  have hExtErr :
      |approxExtensionalFromXiGeom ν n x F W -
          extensionalFromConditional (xiGeomSemimeasure ν) x F W|
        ≤ 2 * (geomTailMass n).toReal / δxF.toReal :=
    approxExtensionalFromXiGeom_abs_sub_le ν n x F W hδxF0 hδxFTop hCtxExt
  have hLogPrior :
      |Real.log (approxPriorFromXiGeom ν n x W) -
          Real.log (priorFromConditional (xiGeomSemimeasure ν) x W)|
        ≤
          |approxPriorFromXiGeom ν n x W -
            priorFromConditional (xiGeomSemimeasure ν) x W| / δPrior :=
    abs_log_sub_le_div_floor hδPrior hPriorApproxFloor hPriorFullFloor
  have hLogExt :
      |Real.log (approxExtensionalFromXiGeom ν n x F W) -
          Real.log (extensionalFromConditional (xiGeomSemimeasure ν) x F W)|
        ≤
          |approxExtensionalFromXiGeom ν n x F W -
            extensionalFromConditional (xiGeomSemimeasure ν) x F W| / δExt :=
    abs_log_sub_le_div_floor hδExt hExtApproxFloor hExtFullFloor
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [approxIntensionalFromXiGeom_eq_log2_ratio ν n x F W hPriorApproxPos hExtApproxPos,
    intensionalFromXiGeom_eq_log2_ratio ν x F W hPriorFullPos hExtFullPos]
  have hdiv :
      Real.log
          (approxExtensionalFromXiGeom ν n x F W / approxPriorFromXiGeom ν n x W) /
          Real.log 2 -
        Real.log
          (extensionalFromConditional (xiGeomSemimeasure ν) x F W /
            priorFromConditional (xiGeomSemimeasure ν) x W) /
          Real.log 2 =
        (Real.log
            (approxExtensionalFromXiGeom ν n x F W / approxPriorFromXiGeom ν n x W) -
          Real.log
            (extensionalFromConditional (xiGeomSemimeasure ν) x F W /
              priorFromConditional (xiGeomSemimeasure ν) x W)) /
          Real.log 2 := by
    field_simp [hlog2.ne']
  rw [hdiv, abs_div, abs_of_pos hlog2]
  rw [Real.log_div (ne_of_gt hExtApproxPos) (ne_of_gt hPriorApproxPos),
    Real.log_div (ne_of_gt hExtFullPos) (ne_of_gt hPriorFullPos)]
  calc
    |(Real.log (approxExtensionalFromXiGeom ν n x F W) -
        Real.log (approxPriorFromXiGeom ν n x W)) -
      (Real.log (extensionalFromConditional (xiGeomSemimeasure ν) x F W) -
        Real.log (priorFromConditional (xiGeomSemimeasure ν) x W))| /
        Real.log 2
        ≤
        (|Real.log (approxExtensionalFromXiGeom ν n x F W) -
            Real.log (extensionalFromConditional (xiGeomSemimeasure ν) x F W)| +
          |Real.log (approxPriorFromXiGeom ν n x W) -
            Real.log (priorFromConditional (xiGeomSemimeasure ν) x W)|) /
          Real.log 2 := by
            gcongr
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (abs_sub
                (Real.log (approxExtensionalFromXiGeom ν n x F W) -
                  Real.log (extensionalFromConditional (xiGeomSemimeasure ν) x F W))
                (Real.log (approxPriorFromXiGeom ν n x W) -
                  Real.log (priorFromConditional (xiGeomSemimeasure ν) x W)))
    _ ≤
        ((|approxExtensionalFromXiGeom ν n x F W -
            extensionalFromConditional (xiGeomSemimeasure ν) x F W| / δExt) +
          (|approxPriorFromXiGeom ν n x W -
            priorFromConditional (xiGeomSemimeasure ν) x W| / δPrior)) /
          Real.log 2 := by
            gcongr
    _ ≤
        ((2 * (geomTailMass n).toReal / δxF.toReal) / δExt +
          (2 * (geomTailMass n).toReal / δx.toReal) / δPrior) /
          Real.log 2 := by
            gcongr
    _ = (2 * (geomTailMass n).toReal / (δxF.toReal * δExt) +
          2 * (geomTailMass n).toReal / (δx.toReal * δPrior)) /
        Real.log 2 := by
          field_simp [hδPrior.ne', hδExt.ne', ENNReal.toReal_pos hδx0 hδxTop,
            ENNReal.toReal_pos hδxF0 hδxFTop, hlog2.ne']

end Mettapedia.Logic.IntensionalInheritance
