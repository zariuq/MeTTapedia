import Mathlib

/-!
# Width scaling and diminishing returns in continual learning

Guha and Lakshman, *On the Diminishing Returns of Width for Continual
Learning* (ICML 2024, arXiv:2403.06398), Theorem 4.1, bound their
continual-learning output drift at width `W` by a source-specific coefficient
times `W⁻ᵝ`, for a positive data-dependent exponent `β`.

This file isolates the exact capacity economics of that displayed power-law
envelope. It proves that positive exponents make the envelope strictly
decrease with width, that equal multiplicative width expansions have
geometrically decreasing absolute benefit, and that a simultaneous increase
in the width-independent load coefficient is offset exactly when it is smaller
than the corresponding width power.

The source network theorem is not reproved here. In particular, this
development does not establish the source's random active-row model,
lazy-training assumption, spectral perturbation estimates, big-O constant, or
empirical fit. The results below apply only after those quantities have been
bound to a positive coefficient and exponent independent of the compared
widths.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace WidthDiminishingReturns

noncomputable section

/-- The width-dependent part of the source's continual-learning drift bound.

`coefficient` collects the task-distance, depth, activation, spectral-norm,
and sparsity terms that must remain fixed during a width comparison. -/
def widthEnvelope (coefficient exponent width : ℝ) : ℝ :=
  coefficient * width ^ (-exponent)

/-- Absolute envelope reduction obtained by multiplying width by `scale`. -/
def scalingGain
    (coefficient exponent scale width : ℝ) : ℝ :=
  widthEnvelope coefficient exponent width -
    widthEnvelope coefficient exponent (scale * width)

/-- A positive coefficient and positive width give a positive envelope for
every real exponent. -/
theorem widthEnvelope_pos
    (coefficient exponent width : ℝ)
    (coefficient_pos : 0 < coefficient)
    (width_pos : 0 < width) :
    0 < widthEnvelope coefficient exponent width := by
  exact mul_pos coefficient_pos (Real.rpow_pos_of_pos width_pos _)

/-- Exact power-law scaling identity. -/
theorem widthEnvelope_scale
    (coefficient exponent scale width : ℝ)
    (scale_pos : 0 < scale)
    (width_pos : 0 < width) :
    widthEnvelope coefficient exponent (scale * width) =
      scale ^ (-exponent) *
        widthEnvelope coefficient exponent width := by
  unfold widthEnvelope
  rw [Real.mul_rpow scale_pos.le width_pos.le]
  ring

/-- Under the source's positive-exponent premise, widening strictly decreases
the power-law envelope. -/
theorem widthEnvelope_strictly_decreases
    (coefficient exponent firstWidth secondWidth : ℝ)
    (coefficient_pos : 0 < coefficient)
    (exponent_pos : 0 < exponent)
    (firstWidth_pos : 0 < firstWidth)
    (width_lt : firstWidth < secondWidth) :
    widthEnvelope coefficient exponent secondWidth <
      widthEnvelope coefficient exponent firstWidth := by
  unfold widthEnvelope
  exact mul_lt_mul_of_pos_left
    (Real.rpow_lt_rpow_of_neg firstWidth_pos width_lt (by linarith))
    coefficient_pos

/-- Equal multiplicative width expansions have gains related by the same
inverse-power factor as the original envelope. -/
theorem scalingGain_scaled_width
    (coefficient exponent scale width : ℝ)
    (scale_pos : 0 < scale)
    (width_pos : 0 < width) :
    scalingGain coefficient exponent scale (scale * width) =
      scale ^ (-exponent) *
        scalingGain coefficient exponent scale width := by
  unfold scalingGain widthEnvelope
  rw [Real.mul_rpow scale_pos.le width_pos.le]
  rw [Real.mul_rpow scale_pos.le (mul_pos scale_pos width_pos).le]
  rw [Real.mul_rpow scale_pos.le width_pos.le]
  ring

/-- Diminishing-returns crown: for a positive exponent and a scale above one,
the next equal multiplicative width expansion still helps, but helps strictly
less than the preceding expansion. -/
theorem scalingGain_strictly_diminishes
    (coefficient exponent scale width : ℝ)
    (coefficient_pos : 0 < coefficient)
    (exponent_pos : 0 < exponent)
    (scale_gt_one : 1 < scale)
    (width_pos : 0 < width) :
    0 < scalingGain coefficient exponent scale (scale * width) ∧
      scalingGain coefficient exponent scale (scale * width) <
        scalingGain coefficient exponent scale width := by
  have scale_pos : 0 < scale := lt_trans (by norm_num) scale_gt_one
  have width_lt_scaled : width < scale * width := by
    nlinarith
  have gain_pos : 0 < scalingGain coefficient exponent scale width := by
    unfold scalingGain
    exact sub_pos.mpr
      (widthEnvelope_strictly_decreases coefficient exponent
        width (scale * width) coefficient_pos exponent_pos
        width_pos width_lt_scaled)
  have factor_pos : 0 < scale ^ (-exponent) :=
    Real.rpow_pos_of_pos scale_pos _
  have factor_lt_one : scale ^ (-exponent) < 1 := by
    rw [Real.rpow_lt_one_iff scale_pos.le]
    exact Or.inr (Or.inl ⟨scale_gt_one, by linarith⟩)
  rw [scalingGain_scaled_width coefficient exponent scale width
    scale_pos width_pos]
  constructor <;>
    nlinarith [mul_pos factor_pos gain_pos]

/-- Exact interaction between increased task/depth load and increased width. -/
theorem load_width_tradeoff_exact
    (coefficient exponent load scale width : ℝ)
    (scale_pos : 0 < scale)
    (width_pos : 0 < width) :
    widthEnvelope (load * coefficient) exponent (scale * width) =
      (load * scale ^ (-exponent)) *
        widthEnvelope coefficient exponent width := by
  rw [widthEnvelope_scale (load * coefficient) exponent scale width
    scale_pos width_pos]
  unfold widthEnvelope
  ring

/-- Capacity/load threshold: after the width-independent coefficient grows by
`load` and width grows by `scale`, the envelope improves exactly when
`load < scale ^ exponent`. -/
theorem load_width_tradeoff_lt_iff
    (coefficient exponent load scale width : ℝ)
    (coefficient_pos : 0 < coefficient)
    (scale_pos : 0 < scale)
    (width_pos : 0 < width) :
    widthEnvelope (load * coefficient) exponent (scale * width) <
        widthEnvelope coefficient exponent width ↔
      load < scale ^ exponent := by
  rw [load_width_tradeoff_exact coefficient exponent load scale width
    scale_pos width_pos]
  have envelope_pos :
      0 < widthEnvelope coefficient exponent width :=
    widthEnvelope_pos coefficient exponent width coefficient_pos width_pos
  have power_pos : 0 < scale ^ exponent :=
    Real.rpow_pos_of_pos scale_pos _
  constructor
  · intro decreased
    have factor_lt_one : load * scale ^ (-exponent) < 1 := by
      by_contra not_lt
      have one_le_factor :
          1 ≤ load * scale ^ (-exponent) :=
        le_of_not_gt not_lt
      have scaled :=
        mul_le_mul_of_nonneg_right one_le_factor envelope_pos.le
      nlinarith
    rw [Real.rpow_neg scale_pos.le] at factor_lt_one
    have divided : load / scale ^ exponent < 1 := by
      simpa [div_eq_mul_inv] using factor_lt_one
    have threshold := (div_lt_iff₀ power_pos).mp divided
    simpa using threshold
  · intro load_lt
    have divided : load / scale ^ exponent < 1 := by
      apply (div_lt_iff₀ power_pos).mpr
      simpa using load_lt
    have factor_lt_one : load * scale ^ (-exponent) < 1 := by
      rw [Real.rpow_neg scale_pos.le]
      simpa [div_eq_mul_inv] using divided
    have decreased :=
      mul_lt_mul_of_pos_right factor_lt_one envelope_pos
    simpa using decreased

/-! ## Positive and negative boundaries -/

/-- If the fitted exponent is zero, changing width produces no improvement. -/
theorem zero_exponent_has_no_width_gain
    (coefficient scale firstWidth secondWidth : ℝ) :
    widthEnvelope coefficient 0 firstWidth =
        widthEnvelope coefficient 0 secondWidth ∧
      scalingGain coefficient 0 scale firstWidth = 0 := by
  simp [widthEnvelope, scalingGain]

/-- If the exponent has the wrong sign, widening makes the envelope strictly
worse. Positivity of the fitted exponent is therefore load-bearing. -/
theorem widthEnvelope_strictly_increases_of_exponent_neg
    (coefficient exponent firstWidth secondWidth : ℝ)
    (coefficient_pos : 0 < coefficient)
    (exponent_neg : exponent < 0)
    (firstWidth_pos : 0 < firstWidth)
    (width_lt : firstWidth < secondWidth) :
    widthEnvelope coefficient exponent firstWidth <
      widthEnvelope coefficient exponent secondWidth := by
  unfold widthEnvelope
  exact mul_lt_mul_of_pos_left
    (Real.rpow_lt_rpow firstWidth_pos.le width_lt (by linarith))
    coefficient_pos

/-- For an inverse-width envelope, doubling width from two to four gains
three units, while doubling again gains only three halves. -/
theorem inverse_width_diminishing :
    widthEnvelope 12 1 2 = 6 ∧
      widthEnvelope 12 1 4 = 3 ∧
      widthEnvelope 12 1 8 = 3 / 2 ∧
      scalingGain 12 1 2 2 = 3 ∧
      scalingGain 12 1 2 4 = 3 / 2 := by
  norm_num [widthEnvelope, scalingGain, Real.rpow_neg_one]

/-- With inverse-width scaling, doubling width offsets a load increase of
three halves. -/
theorem moderate_load_doubling_width_improves :
    widthEnvelope ((3 / 2) * 12) 1 (2 * 2) <
      widthEnvelope 12 1 2 := by
  norm_num [widthEnvelope, Real.rpow_neg_one]

/-- The same width doubling does not offset a tripled load coefficient. -/
theorem tripled_load_doubling_width_worsens :
    widthEnvelope 12 1 2 <
      widthEnvelope (3 * 12) 1 (2 * 2) := by
  norm_num [widthEnvelope, Real.rpow_neg_one]

#print axioms widthEnvelope_scale
#print axioms widthEnvelope_strictly_decreases
#print axioms scalingGain_strictly_diminishes
#print axioms load_width_tradeoff_lt_iff
#print axioms widthEnvelope_strictly_increases_of_exponent_neg
#print axioms tripled_load_doubling_width_worsens

end

end WidthDiminishingReturns

end Mettapedia.MachineLearning.ContinualLearning
