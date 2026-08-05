import Mettapedia.MachineLearning.NeuralNetworks.Architecture.BatchNormalizationDependence

/-!
# Batch-normalization gradient projection

Santurkar, Tsipras, Ilyas, and Madry,
*How Does Batch Normalization Help Optimization?* (arXiv:1805.11604),
Fact C.1 and Theorem 4.1 identify the exact activation-gradient map through
batch normalization.  Apart from the gain-to-standard-deviation ratio, it
removes the constant-batch direction and the normalized-activation direction.

This file proves that finite projection identity directly.  For every
mean-zero normalized activation with squared norm equal to the batch size, the
projected gradient's squared norm is the original squared norm minus the two
explicit nonnegative directional components.  Exact batch normalization with
positive variance satisfies both premises.  The decrease is strict when
either removed component is nonzero, but there is no decrease when the
incoming gradient is already orthogonal to both directions.

The source's Hessian comparison, global or regional smoothness claims,
weight-space minimax bound, initialization claim, and empirical optimization
results are not formalized here.  Runtime use requires the actual batch,
activation gradient, gain, standard deviation, and both removed components.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace BatchNormalizationGradientProjection

open scoped BigOperators

open LayerNormalizationBoundary

noncomputable section

/-- Finite Euclidean inner product written in the coordinate representation
used by a mini-batch trace. -/
def batchInner {batchRemainder : ℕ}
    (left right : Fin (batchRemainder + 1) → ℝ) : ℝ :=
  ∑ sample, left sample * right sample

/-- Squared Euclidean norm of a finite batch vector. -/
def batchNormSq {batchRemainder : ℕ}
    (vector : Fin (batchRemainder + 1) → ℝ) : ℝ :=
  batchInner vector vector

/-- The unscaled tangent projection in Fact C.1: subtract the batch mean and
the component along the normalized activation. -/
def batchGradientProjection {batchRemainder : ℕ}
    (normalized gradient : Fin (batchRemainder + 1) → ℝ)
    (sample : Fin (batchRemainder + 1)) : ℝ :=
  gradient sample - layerMean gradient -
    (batchInner gradient normalized / (batchRemainder + 1 : ℝ)) *
      normalized sample

/-- Full gradient pullback through one scalar BatchNorm feature, including
the learned gain divided by the pre-normalization standard deviation. -/
def batchGradientPullback {batchRemainder : ℕ}
    (gain standardDeviation : ℝ)
    (normalized gradient : Fin (batchRemainder + 1) → ℝ)
    (sample : Fin (batchRemainder + 1)) : ℝ :=
  (gain / standardDeviation) *
    batchGradientProjection normalized gradient sample

/-- Exact finite Pythagorean identity behind source Theorem 4.1. -/
theorem batchGradientProjection_normSq_eq
    {batchRemainder : ℕ}
    (normalized gradient : Fin (batchRemainder + 1) → ℝ)
    (normalized_centered : ∑ sample, normalized sample = 0)
    (normalized_normSq :
      batchNormSq normalized = (batchRemainder + 1 : ℝ)) :
    batchNormSq (batchGradientProjection normalized gradient) =
      batchNormSq gradient -
        (∑ sample, gradient sample) ^ 2 /
          (batchRemainder + 1 : ℝ) -
        batchInner gradient normalized ^ 2 /
          (batchRemainder + 1 : ℝ) := by
  let batchSize : ℝ := (batchRemainder + 1 : ℝ)
  let gradientSum : ℝ := ∑ sample, gradient sample
  let activationComponent : ℝ := batchInner gradient normalized
  have batchSize_ne : batchSize ≠ 0 := by
    dsimp [batchSize]
    positivity
  have normalized_normSq' :
      ∑ sample, normalized sample * normalized sample = batchSize := by
    simpa [batchNormSq, batchInner, batchSize] using normalized_normSq
  have scalar_projection_identity (base : ℝ) :
      base -
          2 * (gradientSum / batchSize) * gradientSum -
          2 * (activationComponent / batchSize) * activationComponent +
          batchSize * (gradientSum / batchSize) ^ 2 +
          batchSize * (activationComponent / batchSize) ^ 2 =
        base -
          gradientSum ^ 2 / batchSize -
          activationComponent ^ 2 / batchSize := by
    field_simp [batchSize_ne]
    ring
  unfold batchNormSq batchInner batchGradientProjection
  change
    (∑ sample,
      (gradient sample - gradientSum / batchSize -
          (activationComponent / batchSize) * normalized sample) *
        (gradient sample - gradientSum / batchSize -
          (activationComponent / batchSize) * normalized sample)) = _
  have expand_sample (sample : Fin (batchRemainder + 1)) :
      (gradient sample - gradientSum / batchSize -
          (activationComponent / batchSize) * normalized sample) *
        (gradient sample - gradientSum / batchSize -
          (activationComponent / batchSize) * normalized sample) =
      gradient sample * gradient sample -
          (2 * (gradientSum / batchSize)) * gradient sample -
          (2 * (activationComponent / batchSize)) *
            (gradient sample * normalized sample) +
          (gradientSum / batchSize) ^ 2 +
          (2 * (gradientSum / batchSize) *
            (activationComponent / batchSize)) * normalized sample +
          (activationComponent / batchSize) ^ 2 *
            (normalized sample * normalized sample) := by
    ring
  simp_rw [expand_sample]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rw [normalized_centered, normalized_normSq']
  simp only [mul_zero, add_zero, nsmul_eq_mul]
  rw [show (∑ sample, gradient sample) = gradientSum by rfl,
    show (∑ sample, gradient sample * normalized sample) =
      activationComponent by rfl,
    show (↑(batchRemainder + 1) : ℝ) = batchSize by
      norm_num [batchSize],
    show (↑batchRemainder + 1 : ℝ) = batchSize by
      norm_num [batchSize]]
  nlinarith [
    scalar_projection_identity
      (∑ sample, gradient sample * gradient sample)]

/-- The complete gain-scaled gradient has the same two-component
decomposition. -/
theorem batchGradientPullback_normSq_eq
    {batchRemainder : ℕ}
    (gain standardDeviation : ℝ)
    (normalized gradient : Fin (batchRemainder + 1) → ℝ)
    (normalized_centered : ∑ sample, normalized sample = 0)
    (normalized_normSq :
      batchNormSq normalized = (batchRemainder + 1 : ℝ)) :
    batchNormSq
        (batchGradientPullback gain standardDeviation normalized gradient) =
      (gain / standardDeviation) ^ 2 *
        (batchNormSq gradient -
          (∑ sample, gradient sample) ^ 2 /
            (batchRemainder + 1 : ℝ) -
          batchInner gradient normalized ^ 2 /
            (batchRemainder + 1 : ℝ)) := by
  unfold batchNormSq batchInner batchGradientPullback
  simp_rw [show
      (gain / standardDeviation *
          batchGradientProjection normalized gradient _) *
        (gain / standardDeviation *
          batchGradientProjection normalized gradient _) =
        (gain / standardDeviation) ^ 2 *
          (batchGradientProjection normalized gradient _ *
            batchGradientProjection normalized gradient _) by ring]
  rw [← Finset.mul_sum]
  have projection_identity :=
    batchGradientProjection_normSq_eq normalized gradient
      normalized_centered normalized_normSq
  unfold batchNormSq batchInner at projection_identity
  rw [projection_identity]

/-- Projection cannot increase squared gradient norm. -/
theorem batchGradientProjection_normSq_le
    {batchRemainder : ℕ}
    (normalized gradient : Fin (batchRemainder + 1) → ℝ)
    (normalized_centered : ∑ sample, normalized sample = 0)
    (normalized_normSq :
      batchNormSq normalized = (batchRemainder + 1 : ℝ)) :
    batchNormSq (batchGradientProjection normalized gradient) ≤
      batchNormSq gradient := by
  rw [batchGradientProjection_normSq_eq normalized gradient
    normalized_centered normalized_normSq]
  have batchSize_nonnegative :
      0 ≤ (batchRemainder + 1 : ℝ) := by positivity
  have meanComponent_nonnegative :
      0 ≤ (∑ sample, gradient sample) ^ 2 /
        (batchRemainder + 1 : ℝ) :=
    div_nonneg (sq_nonneg _) batchSize_nonnegative
  have activationComponent_nonnegative :
      0 ≤ batchInner gradient normalized ^ 2 /
        (batchRemainder + 1 : ℝ) :=
    div_nonneg (sq_nonneg _) batchSize_nonnegative
  linarith

/-- The norm decrease is strict whenever either projected-away component is
nonzero. -/
theorem batchGradientProjection_normSq_lt
    {batchRemainder : ℕ}
    (normalized gradient : Fin (batchRemainder + 1) → ℝ)
    (normalized_centered : ∑ sample, normalized sample = 0)
    (normalized_normSq :
      batchNormSq normalized = (batchRemainder + 1 : ℝ))
    (removed_nonzero :
      (∑ sample, gradient sample) ≠ 0 ∨
        batchInner gradient normalized ≠ 0) :
    batchNormSq (batchGradientProjection normalized gradient) <
      batchNormSq gradient := by
  rw [batchGradientProjection_normSq_eq normalized gradient
    normalized_centered normalized_normSq]
  have batchSize_pos : 0 < (batchRemainder + 1 : ℝ) := by positivity
  have meanComponent_nonnegative :
      0 ≤ (∑ sample, gradient sample) ^ 2 /
        (batchRemainder + 1 : ℝ) :=
    div_nonneg (sq_nonneg _) batchSize_pos.le
  have activationComponent_nonnegative :
      0 ≤ batchInner gradient normalized ^ 2 /
        (batchRemainder + 1 : ℝ) :=
    div_nonneg (sq_nonneg _) batchSize_pos.le
  rcases removed_nonzero with mean_nonzero | activation_nonzero
  · have meanComponent_pos :
        0 < (∑ sample, gradient sample) ^ 2 /
          (batchRemainder + 1 : ℝ) :=
      div_pos (sq_pos_of_ne_zero mean_nonzero) batchSize_pos
    linarith
  · have activationComponent_pos :
        0 < batchInner gradient normalized ^ 2 /
          (batchRemainder + 1 : ℝ) :=
      div_pos (sq_pos_of_ne_zero activation_nonzero) batchSize_pos
    linarith

/-- A gradient already orthogonal to both removed directions is unchanged. -/
theorem batchGradientProjection_eq_gradient_of_orthogonal
    {batchRemainder : ℕ}
    (normalized gradient : Fin (batchRemainder + 1) → ℝ)
    (gradient_centered : ∑ sample, gradient sample = 0)
    (gradient_orthogonal :
      batchInner gradient normalized = 0) :
    batchGradientProjection normalized gradient = gradient := by
  funext sample
  have gradient_mean_zero : layerMean gradient = 0 := by
    simp [layerMean, gradient_centered]
  simp [batchGradientProjection, gradient_mean_zero,
    gradient_orthogonal]

/-- The normalized activation direction itself is removed completely. -/
theorem batchGradientProjection_self_eq_zero
    {batchRemainder : ℕ}
    (normalized : Fin (batchRemainder + 1) → ℝ)
    (normalized_centered : ∑ sample, normalized sample = 0)
    (normalized_normSq :
      batchNormSq normalized = (batchRemainder + 1 : ℝ)) :
    batchGradientProjection normalized normalized = fun _ => 0 := by
  funext sample
  have normalized_mean_zero : layerMean normalized = 0 := by
    simp [layerMean, normalized_centered]
  have batchSize_ne : (batchRemainder + 1 : ℝ) ≠ 0 := by positivity
  have normalized_inner :
      batchInner normalized normalized =
        (batchRemainder + 1 : ℝ) := by
    simpa [batchNormSq] using normalized_normSq
  simp [batchGradientProjection, normalized_mean_zero, normalized_inner,
    batchSize_ne]

/-- Exact finite BatchNorm with positive variance supplies the norm premise
used by Fact C.1. -/
theorem exactLayerNormalize_batchNormSq_eq_card
    {batchRemainder : ℕ}
    (activation : Fin (batchRemainder + 1) → ℝ)
    (variance_pos : 0 < layerVariance activation) :
    batchNormSq (exactLayerNormalize activation) =
      (batchRemainder + 1 : ℝ) := by
  have source_second_moment :=
    exactLayerNormalize_secondMoment_eq_one activation variance_pos
  have batchSize_ne : (batchRemainder + 1 : ℝ) ≠ 0 := by positivity
  field_simp [batchSize_ne] at source_second_moment
  simpa [batchNormSq, batchInner, pow_two] using source_second_moment

/-- Source Theorem 4.1 recovered for the actual finite exact-normalization
operator. -/
theorem exactBatchNorm_gradientPullback_normSq_eq
    {batchRemainder : ℕ}
    (gain : ℝ)
    (activation gradient : Fin (batchRemainder + 1) → ℝ)
    (variance_pos : 0 < layerVariance activation) :
    batchNormSq
        (batchGradientPullback gain (layerStd activation)
          (exactLayerNormalize activation) gradient) =
      (gain / layerStd activation) ^ 2 *
        (batchNormSq gradient -
          (∑ sample, gradient sample) ^ 2 /
            (batchRemainder + 1 : ℝ) -
          batchInner gradient (exactLayerNormalize activation) ^ 2 /
            (batchRemainder + 1 : ℝ)) := by
  apply batchGradientPullback_normSq_eq
  · exact sum_exactLayerNormalize_eq_zero activation
  · exact exactLayerNormalize_batchNormSq_eq_card activation variance_pos

private def alternatingFour : Fin 4 → ℝ :=
  fun sample =>
    if sample.val = 0 then 1
    else if sample.val = 1 then -1
    else if sample.val = 2 then 1
    else -1

private def orthogonalFour : Fin 4 → ℝ :=
  fun sample =>
    if sample.val = 0 then 1
    else if sample.val = 1 then 1
    else -1

theorem alternatingFour_centered :
    ∑ sample, alternatingFour sample = 0 := by
  rw [Fin.sum_univ_four]
  norm_num [alternatingFour]

theorem alternatingFour_normSq :
    batchNormSq alternatingFour = 4 := by
  unfold batchNormSq batchInner
  rw [Fin.sum_univ_four]
  norm_num [alternatingFour]

theorem orthogonalFour_centered :
    ∑ sample, orthogonalFour sample = 0 := by
  rw [Fin.sum_univ_four]
  norm_num [orthogonalFour]

theorem orthogonalFour_orthogonal :
    batchInner orthogonalFour alternatingFour = 0 := by
  unfold batchInner
  rw [Fin.sum_univ_four]
  norm_num [orthogonalFour, alternatingFour]

/-- Positive fixture: a gradient parallel to the normalized activation is
removed completely. -/
theorem alternatingFour_self_projection :
    batchGradientProjection alternatingFour alternatingFour =
        (fun _ => 0) ∧
      batchNormSq alternatingFour = 4 := by
  constructor
  · have normalized_normSq :
        batchNormSq alternatingFour = (3 + 1 : ℝ) := by
        rw [alternatingFour_normSq]
        norm_num
    exact batchGradientProjection_self_eq_zero alternatingFour
      alternatingFour_centered normalized_normSq
  · exact alternatingFour_normSq

/-- Negative boundary: a nonzero gradient orthogonal to both removed
directions is unchanged. -/
theorem orthogonalFour_projection_unchanged :
    batchGradientProjection alternatingFour orthogonalFour =
        orthogonalFour ∧
      batchNormSq orthogonalFour = 4 := by
  constructor
  · exact batchGradientProjection_eq_gradient_of_orthogonal
      alternatingFour orthogonalFour orthogonalFour_centered
      orthogonalFour_orthogonal
  · unfold batchNormSq batchInner
    rw [Fin.sum_univ_four]
    norm_num [orthogonalFour]

#print axioms batchGradientProjection_normSq_eq
#print axioms batchGradientPullback_normSq_eq
#print axioms batchGradientProjection_normSq_le
#print axioms batchGradientProjection_normSq_lt
#print axioms batchGradientProjection_eq_gradient_of_orthogonal
#print axioms batchGradientProjection_self_eq_zero
#print axioms exactLayerNormalize_batchNormSq_eq_card
#print axioms exactBatchNorm_gradientPullback_normSq_eq
#print axioms alternatingFour_self_projection
#print axioms orthogonalFour_projection_unchanged

end

end BatchNormalizationGradientProjection

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
