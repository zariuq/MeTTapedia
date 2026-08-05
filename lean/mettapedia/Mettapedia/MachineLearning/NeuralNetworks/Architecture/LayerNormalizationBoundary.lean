import Mettapedia.MachineLearning.NeuralNetworks.Architecture.HighwayGateBoundary

/-!
# Layer-normalization invariance and stabilization boundary

Ba, Kiros, and Hinton, *Layer Normalization* (2016), define the mean and
standard deviation of the preactivations within one layer in Equation (3).
Equations (6)--(7) use the resulting shift and rescaling invariances.

This file recovers those laws for every nonempty finite layer.  It makes two
scope conditions explicit:

* the rescaling invariance is exact for positive scales; a negative scale
  reverses the normalized direction because the standard deviation scales by
  the absolute value;
* adding a positive stabilizer inside the square root makes the operator
  total at zero variance, but breaks exact positive-rescaling invariance.

These boundaries matter when a normalization identity is used inside a
recurrent or predictive-coding stability argument.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace LayerNormalizationBoundary

noncomputable section

/-! ## Exact finite-width statistics -/

/-- Mean of a nonempty layer of width `width + 1`. -/
def layerMean {width : ℕ} (activation : Fin (width + 1) → ℝ) : ℝ :=
  (∑ index, activation index) / (width + 1 : ℝ)

/-- Coordinate centered by the within-layer mean. -/
def layerCentered {width : ℕ}
    (activation : Fin (width + 1) → ℝ) (index : Fin (width + 1)) : ℝ :=
  activation index - layerMean activation

/-- Population variance used by source Equation (3). -/
def layerVariance {width : ℕ} (activation : Fin (width + 1) → ℝ) : ℝ :=
  (∑ index, (layerCentered activation index) ^ 2) /
    (width + 1 : ℝ)

/-- Population standard deviation used by source Equation (3). -/
def layerStd {width : ℕ} (activation : Fin (width + 1) → ℝ) : ℝ :=
  Real.sqrt (layerVariance activation)

/-- Exact source normalization, totalized by Lean's division at zero. -/
def exactLayerNormalize {width : ℕ}
    (activation : Fin (width + 1) → ℝ) (index : Fin (width + 1)) : ℝ :=
  layerCentered activation index / layerStd activation

/-- Numerically stabilized normalization used by common implementations. -/
def stabilizedLayerNormalize {width : ℕ}
    (epsilon : ℝ)
    (activation : Fin (width + 1) → ℝ)
    (index : Fin (width + 1)) : ℝ :=
  layerCentered activation index /
    Real.sqrt (layerVariance activation + epsilon)

theorem layerMean_add_const {width : ℕ}
    (activation : Fin (width + 1) → ℝ) (shift : ℝ) :
    layerMean (fun index => activation index + shift) =
      layerMean activation + shift := by
  unfold layerMean
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have width_ne : (width + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem layerCentered_add_const {width : ℕ}
    (activation : Fin (width + 1) → ℝ) (shift : ℝ)
    (index : Fin (width + 1)) :
    layerCentered (fun coordinate => activation coordinate + shift) index =
      layerCentered activation index := by
  simp [layerCentered, layerMean_add_const]

/-- Centering makes the within-layer coordinate sum exactly zero. -/
theorem sum_layerCentered_eq_zero {width : ℕ}
    (activation : Fin (width + 1) → ℝ) :
    ∑ index, layerCentered activation index = 0 := by
  unfold layerCentered layerMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have width_ne : (width + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem layerVariance_add_const {width : ℕ}
    (activation : Fin (width + 1) → ℝ) (shift : ℝ) :
    layerVariance (fun index => activation index + shift) =
      layerVariance activation := by
  unfold layerVariance
  simp_rw [layerCentered_add_const]

theorem exactLayerNormalize_add_const {width : ℕ}
    (activation : Fin (width + 1) → ℝ) (shift : ℝ)
    (index : Fin (width + 1)) :
    exactLayerNormalize (fun coordinate => activation coordinate + shift)
        index =
      exactLayerNormalize activation index := by
  simp [exactLayerNormalize, layerStd, layerCentered_add_const,
    layerVariance_add_const]

/-- Exact layer normalization remains centered, including the totalized
zero-variance case. -/
theorem sum_exactLayerNormalize_eq_zero {width : ℕ}
    (activation : Fin (width + 1) → ℝ) :
    ∑ index, exactLayerNormalize activation index = 0 := by
  unfold exactLayerNormalize
  rw [← Finset.sum_div, sum_layerCentered_eq_zero]
  simp

theorem layerMean_exactLayerNormalize_eq_zero {width : ℕ}
    (activation : Fin (width + 1) → ℝ) :
    layerMean (exactLayerNormalize activation) = 0 := by
  simp [layerMean, sum_exactLayerNormalize_eq_zero]

/-- For a nonconstant layer, exact normalization has unit population second
moment.  Combined with the preceding zero-mean theorem, this is unit
population variance. -/
theorem exactLayerNormalize_secondMoment_eq_one {width : ℕ}
    (activation : Fin (width + 1) → ℝ)
    (variance_pos : 0 < layerVariance activation) :
    (∑ index, (exactLayerNormalize activation index) ^ 2) /
        (width + 1 : ℝ) =
      1 := by
  have width_ne : (width + 1 : ℝ) ≠ 0 := by positivity
  have variance_ne : layerVariance activation ≠ 0 :=
    ne_of_gt variance_pos
  have std_sq :
      (layerStd activation) ^ 2 = layerVariance activation := by
    unfold layerStd
    exact Real.sq_sqrt variance_pos.le
  have sum_sq_ne :
      (∑ index, (layerCentered activation index) ^ 2) ≠ 0 := by
    intro sum_zero
    apply variance_ne
    simp [layerVariance, sum_zero]
  unfold exactLayerNormalize
  simp_rw [div_pow]
  rw [← Finset.sum_div, std_sq]
  unfold layerVariance at variance_ne ⊢
  field_simp [sum_sq_ne]

/-- Exact normalization therefore has unit population variance whenever the
source variance is positive. -/
theorem layerVariance_exactLayerNormalize_eq_one {width : ℕ}
    (activation : Fin (width + 1) → ℝ)
    (variance_pos : 0 < layerVariance activation) :
    layerVariance (exactLayerNormalize activation) = 1 := by
  rw [layerVariance]
  simp_rw [layerCentered, layerMean_exactLayerNormalize_eq_zero, sub_zero]
  exact exactLayerNormalize_secondMoment_eq_one activation variance_pos

theorem stabilizedLayerNormalize_add_const {width : ℕ}
    (epsilon : ℝ)
    (activation : Fin (width + 1) → ℝ) (shift : ℝ)
    (index : Fin (width + 1)) :
    stabilizedLayerNormalize epsilon
        (fun coordinate => activation coordinate + shift) index =
      stabilizedLayerNormalize epsilon activation index := by
  simp [stabilizedLayerNormalize, layerCentered_add_const,
    layerVariance_add_const]

theorem layerMean_scale {width : ℕ}
    (scale : ℝ) (activation : Fin (width + 1) → ℝ) :
    layerMean (fun index => scale * activation index) =
      scale * layerMean activation := by
  unfold layerMean
  rw [← Finset.mul_sum]
  ring

theorem layerCentered_scale {width : ℕ}
    (scale : ℝ) (activation : Fin (width + 1) → ℝ)
    (index : Fin (width + 1)) :
    layerCentered (fun coordinate => scale * activation coordinate) index =
      scale * layerCentered activation index := by
  simp [layerCentered, layerMean_scale]
  ring

theorem layerVariance_scale {width : ℕ}
    (scale : ℝ) (activation : Fin (width + 1) → ℝ) :
    layerVariance (fun index => scale * activation index) =
      scale ^ 2 * layerVariance activation := by
  unfold layerVariance
  simp_rw [layerCentered_scale, mul_pow]
  rw [← Finset.mul_sum]
  ring

theorem layerVariance_nonnegative {width : ℕ}
    (activation : Fin (width + 1) → ℝ) :
    0 ≤ layerVariance activation := by
  unfold layerVariance
  positivity

theorem layerStd_scale {width : ℕ}
    (scale : ℝ) (activation : Fin (width + 1) → ℝ) :
    layerStd (fun index => scale * activation index) =
      |scale| * layerStd activation := by
  rw [layerStd, layerStd, layerVariance_scale,
    Real.sqrt_mul (sq_nonneg scale)]
  rw [Real.sqrt_sq_eq_abs]

/-- Source Equation (7) is exact for a strictly positive rescaling. -/
theorem exactLayerNormalize_pos_scale {width : ℕ}
    (scale : ℝ) (activation : Fin (width + 1) → ℝ)
    (index : Fin (width + 1))
    (scale_pos : 0 < scale) :
    exactLayerNormalize (fun coordinate => scale * activation coordinate)
        index =
      exactLayerNormalize activation index := by
  rw [exactLayerNormalize, exactLayerNormalize, layerCentered_scale,
    layerStd_scale, abs_of_pos scale_pos]
  field_simp

/-- A negative rescaling reverses the normalized direction. -/
theorem exactLayerNormalize_neg_scale {width : ℕ}
    (scale : ℝ) (activation : Fin (width + 1) → ℝ)
    (index : Fin (width + 1))
    (scale_neg : scale < 0) :
    exactLayerNormalize (fun coordinate => scale * activation coordinate)
        index =
      -exactLayerNormalize activation index := by
  rw [exactLayerNormalize, exactLayerNormalize, layerCentered_scale,
    layerStd_scale, abs_of_neg scale_neg]
  have scale_ne : scale ≠ 0 := ne_of_lt scale_neg
  field_simp

/-! ## Exact fixtures and the stabilizer boundary -/

private def opposedPair (index : Fin 2) : ℝ :=
  if index = 0 then -1 else 1

theorem opposedPair_mean :
    layerMean opposedPair = 0 := by
  unfold layerMean
  rw [Fin.sum_univ_two]
  norm_num [opposedPair]

theorem opposedPair_variance :
    layerVariance opposedPair = 1 := by
  unfold layerVariance
  rw [Fin.sum_univ_two]
  norm_num [layerCentered, opposedPair_mean, opposedPair]

theorem negative_scale_not_invariant :
    exactLayerNormalize (fun index => (-1 : ℝ) * opposedPair index) 0 ≠
      exactLayerNormalize opposedPair 0 := by
  rw [exactLayerNormalize_neg_scale (scale := (-1 : ℝ))
    (activation := opposedPair) (index := 0) (by norm_num)]
  have nonzero : exactLayerNormalize opposedPair 0 ≠ 0 := by
    rw [exactLayerNormalize, layerCentered, opposedPair_mean,
      layerStd, opposedPair_variance]
    norm_num [opposedPair]
  intro equality
  apply nonzero
  linarith

/-- A constant layer has zero centered values and zero variance. -/
theorem constant_layer_zero_variance {width : ℕ} (constant : ℝ) :
    layerVariance (fun _ : Fin (width + 1) => constant) = 0 := by
  have mean :
      layerMean (fun _ : Fin (width + 1) => constant) = constant := by
    simpa [layerMean] using
      layerMean_add_const
        (activation := fun _ : Fin (width + 1) => 0) constant
  simp [layerVariance, layerCentered, mean]

/-- The totalized exact operator maps a constant layer to zero.  This is a
formal totalization, not evidence that division by zero is numerically valid. -/
theorem exactLayerNormalize_constant {width : ℕ}
    (constant : ℝ) (index : Fin (width + 1)) :
    exactLayerNormalize (fun _ => constant) index = 0 := by
  have mean :
      layerMean (fun _ : Fin (width + 1) => constant) = constant := by
    simpa [layerMean] using
      layerMean_add_const
        (activation := fun _ : Fin (width + 1) => 0) constant
  simp [exactLayerNormalize, layerCentered, mean]

/-- A positive stabilizer keeps the denominator strictly positive. -/
theorem stabilized_denominator_pos {width : ℕ}
    (epsilon : ℝ) (activation : Fin (width + 1) → ℝ)
    (epsilon_pos : 0 < epsilon) :
    0 < Real.sqrt (layerVariance activation + epsilon) := by
  apply Real.sqrt_pos.2
  linarith [layerVariance_nonnegative activation]

/-- A concrete exact counterexample: with variance one and stabilizer three,
positive scale `11/4` changes the normalized value from `-1/2` to `-11/13`.
Thus stabilized normalization is not exactly scale invariant. -/
theorem positive_scale_stabilized_not_invariant :
    stabilizedLayerNormalize 3
        (fun index => (11 / 4 : ℝ) * opposedPair index) 0 ≠
      stabilizedLayerNormalize 3 opposedPair 0 := by
  have scaledVariance :
      layerVariance (fun index => (11 / 4 : ℝ) * opposedPair index) =
        121 / 16 := by
    rw [layerVariance_scale, opposedPair_variance]
    norm_num
  have sqrtFour : Real.sqrt 4 = 2 := by norm_num
  have sqrtScaled : Real.sqrt (121 / 16 + 3) = 13 / 4 := by
    norm_num
  rw [stabilizedLayerNormalize, stabilizedLayerNormalize,
    layerCentered_scale, layerCentered, opposedPair_mean,
    opposedPair_variance, scaledVariance]
  norm_num [opposedPair, sqrtFour, sqrtScaled]

/-- With no stabilizer, the stabilized definition reduces to the exact source
operator. -/
theorem stabilizedLayerNormalize_zero_epsilon {width : ℕ}
    (activation : Fin (width + 1) → ℝ)
    (index : Fin (width + 1)) :
    stabilizedLayerNormalize 0 activation index =
      exactLayerNormalize activation index := by
  simp [stabilizedLayerNormalize, exactLayerNormalize, layerStd]

#print axioms layerMean_add_const
#print axioms sum_layerCentered_eq_zero
#print axioms layerVariance_add_const
#print axioms layerVariance_exactLayerNormalize_eq_one
#print axioms layerVariance_scale
#print axioms layerStd_scale
#print axioms exactLayerNormalize_pos_scale
#print axioms exactLayerNormalize_neg_scale
#print axioms negative_scale_not_invariant
#print axioms constant_layer_zero_variance
#print axioms positive_scale_stabilized_not_invariant

end

end LayerNormalizationBoundary

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
