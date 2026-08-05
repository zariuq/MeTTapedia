import Mettapedia.MachineLearning.NeuralNetworks.Architecture.LayerNormalizationBoundary

/-!
# Batch-normalization dependence and restoration boundary

Ioffe and Szegedy, *Batch Normalization* (2015), Algorithm 1 normalize each
scalar feature using the mean and population variance of its current
mini-batch, add a positive stabilizer under the square root, then apply a
learned gain and bias.

The finite-population algebra is shared with layer normalization, but the
index now denotes examples rather than features.  This file formalizes the
consequences specific to that interpretation:

* one example's training output can change when only a companion example
  changes;
* batch size one has zero population variance and erases the normalized
  signal;
* a positive stabilizer makes the normalized second moment strictly below one;
* exact identity restoration requires gain `sqrt (variance + epsilon)`, not
  merely `sqrt variance`.

These are the boundaries needed before batch-dependent statistics can be used
inside a recurrent inference or predictive-coding settling loop.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace BatchNormalizationDependence

open LayerNormalizationBoundary

noncomputable section

/-- Algorithm 1 for one scalar feature across a nonempty mini-batch. -/
def batchNormalize {batchRemainder : ℕ}
    (epsilon gain bias : ℝ)
    (batch : Fin (batchRemainder + 1) → ℝ)
    (sample : Fin (batchRemainder + 1)) : ℝ :=
  gain * stabilizedLayerNormalize epsilon batch sample + bias

/-- Inference-time normalization with externally frozen population
statistics.  Unlike `batchNormalize`, this is a pointwise function of the
current example. -/
def frozenPopulationNormalize
    (epsilon gain bias populationMean populationVariance input : ℝ) : ℝ :=
  gain * ((input - populationMean) /
    Real.sqrt (populationVariance + epsilon)) + bias

/-! ## Normalized moments with a positive stabilizer -/

/-- Exact normalized second moment with a stabilizer.  The source's unit
second-moment statement is recovered only when `epsilon = 0`. -/
theorem stabilized_secondMoment_eq_variance_ratio {batchRemainder : ℕ}
    (epsilon : ℝ)
    (batch : Fin (batchRemainder + 1) → ℝ)
    (denominator_pos : 0 < layerVariance batch + epsilon) :
    (∑ sample, (stabilizedLayerNormalize epsilon batch sample) ^ 2) /
        (batchRemainder + 1 : ℝ) =
      layerVariance batch / (layerVariance batch + epsilon) := by
  have width_ne : (batchRemainder + 1 : ℝ) ≠ 0 := by positivity
  have denominator_ne : layerVariance batch + epsilon ≠ 0 :=
    ne_of_gt denominator_pos
  have sqrt_sq :
      (Real.sqrt (layerVariance batch + epsilon)) ^ 2 =
        layerVariance batch + epsilon :=
    Real.sq_sqrt denominator_pos.le
  unfold stabilizedLayerNormalize
  simp_rw [div_pow]
  rw [← Finset.sum_div, sqrt_sq]
  unfold layerVariance
  field_simp

/-- Positive stabilization attenuates the normalized population variance
strictly below one whenever the source variance is positive. -/
theorem stabilized_secondMoment_lt_one {batchRemainder : ℕ}
    (epsilon : ℝ)
    (batch : Fin (batchRemainder + 1) → ℝ)
    (epsilon_pos : 0 < epsilon)
    (variance_pos : 0 < layerVariance batch) :
    (∑ sample, (stabilizedLayerNormalize epsilon batch sample) ^ 2) /
        (batchRemainder + 1 : ℝ) <
      1 := by
  rw [stabilized_secondMoment_eq_variance_ratio]
  · rw [div_lt_one]
    · linarith
    · linarith
  · linarith

/-! ## Batch-size-one and companion dependence -/

theorem singleton_batch_mean (batch : Fin 1 → ℝ) :
    layerMean batch = batch 0 := by
  unfold layerMean
  rw [Fin.sum_univ_one]
  norm_num

theorem singleton_batch_variance (batch : Fin 1 → ℝ) :
    layerVariance batch = 0 := by
  unfold layerVariance
  rw [Fin.sum_univ_one]
  simp [layerCentered, singleton_batch_mean]

/-- With one example, Algorithm 1's normalized signal is zero, so only the
learned bias remains. -/
theorem singleton_batch_output_eq_bias
    (epsilon gain bias : ℝ)
    (batch : Fin 1 → ℝ) :
    batchNormalize epsilon gain bias batch 0 = bias := by
  simp [batchNormalize, stabilizedLayerNormalize, layerCentered,
    singleton_batch_mean, singleton_batch_variance]

private def constantPair (_ : Fin 2) : ℝ := 0

private def changedCompanionPair (sample : Fin 2) : ℝ :=
  if sample = 0 then 0 else 2

theorem changedCompanionPair_mean :
    layerMean changedCompanionPair = 1 := by
  unfold layerMean
  rw [Fin.sum_univ_two]
  norm_num [changedCompanionPair]

theorem changedCompanionPair_variance :
    layerVariance changedCompanionPair = 1 := by
  unfold layerVariance
  rw [Fin.sum_univ_two]
  norm_num [layerCentered, changedCompanionPair_mean,
    changedCompanionPair]

theorem constantPair_output :
    batchNormalize 0 1 0 constantPair 0 = 0 := by
  norm_num [batchNormalize, stabilizedLayerNormalize, layerVariance,
    layerCentered, layerMean, constantPair, Fin.sum_univ_two]

theorem changedCompanionPair_output :
    batchNormalize 0 1 0 changedCompanionPair 0 = -1 := by
  norm_num [batchNormalize, stabilizedLayerNormalize,
    layerCentered, changedCompanionPair_mean,
    changedCompanionPair_variance, changedCompanionPair]

/-- The current example is zero in both batches, yet changing only its
companion changes the training-time output. -/
theorem batch_output_depends_on_companion :
    constantPair 0 = changedCompanionPair 0 ∧
      batchNormalize 0 1 0 constantPair 0 ≠
        batchNormalize 0 1 0 changedCompanionPair 0 := by
  constructor
  · simp [constantPair, changedCompanionPair]
  · rw [constantPair_output, changedCompanionPair_output]
    norm_num

/-! ## Exact affine restoration and the epsilon correction -/

/-- Algorithm 1 can restore the input exactly when its gain is the complete
stabilized denominator and its bias is the batch mean. -/
theorem batchNormalize_restore_input {batchRemainder : ℕ}
    (epsilon : ℝ)
    (batch : Fin (batchRemainder + 1) → ℝ)
    (sample : Fin (batchRemainder + 1))
    (denominator_pos : 0 < layerVariance batch + epsilon) :
    batchNormalize epsilon
        (Real.sqrt (layerVariance batch + epsilon))
        (layerMean batch) batch sample =
      batch sample := by
  have sqrt_ne :
      Real.sqrt (layerVariance batch + epsilon) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 denominator_pos)
  unfold batchNormalize stabilizedLayerNormalize layerCentered
  field_simp
  ring

private def balancedPair (sample : Fin 2) : ℝ :=
  if sample = 0 then -1 else 1

theorem balancedPair_mean :
    layerMean balancedPair = 0 := by
  unfold layerMean
  rw [Fin.sum_univ_two]
  norm_num [balancedPair]

theorem balancedPair_variance :
    layerVariance balancedPair = 1 := by
  unfold layerVariance
  rw [Fin.sum_univ_two]
  norm_num [layerCentered, balancedPair_mean, balancedPair]

/-- With positive epsilon, the source's unstabilized choice
`gain = sqrt variance` does not restore the original activation. -/
theorem unstabilized_gain_does_not_restore_with_epsilon :
    batchNormalize 3 (Real.sqrt (layerVariance balancedPair))
        (layerMean balancedPair) balancedPair 0 ≠
      balancedPair 0 := by
  norm_num [batchNormalize, stabilizedLayerNormalize, layerCentered,
    balancedPair_mean, balancedPair_variance, balancedPair]

/-- The corrected gain `sqrt (variance + epsilon)` does restore the same
stabilized fixture. -/
theorem stabilized_gain_restores :
    batchNormalize 3
        (Real.sqrt (layerVariance balancedPair + 3))
        (layerMean balancedPair) balancedPair 0 =
      balancedPair 0 := by
  exact batchNormalize_restore_input 3 balancedPair 0 (by
    rw [balancedPair_variance]
    norm_num)

#print axioms stabilized_secondMoment_eq_variance_ratio
#print axioms stabilized_secondMoment_lt_one
#print axioms singleton_batch_output_eq_bias
#print axioms batch_output_depends_on_companion
#print axioms batchNormalize_restore_input
#print axioms unstabilized_gain_does_not_restore_with_epsilon
#print axioms stabilized_gain_restores

end

end BatchNormalizationDependence

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
