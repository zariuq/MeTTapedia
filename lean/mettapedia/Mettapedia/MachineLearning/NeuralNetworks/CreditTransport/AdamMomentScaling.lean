import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DecoupledWeightDecay

/-!
# Adam moment scaling and stabilization boundaries

Kingma and Ba, *Adam: A Method for Stochastic Optimization*
(arXiv:1412.6980), define exponentially weighted first and second moments,
bias correction, and a stabilized coordinatewise direction.  The primary PDF
has SHA-256
`eab9c73ae2ceda884b94830bda99312254bac4806f6c9f045cbab90721ecda31`.

This file isolates the scalar coordinate algebra behind Algorithm 1,
Sections 2.1 and 3.  Positive gradient rescaling multiplies the first moment by
the scale and the second moment by its square.  Bias correction commutes with
those scalings.  At zero stabilizer the Adam direction is therefore exactly
invariant under positive gradient rescaling.  A fixed positive stabilizer
breaks that invariance in a controlled way: rescaling the gradients is
equivalent to inversely rescaling the stabilizer.

The theorems are coordinatewise and exact.  They do not establish the paper's
online-convex regret claim or infer that a runtime's moment buffers, update
order, or floating-point evaluation match these real recurrences.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace AdamMomentScaling

noncomputable section

/-! ## Moment and bias-correction recurrences -/

def firstMomentStep
    (decay previous gradient : ℝ) : ℝ :=
  decay * previous + (1 - decay) * gradient

def secondMomentStep
    (decay previous gradient : ℝ) : ℝ :=
  decay * previous + (1 - decay) * gradient ^ 2

def biasCorrect
    (decay : ℝ) (time : ℕ) (moment : ℝ) : ℝ :=
  moment / (1 - decay ^ time)

def adamDirection
    (stabilizer first second : ℝ) : ℝ :=
  first / (Real.sqrt second + stabilizer)

theorem firstMomentStep_scale
    (decay previous gradient scale : ℝ) :
    firstMomentStep decay (scale * previous) (scale * gradient) =
      scale * firstMomentStep decay previous gradient := by
  simp only [firstMomentStep]
  ring

theorem secondMomentStep_scale_sq
    (decay previous gradient scale : ℝ) :
    secondMomentStep decay (scale ^ 2 * previous) (scale * gradient) =
      scale ^ 2 * secondMomentStep decay previous gradient := by
  simp only [secondMomentStep]
  ring

theorem biasCorrect_scale
    (decay : ℝ) (time : ℕ) (moment scale : ℝ) :
    biasCorrect decay time (scale * moment) =
      scale * biasCorrect decay time moment := by
  simp only [biasCorrect]
  ring

theorem biasCorrectionDenominator_pos
    {decay : ℝ} (decayNonnegative : 0 ≤ decay)
    (decayLtOne : decay < 1)
    {time : ℕ} (timePositive : 0 < time) :
    0 < 1 - decay ^ time := by
  exact sub_pos.mpr
    (pow_lt_one₀ decayNonnegative decayLtOne (Nat.ne_of_gt timePositive))

/-- The source starts bias correction at time one. At time zero its
denominator is zero, and Lean's total division returns zero rather than a
meaningful corrected estimate. -/
theorem biasCorrect_time_zero
    (decay moment : ℝ) :
    biasCorrect decay 0 moment = 0 := by
  simp [biasCorrect]

theorem secondMomentStep_nonnegative
    {decay previous gradient : ℝ}
    (decayNonnegative : 0 ≤ decay)
    (decayLeOne : decay ≤ 1)
    (previousNonnegative : 0 ≤ previous) :
    0 ≤ secondMomentStep decay previous gradient := by
  simp only [secondMomentStep]
  exact add_nonneg
    (mul_nonneg decayNonnegative previousNonnegative)
    (mul_nonneg (sub_nonneg.mpr decayLeOne) (sq_nonneg gradient))

theorem biasCorrect_second_nonnegative
    {decay previous gradient : ℝ}
    (decayNonnegative : 0 ≤ decay)
    (decayLtOne : decay < 1)
    (previousNonnegative : 0 ≤ previous)
    {time : ℕ} (timePositive : 0 < time) :
    0 ≤ biasCorrect decay time
      (secondMomentStep decay previous gradient) := by
  exact div_nonneg
    (secondMomentStep_nonnegative decayNonnegative
      (le_of_lt decayLtOne) previousNonnegative)
    (le_of_lt
      (biasCorrectionDenominator_pos
        decayNonnegative decayLtOne timePositive))

/-! ## Exact positive-scale transport -/

theorem sqrt_scale_sq
    {scale second : ℝ}
    (scaleNonnegative : 0 ≤ scale) :
    Real.sqrt (scale ^ 2 * second) =
      scale * Real.sqrt second := by
  rw [Real.sqrt_mul (sq_nonneg scale) second]
  rw [Real.sqrt_sq scaleNonnegative]

/-- Section 2.1's exact scale invariance, with the positive-scale hypothesis
made explicit. -/
theorem adamDirection_scale_zeroStabilizer
    {scale first second : ℝ}
    (scalePositive : 0 < scale) :
    adamDirection 0 (scale * first) (scale ^ 2 * second) =
      adamDirection 0 first second := by
  simp only [adamDirection, add_zero]
  rw [sqrt_scale_sq (le_of_lt scalePositive)]
  by_cases rootZero : Real.sqrt second = 0
  · simp [rootZero]
  · field_simp [ne_of_gt scalePositive, rootZero]

/-- With a fixed stabilizer, positive gradient scaling is exactly equivalent
to inverse scaling of the stabilizer. -/
theorem adamDirection_scale_eq_rescaledStabilizer
    {scale stabilizer first second : ℝ}
    (scalePositive : 0 < scale)
    (stabilizerPositive : 0 < stabilizer) :
    adamDirection stabilizer (scale * first) (scale ^ 2 * second) =
      adamDirection (stabilizer / scale) first second := by
  simp only [adamDirection]
  rw [sqrt_scale_sq (le_of_lt scalePositive)]
  have leftDenominatorPositive :
      0 < scale * Real.sqrt second + stabilizer :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg (le_of_lt scalePositive) (Real.sqrt_nonneg second))
      stabilizerPositive
  have rightDenominatorPositive :
      0 < Real.sqrt second + stabilizer / scale :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg second)
      (div_pos stabilizerPositive scalePositive)
  field_simp [
    ne_of_gt scalePositive,
    ne_of_gt leftDenominatorPositive,
    ne_of_gt rightDenominatorPositive,
  ]

/-- Bias correction preserves the moment scaling needed by the Adam
direction theorem. -/
theorem biasCorrectedMoments_scale
    (firstDecay secondDecay : ℝ) (time : ℕ)
    (first second scale : ℝ) :
    biasCorrect firstDecay time (scale * first) =
        scale * biasCorrect firstDecay time first ∧
      biasCorrect secondDecay time (scale ^ 2 * second) =
        scale ^ 2 * biasCorrect secondDecay time second := by
  constructor <;> exact biasCorrect_scale _ _ _ _

/-- Full one-step source recurrence: positively rescaling both the current
gradient and consistently scaled incoming moments leaves the zero-stabilizer
bias-corrected direction unchanged. -/
theorem oneStep_biasCorrectedDirection_scale_zeroStabilizer
    {firstDecay secondDecay previousFirst previousSecond gradient scale : ℝ}
    (scalePositive : 0 < scale)
    {time : ℕ} :
    adamDirection 0
        (biasCorrect firstDecay time
          (firstMomentStep firstDecay
            (scale * previousFirst) (scale * gradient)))
        (biasCorrect secondDecay time
          (secondMomentStep secondDecay
            (scale ^ 2 * previousSecond) (scale * gradient))) =
      adamDirection 0
        (biasCorrect firstDecay time
          (firstMomentStep firstDecay previousFirst gradient))
        (biasCorrect secondDecay time
          (secondMomentStep secondDecay previousSecond gradient)) := by
  rw [firstMomentStep_scale, secondMomentStep_scale_sq,
    biasCorrect_scale, biasCorrect_scale]
  exact adamDirection_scale_zeroStabilizer scalePositive

/-! ## Boundaries -/

/-- The practical positive stabilizer breaks exact scale invariance. -/
theorem fixed_stabilizer_breaks_scale_invariance :
    adamDirection 1 (2 * 1) (2 ^ 2 * 1) = (2 / 3 : ℝ) ∧
      adamDirection 1 1 1 = (1 / 2 : ℝ) ∧
      adamDirection 1 (2 * 1) (2 ^ 2 * 1) ≠
        adamDirection 1 1 1 := by
  norm_num [adamDirection]

/-- Positive scaling is load-bearing. Negating every gradient reverses the
zero-stabilizer direction instead of preserving it. -/
theorem negative_scaling_reverses_direction :
    adamDirection 0 ((-1) * 1) ((-1) ^ 2 * 1) = (-1 : ℝ) ∧
      adamDirection 0 1 1 = (1 : ℝ) := by
  norm_num [adamDirection]

/-- The zero-second-moment, zero-stabilizer corner is totalized to zero in
Lean; it is not evidence for a meaningful optimizer direction. -/
theorem zero_second_zero_stabilizer_is_degenerate :
    adamDirection 0 1 0 = 0 := by
  norm_num [adamDirection]

end

end AdamMomentScaling

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamMomentScaling.biasCorrectionDenominator_pos
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamMomentScaling.sqrt_scale_sq
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamMomentScaling.adamDirection_scale_zeroStabilizer
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamMomentScaling.adamDirection_scale_eq_rescaledStabilizer
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamMomentScaling.oneStep_biasCorrectedDirection_scale_zeroStabilizer
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamMomentScaling.fixed_stabilizer_breaks_scale_invariance
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AdamMomentScaling.zero_second_zero_stabilizer_is_degenerate
