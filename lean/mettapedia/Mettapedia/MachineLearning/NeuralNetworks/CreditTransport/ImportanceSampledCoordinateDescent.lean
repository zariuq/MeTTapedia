import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.UniformBlockExpectedDescent

/-!
# Importance-sampled coordinate descent

Bubeck, *Convex Optimization: Algorithms and Complexity*,
arXiv:1405.4980, Theorem 6.8, samples coordinate `i` in proportion to its
directional smoothness `βᵢ` and obtains a geometric expected convergence rate
under strong convexity.  This module extracts the finite algebraic spine of
the `γ = 1` case.

Rather than assuming differentiability inside the theorem, a concrete solver
supplies two executable obligations:

* its selected-coordinate step decreases the gap by at least
  `gradientᵢ² / (2 βᵢ)`;
* its squared coordinate gradients dominate `2 α` times the gap.

The first obligation is the source's one-dimensional smoothness inequality.
The second is the gradient-dominance consequence of strong convexity.  Their
composition gives contraction factor `1 - α / ∑ βᵢ`, followed by an exact
finite weighted-expectation induction.

This form is reusable for sparse predictive-coding settling: the theorem does
not infer smoothness, strong convexity, or a useful active set merely from
coordinate sparsity.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ImportanceSampledCoordinateDescent

universe u v

variable {Coordinate : Type u} {State : Type v}
  [Fintype Coordinate] [Nonempty Coordinate]

/-- Total unnormalized mass of a finite sampling distribution. -/
noncomputable def totalWeight (weight : Coordinate → ℝ) : ℝ :=
  ∑ coordinate, weight coordinate

/-- Exact expectation under the distribution obtained by normalizing
positive finite weights. -/
noncomputable def weightedAverage
    (weight value : Coordinate → ℝ) : ℝ :=
  (∑ coordinate, weight coordinate * value coordinate) /
    totalWeight weight

theorem totalWeight_pos
    (weight : Coordinate → ℝ)
    (positive : ∀ coordinate, 0 < weight coordinate) :
    0 < totalWeight weight := by
  unfold totalWeight
  exact Finset.sum_pos
    (fun coordinate _ => positive coordinate)
    Finset.univ_nonempty

omit [Nonempty Coordinate] in
theorem weightedAverage_mono
    (weight : Coordinate → ℝ)
    (nonnegative : ∀ coordinate, 0 ≤ weight coordinate)
    (positiveTotal : 0 < totalWeight weight)
    {left right : Coordinate → ℝ}
    (pointwise : ∀ coordinate, left coordinate ≤ right coordinate) :
    weightedAverage weight left ≤ weightedAverage weight right := by
  unfold weightedAverage
  apply div_le_div_of_nonneg_right _ positiveTotal.le
  exact Finset.sum_le_sum fun coordinate _ =>
    mul_le_mul_of_nonneg_left
      (pointwise coordinate) (nonnegative coordinate)

omit [Nonempty Coordinate] in
theorem weightedAverage_const_mul
    (weight : Coordinate → ℝ) (scale : ℝ)
    (value : Coordinate → ℝ) :
    weightedAverage weight (fun coordinate =>
        scale * value coordinate) =
      scale * weightedAverage weight value := by
  unfold weightedAverage
  calc
    (∑ coordinate,
        weight coordinate * (scale * value coordinate)) /
          totalWeight weight =
        (scale * ∑ coordinate,
          weight coordinate * value coordinate) /
            totalWeight weight := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro coordinate _
      ring
    _ = scale *
        ((∑ coordinate, weight coordinate * value coordinate) /
          totalWeight weight) := by
      ring

/-- Exact weighted mean after independent draws from the same finite
distribution. -/
noncomputable def weightedMeanGapAfter
    (weight : Coordinate → ℝ)
    (step : Coordinate → State → State)
    (gap : State → ℝ) :
    ℕ → State → ℝ
  | 0, state => gap state
  | rounds + 1, state =>
      weightedAverage weight (fun coordinate =>
        weightedMeanGapAfter weight step gap rounds
          (step coordinate state))

/-- Statewise contraction under one exact weighted coordinate draw. -/
def HasWeightedOneStepContraction
    (weight : Coordinate → ℝ)
    (step : Coordinate → State → State)
    (gap : State → ℝ) (rate : ℝ) : Prop :=
  ∀ state,
    weightedAverage weight (fun coordinate =>
      gap (step coordinate state)) ≤
        rate * gap state

omit [Nonempty Coordinate] in
/-- A statewise weighted contraction yields geometric convergence of the
recursively averaged gap. -/
theorem weightedMeanGapAfter_le_geometric
    (weight : Coordinate → ℝ)
    (step : Coordinate → State → State)
    (gap : State → ℝ) (rate : ℝ)
    (nonnegativeWeight : ∀ coordinate, 0 ≤ weight coordinate)
    (positiveTotal : 0 < totalWeight weight)
    (nonnegativeRate : 0 ≤ rate)
    (contract :
      HasWeightedOneStepContraction weight step gap rate)
    (rounds : ℕ) (state : State) :
    weightedMeanGapAfter weight step gap rounds state ≤
      rate ^ rounds * gap state := by
  induction rounds generalizing state with
  | zero =>
      simp [weightedMeanGapAfter]
  | succ rounds inductionHypothesis =>
      calc
        weightedMeanGapAfter weight step gap (rounds + 1) state =
            weightedAverage weight (fun coordinate =>
              weightedMeanGapAfter weight step gap rounds
                (step coordinate state)) := by
          rfl
        _ ≤ weightedAverage weight (fun coordinate =>
              rate ^ rounds * gap (step coordinate state)) :=
          weightedAverage_mono weight nonnegativeWeight positiveTotal
            (fun coordinate =>
              inductionHypothesis (step coordinate state))
        _ = rate ^ rounds *
              weightedAverage weight (fun coordinate =>
                gap (step coordinate state)) :=
          weightedAverage_const_mul weight _ _
        _ ≤ rate ^ rounds * (rate * gap state) :=
          mul_le_mul_of_nonneg_left (contract state)
            (pow_nonneg nonnegativeRate rounds)
        _ = rate ^ (rounds + 1) * gap state := by
          rw [pow_succ]
          ring

/-- Importance sampling by `βᵢ` cancels the denominator in the
coordinate-smoothness benefit exactly. -/
theorem weightedAverage_coordinateBenefit
    (smoothness gradient : Coordinate → ℝ)
    (gap : ℝ)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate) :
    weightedAverage smoothness (fun coordinate =>
        gap -
          gradient coordinate ^ 2 /
            (2 * smoothness coordinate)) =
      gap -
        (∑ coordinate, gradient coordinate ^ 2) /
          (2 * totalWeight smoothness) := by
  have nonzeroSmoothness :
      ∀ coordinate, smoothness coordinate ≠ 0 :=
    fun coordinate => ne_of_gt (positiveSmoothness coordinate)
  have positiveTotal :=
    totalWeight_pos smoothness positiveSmoothness
  have numeratorIdentity :
      (∑ coordinate,
        smoothness coordinate *
          (gap -
            gradient coordinate ^ 2 /
              (2 * smoothness coordinate))) =
        totalWeight smoothness * gap -
          (∑ coordinate, gradient coordinate ^ 2) / 2 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    congr 1
    calc
      (∑ coordinate,
          smoothness coordinate *
            (gradient coordinate ^ 2 /
              (2 * smoothness coordinate))) =
          ∑ coordinate, gradient coordinate ^ 2 / 2 := by
        apply Finset.sum_congr rfl
        intro coordinate _
        field_simp [nonzeroSmoothness coordinate]
      _ = (∑ coordinate, gradient coordinate ^ 2) / 2 := by
        rw [Finset.sum_div]
  unfold weightedAverage
  rw [numeratorIdentity]
  field_simp [ne_of_gt positiveTotal]

/-- Squared-gradient quantity induced jointly by the sampling weights and
the coordinate smoothnesses.  Choosing sampling weight `βᵢ^γ` gives the
source dual weight `βᵢ^(γ-1)`. -/
noncomputable def weightedGradientSq
    (samplingWeight smoothness gradient : Coordinate → ℝ) : ℝ :=
  ∑ coordinate,
    samplingWeight coordinate / smoothness coordinate *
      gradient coordinate ^ 2

/-- General finite importance-sampling identity.  The `γ = 1` cancellation
above is the specialization `samplingWeight = smoothness`. -/
theorem weightedAverage_coordinateBenefit_general
    (samplingWeight smoothness gradient : Coordinate → ℝ)
    (gap : ℝ)
    (positiveSamplingWeight :
      ∀ coordinate, 0 < samplingWeight coordinate)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate) :
    weightedAverage samplingWeight (fun coordinate =>
        gap -
          gradient coordinate ^ 2 /
            (2 * smoothness coordinate)) =
      gap -
        weightedGradientSq samplingWeight smoothness gradient /
          (2 * totalWeight samplingWeight) := by
  have nonzeroSmoothness :
      ∀ coordinate, smoothness coordinate ≠ 0 :=
    fun coordinate => ne_of_gt (positiveSmoothness coordinate)
  have positiveTotal :=
    totalWeight_pos samplingWeight positiveSamplingWeight
  have numeratorIdentity :
      (∑ coordinate,
        samplingWeight coordinate *
          (gap -
            gradient coordinate ^ 2 /
              (2 * smoothness coordinate))) =
        totalWeight samplingWeight * gap -
          weightedGradientSq samplingWeight smoothness gradient / 2 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    congr 1
    unfold weightedGradientSq
    calc
      (∑ coordinate,
          samplingWeight coordinate *
            (gradient coordinate ^ 2 /
              (2 * smoothness coordinate))) =
          ∑ coordinate,
            (samplingWeight coordinate /
                smoothness coordinate *
              gradient coordinate ^ 2) / 2 := by
        apply Finset.sum_congr rfl
        intro coordinate _
        field_simp [nonzeroSmoothness coordinate]
      _ = (∑ coordinate,
          samplingWeight coordinate /
              smoothness coordinate *
            gradient coordinate ^ 2) / 2 := by
        rw [Finset.sum_div]
  unfold weightedAverage
  rw [numeratorIdentity]
  field_simp [ne_of_gt positiveTotal]

omit [Nonempty Coordinate] in
/-- With sampling weights proportional to the smoothnesses, the weighted
dual-gradient quantity is the ordinary sum of coordinate squares. -/
theorem weightedGradientSq_self
    (smoothness gradient : Coordinate → ℝ)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate) :
    weightedGradientSq smoothness smoothness gradient =
      ∑ coordinate, gradient coordinate ^ 2 := by
  unfold weightedGradientSq
  apply Finset.sum_congr rfl
  intro coordinate _
  field_simp [ne_of_gt (positiveSmoothness coordinate)]

/-- General weighted-coordinate contraction.  This contains the finite
algebra of every positive sampling law; a source-level `γ` choice is obtained
by binding `samplingWeightᵢ = βᵢ^γ` and discharging the corresponding weighted
gradient-dominance premise. -/
theorem weightedCoordinate_has_contraction
    (samplingWeight smoothness : Coordinate → ℝ)
    (gradient : State → Coordinate → ℝ)
    (step : Coordinate → State → State)
    (gap : State → ℝ)
    (modulus : ℝ)
    (positiveSamplingWeight :
      ∀ coordinate, 0 < samplingWeight coordinate)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate)
    (coordinateDecrease :
      ∀ state coordinate,
        gap (step coordinate state) ≤
          gap state -
            gradient state coordinate ^ 2 /
              (2 * smoothness coordinate))
    (weightedGradientDominance :
      ∀ state,
        2 * modulus * gap state ≤
          weightedGradientSq samplingWeight smoothness
            (gradient state)) :
    HasWeightedOneStepContraction samplingWeight step gap
      (1 - modulus / totalWeight samplingWeight) := by
  intro state
  have positiveTotal :=
    totalWeight_pos samplingWeight positiveSamplingWeight
  have nonnegativeSamplingWeight :
      ∀ coordinate, 0 ≤ samplingWeight coordinate :=
    fun coordinate => (positiveSamplingWeight coordinate).le
  have normalizedDominance :
      modulus / totalWeight samplingWeight * gap state ≤
        weightedGradientSq samplingWeight smoothness
            (gradient state) /
          (2 * totalWeight samplingWeight) := by
    calc
      modulus / totalWeight samplingWeight * gap state =
          (2 * modulus * gap state) /
            (2 * totalWeight samplingWeight) := by
        field_simp [ne_of_gt positiveTotal]
      _ ≤ weightedGradientSq samplingWeight smoothness
              (gradient state) /
            (2 * totalWeight samplingWeight) :=
        div_le_div_of_nonneg_right
          (weightedGradientDominance state)
          (mul_nonneg (by norm_num) positiveTotal.le)
  calc
    weightedAverage samplingWeight (fun coordinate =>
        gap (step coordinate state)) ≤
      weightedAverage samplingWeight (fun coordinate =>
        gap state -
          gradient state coordinate ^ 2 /
            (2 * smoothness coordinate)) :=
      weightedAverage_mono samplingWeight
        nonnegativeSamplingWeight positiveTotal
        (coordinateDecrease state)
    _ = gap state -
        weightedGradientSq samplingWeight smoothness
            (gradient state) /
          (2 * totalWeight samplingWeight) :=
      weightedAverage_coordinateBenefit_general
        samplingWeight smoothness (gradient state) (gap state)
        positiveSamplingWeight positiveSmoothness
    _ ≤ gap state -
        modulus / totalWeight samplingWeight * gap state :=
      sub_le_sub_left normalizedDominance _
    _ = (1 - modulus / totalWeight samplingWeight) * gap state := by
      ring

/-- Complete geometric rate for a declared positive finite sampling law. -/
theorem weightedCoordinate_meanGap_le
    (samplingWeight smoothness : Coordinate → ℝ)
    (gradient : State → Coordinate → ℝ)
    (step : Coordinate → State → State)
    (gap : State → ℝ)
    (modulus : ℝ)
    (positiveSamplingWeight :
      ∀ coordinate, 0 < samplingWeight coordinate)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate)
    (modulus_le_total :
      modulus ≤ totalWeight samplingWeight)
    (coordinateDecrease :
      ∀ state coordinate,
        gap (step coordinate state) ≤
          gap state -
            gradient state coordinate ^ 2 /
              (2 * smoothness coordinate))
    (weightedGradientDominance :
      ∀ state,
        2 * modulus * gap state ≤
          weightedGradientSq samplingWeight smoothness
            (gradient state))
    (rounds : ℕ) (state : State) :
    weightedMeanGapAfter samplingWeight step gap rounds state ≤
      (1 - modulus / totalWeight samplingWeight) ^ rounds *
        gap state := by
  have positiveTotal :=
    totalWeight_pos samplingWeight positiveSamplingWeight
  have nonnegativeRate :
      0 ≤ 1 - modulus / totalWeight samplingWeight := by
    apply sub_nonneg.mpr
    exact (div_le_one positiveTotal).2 modulus_le_total
  exact weightedMeanGapAfter_le_geometric
    samplingWeight step gap
    (1 - modulus / totalWeight samplingWeight)
    (fun coordinate => (positiveSamplingWeight coordinate).le)
    positiveTotal nonnegativeRate
    (weightedCoordinate_has_contraction
      samplingWeight smoothness gradient step gap modulus
      positiveSamplingWeight positiveSmoothness coordinateDecrease
      weightedGradientDominance)
    rounds state

/-- Source Theorem 6.8 at `γ = 1`, in assumption-explicit finite form.
Coordinate smoothness supplies `coordinateDecrease`; strong convexity
supplies `gradientDominance`. -/
theorem importanceSampled_has_contraction
    (smoothness : Coordinate → ℝ)
    (gradient : State → Coordinate → ℝ)
    (step : Coordinate → State → State)
    (gap : State → ℝ)
    (modulus : ℝ)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate)
    (coordinateDecrease :
      ∀ state coordinate,
        gap (step coordinate state) ≤
          gap state -
            gradient state coordinate ^ 2 /
              (2 * smoothness coordinate))
    (gradientDominance :
      ∀ state,
        2 * modulus * gap state ≤
          ∑ coordinate, gradient state coordinate ^ 2) :
    HasWeightedOneStepContraction smoothness step gap
      (1 - modulus / totalWeight smoothness) := by
  apply weightedCoordinate_has_contraction
    smoothness smoothness gradient step gap modulus
    positiveSmoothness positiveSmoothness coordinateDecrease
  intro state
  rw [weightedGradientSq_self
    smoothness (gradient state) positiveSmoothness]
  exact gradientDominance state

/-- Complete geometric theorem corresponding to the source's linear-rate
claim. -/
theorem importanceSampled_meanGap_le
    (smoothness : Coordinate → ℝ)
    (gradient : State → Coordinate → ℝ)
    (step : Coordinate → State → State)
    (gap : State → ℝ)
    (modulus : ℝ)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate)
    (modulus_le_total : modulus ≤ totalWeight smoothness)
    (coordinateDecrease :
      ∀ state coordinate,
        gap (step coordinate state) ≤
          gap state -
            gradient state coordinate ^ 2 /
              (2 * smoothness coordinate))
    (gradientDominance :
      ∀ state,
        2 * modulus * gap state ≤
          ∑ coordinate, gradient state coordinate ^ 2)
    (rounds : ℕ) (state : State) :
    weightedMeanGapAfter smoothness step gap rounds state ≤
      (1 - modulus / totalWeight smoothness) ^ rounds *
        gap state := by
  have positiveTotal :=
    totalWeight_pos smoothness positiveSmoothness
  have nonnegativeRate :
      0 ≤ 1 - modulus / totalWeight smoothness := by
    apply sub_nonneg.mpr
    exact (div_le_one positiveTotal).2 modulus_le_total
  exact weightedMeanGapAfter_le_geometric
    smoothness step gap
    (1 - modulus / totalWeight smoothness)
    (fun coordinate => (positiveSmoothness coordinate).le)
    positiveTotal nonnegativeRate
    (importanceSampled_has_contraction
      smoothness gradient step gap modulus
      positiveSmoothness coordinateDecrease gradientDominance)
    rounds state

/-! ## Exact anisotropic two-coordinate fixture -/

def anisotropicSmoothness : Bool → ℝ
  | false => 1
  | true => 3

def zeroSelectedCoordinate
    (coordinate : Bool) (state : Bool → ℝ) : Bool → ℝ :=
  Function.update state coordinate 0

noncomputable def anisotropicGap (state : Bool → ℝ) : ℝ :=
  (state false ^ 2 + 3 * state true ^ 2) / 2

noncomputable def anisotropicGradient
    (state : Bool → ℝ) (coordinate : Bool) : ℝ :=
  anisotropicSmoothness coordinate * state coordinate

theorem anisotropic_totalWeight :
    totalWeight anisotropicSmoothness = 4 := by
  norm_num [totalWeight, anisotropicSmoothness]

theorem anisotropic_coordinateDecrease_exact
    (state : Bool → ℝ) (coordinate : Bool) :
    anisotropicGap (zeroSelectedCoordinate coordinate state) =
      anisotropicGap state -
        anisotropicGradient state coordinate ^ 2 /
          (2 * anisotropicSmoothness coordinate) := by
  cases coordinate <;>
    simp [anisotropicGap, anisotropicGradient, anisotropicSmoothness,
      zeroSelectedCoordinate, Function.update] <;>
    ring

theorem anisotropic_gradientDominance (state : Bool → ℝ) :
    2 * (1 : ℝ) * anisotropicGap state ≤
      ∑ coordinate : Bool, anisotropicGradient state coordinate ^ 2 := by
  simp [anisotropicGap, anisotropicGradient, anisotropicSmoothness]
  nlinarith [sq_nonneg (state true)]

theorem anisotropic_meanGap_le
    (rounds : ℕ) (state : Bool → ℝ) :
    weightedMeanGapAfter anisotropicSmoothness
        zeroSelectedCoordinate anisotropicGap rounds state ≤
      (3 / 4 : ℝ) ^ rounds * anisotropicGap state := by
  have theoremInstance :=
    importanceSampled_meanGap_le
      anisotropicSmoothness anisotropicGradient
      zeroSelectedCoordinate anisotropicGap 1
      (by intro coordinate; cases coordinate <;>
        norm_num [anisotropicSmoothness])
      (by rw [anisotropic_totalWeight]; norm_num)
      (fun state coordinate =>
        (anisotropic_coordinateDecrease_exact state coordinate).le)
      anisotropic_gradientDominance rounds state
  rw [anisotropic_totalWeight] at theoremInstance
  norm_num at theoremInstance ⊢
  exact theoremInstance

/-! ## Negative boundary -/

def stalledStep (_coordinate : Bool) (state : ℝ) : ℝ :=
  state

noncomputable def unitGap (_state : ℝ) : ℝ :=
  1

/-- Positive sampling weights and a coordinate-labelled step do not imply
contraction when the gradient-dominance obligation is absent. -/
theorem stalledStep_has_no_halfContraction :
    ¬ HasWeightedOneStepContraction
      anisotropicSmoothness stalledStep unitGap (1 / 2 : ℝ) := by
  intro contract
  have contradiction := contract 0
  norm_num
    [weightedAverage, totalWeight, anisotropicSmoothness,
      stalledStep, unitGap] at contradiction

#print axioms weightedAverage_coordinateBenefit
#print axioms weightedAverage_coordinateBenefit_general
#print axioms weightedGradientSq_self
#print axioms weightedCoordinate_has_contraction
#print axioms weightedCoordinate_meanGap_le
#print axioms importanceSampled_has_contraction
#print axioms importanceSampled_meanGap_le
#print axioms anisotropic_coordinateDecrease_exact
#print axioms anisotropic_gradientDominance
#print axioms anisotropic_meanGap_le
#print axioms stalledStep_has_no_halfContraction

end ImportanceSampledCoordinateDescent

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
