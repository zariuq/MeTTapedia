import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ImportanceSampledCoordinateDescent

/-!
# Weighted strong convexity and coordinate-descent contraction

Bubeck, *Convex Optimization: Algorithms and Complexity*,
arXiv:1405.4980, Lemma 6.9 and Theorem 6.8, derives the
gradient-dominance premise used by importance-sampled coordinate descent from
strong convexity in the sampling-induced weighted norm.

This module formalizes that missing analytic link.  For arbitrary positive
sampling weights `pᵢ` and directional smoothnesses `βᵢ`, the relevant primal
weight is `βᵢ / pᵢ`; its dual squared norm is exactly

`∑ᵢ (pᵢ / βᵢ) gᵢ²`.

Weighted Young's inequality turns the first-order strong-convexity model into
the required gradient-dominance inequality.  The existing finite weighted
expectation theorem then yields the geometric rate without assuming gradient
dominance separately.

No neural settling energy is declared strongly convex here.  A concrete
application must prove the first-order inequality and every coordinate
decrease on its actual state space.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace WeightedStrongConvexity

open ImportanceSampledCoordinateDescent

universe u

variable {Coordinate : Type u} [Fintype Coordinate]

/-- Squared coordinate norm with positive diagonal weights. -/
noncomputable def weightedNormSq
    (weight vector : Coordinate → ℝ) : ℝ :=
  ∑ coordinate, weight coordinate * vector coordinate ^ 2

/-- Squared dual coordinate norm for a positive diagonal primal weight. -/
noncomputable def weightedDualNormSq
    (weight vector : Coordinate → ℝ) : ℝ :=
  ∑ coordinate, vector coordinate ^ 2 / weight coordinate

/-- Finite coordinate dot product. -/
noncomputable def weightedDot
    (left right : Coordinate → ℝ) : ℝ :=
  ∑ coordinate, left coordinate * right coordinate

/-- First-order strong-convexity inequality in a declared weighted coordinate
geometry.

The definition deliberately exposes the supplied gradient.  It does not infer
differentiability or convexity from an implementation label. -/
def IsWeightedStronglyConvexAtGradient
    (weight : Coordinate → ℝ)
    (objective : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (modulus : ℝ) : Prop :=
  ∀ x y,
    objective x - objective y ≤
      weightedDot (gradient x)
          (fun coordinate => x coordinate - y coordinate) -
        modulus / 2 *
          weightedNormSq weight
            (fun coordinate => x coordinate - y coordinate)

omit [Fintype Coordinate] in
/-- Scalar weighted Young inequality.  Positivity of both the coordinate
weight and the modulus is essential. -/
theorem weightedYoungTerm
    (weight gradient displacement modulus : ℝ)
    (positiveWeight : 0 < weight)
    (positiveModulus : 0 < modulus) :
    gradient * displacement -
        modulus / 2 * (weight * displacement ^ 2) ≤
      (gradient ^ 2 / weight) / (2 * modulus) := by
  rw [div_div]
  have denominatorPositive : 0 < weight * (2 * modulus) :=
    mul_pos positiveWeight (mul_pos (by norm_num) positiveModulus)
  apply (le_div_iff₀ denominatorPositive).2
  nlinarith [
    sq_nonneg (gradient - modulus * weight * displacement)]

/-- Finite-dimensional weighted Young inequality. -/
theorem weightedYoung
    (weight gradient displacement : Coordinate → ℝ)
    (modulus : ℝ)
    (positiveWeight : ∀ coordinate, 0 < weight coordinate)
    (positiveModulus : 0 < modulus) :
    weightedDot gradient displacement -
        modulus / 2 * weightedNormSq weight displacement ≤
      weightedDualNormSq weight gradient / (2 * modulus) := by
  unfold weightedDot weightedNormSq weightedDualNormSq
  calc
    (∑ coordinate, gradient coordinate * displacement coordinate) -
        modulus / 2 *
          (∑ coordinate,
            weight coordinate * displacement coordinate ^ 2) =
      ∑ coordinate,
        (gradient coordinate * displacement coordinate -
          modulus / 2 *
            (weight coordinate * displacement coordinate ^ 2)) := by
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ ∑ coordinate,
        (gradient coordinate ^ 2 / weight coordinate) /
          (2 * modulus) :=
      Finset.sum_le_sum fun coordinate _ =>
        weightedYoungTerm
          (weight coordinate) (gradient coordinate)
          (displacement coordinate) modulus
          (positiveWeight coordinate) positiveModulus
    _ = (∑ coordinate,
          gradient coordinate ^ 2 / weight coordinate) /
            (2 * modulus) := by
      exact (Finset.sum_div _ _ _).symm

/-- Weighted version of Bubeck's Lemma 6.9: the first-order
strong-convexity inequality bounds an objective gap by the squared dual
gradient norm. -/
theorem objectiveGap_le_weightedDualGradient
    (weight : Coordinate → ℝ)
    (objective : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (reference state : Coordinate → ℝ)
    (modulus : ℝ)
    (positiveWeight : ∀ coordinate, 0 < weight coordinate)
    (positiveModulus : 0 < modulus)
    (strong :
      IsWeightedStronglyConvexAtGradient
        weight objective gradient modulus) :
    objective state - objective reference ≤
      weightedDualNormSq weight (gradient state) /
        (2 * modulus) :=
  (strong state reference).trans
    (weightedYoung weight (gradient state)
      (fun coordinate => state coordinate - reference coordinate)
      modulus positiveWeight positiveModulus)

/-- Multiplicative form of weighted gradient dominance. -/
theorem weightedStrongConvexity_gradientDominance
    (weight : Coordinate → ℝ)
    (objective : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (reference state : Coordinate → ℝ)
    (modulus : ℝ)
    (positiveWeight : ∀ coordinate, 0 < weight coordinate)
    (positiveModulus : 0 < modulus)
    (strong :
      IsWeightedStronglyConvexAtGradient
        weight objective gradient modulus) :
    2 * modulus * (objective state - objective reference) ≤
      weightedDualNormSq weight (gradient state) := by
  have gapBound :=
    objectiveGap_le_weightedDualGradient
      weight objective gradient reference state modulus
      positiveWeight positiveModulus strong
  have scaled :=
    (le_div_iff₀ (mul_pos (by norm_num) positiveModulus)).mp gapBound
  nlinarith

/-- The dual norm induced by primal weight `βᵢ / pᵢ` is exactly the
weighted-gradient quantity used by the general coordinate sampler. -/
theorem weightedGradientSq_eq_dualRatio
    (samplingWeight smoothness gradient : Coordinate → ℝ)
    (positiveSamplingWeight :
      ∀ coordinate, 0 < samplingWeight coordinate)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate) :
    weightedGradientSq samplingWeight smoothness gradient =
      weightedDualNormSq
        (fun coordinate =>
          smoothness coordinate / samplingWeight coordinate)
        gradient := by
  unfold weightedGradientSq weightedDualNormSq
  apply Finset.sum_congr rfl
  intro coordinate _
  field_simp [
    ne_of_gt (positiveSamplingWeight coordinate),
    ne_of_gt (positiveSmoothness coordinate)]

section Nonempty

variable [Nonempty Coordinate]

/-- Bubeck's one-step weighted coordinate contraction with gradient dominance
derived from the source's weighted strong-convexity premise. -/
theorem weightedStronglyConvex_hasContraction
    (samplingWeight smoothness : Coordinate → ℝ)
    (objective : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (step : Coordinate → (Coordinate → ℝ) → Coordinate → ℝ)
    (reference : Coordinate → ℝ)
    (modulus : ℝ)
    (positiveSamplingWeight :
      ∀ coordinate, 0 < samplingWeight coordinate)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate)
    (positiveModulus : 0 < modulus)
    (strong :
      IsWeightedStronglyConvexAtGradient
        (fun coordinate =>
          smoothness coordinate / samplingWeight coordinate)
        objective gradient modulus)
    (coordinateDecrease :
      ∀ state coordinate,
        objective (step coordinate state) - objective reference ≤
          objective state - objective reference -
            gradient state coordinate ^ 2 /
              (2 * smoothness coordinate)) :
    HasWeightedOneStepContraction
      samplingWeight step
      (fun state => objective state - objective reference)
      (1 - modulus / totalWeight samplingWeight) := by
  apply weightedCoordinate_has_contraction
    samplingWeight smoothness gradient step
    (fun state => objective state - objective reference) modulus
    positiveSamplingWeight positiveSmoothness coordinateDecrease
  intro state
  rw [weightedGradientSq_eq_dualRatio
    samplingWeight smoothness (gradient state)
    positiveSamplingWeight positiveSmoothness]
  exact weightedStrongConvexity_gradientDominance
    (fun coordinate =>
      smoothness coordinate / samplingWeight coordinate)
    objective gradient reference state modulus
    (fun coordinate =>
      div_pos (positiveSmoothness coordinate)
        (positiveSamplingWeight coordinate))
    positiveModulus strong

/-- Complete geometric expected-gap theorem with weighted strong convexity
supplying the gradient-dominance premise. -/
theorem weightedStronglyConvex_meanGap_le
    (samplingWeight smoothness : Coordinate → ℝ)
    (objective : (Coordinate → ℝ) → ℝ)
    (gradient : (Coordinate → ℝ) → Coordinate → ℝ)
    (step : Coordinate → (Coordinate → ℝ) → Coordinate → ℝ)
    (reference : Coordinate → ℝ)
    (modulus : ℝ)
    (positiveSamplingWeight :
      ∀ coordinate, 0 < samplingWeight coordinate)
    (positiveSmoothness :
      ∀ coordinate, 0 < smoothness coordinate)
    (positiveModulus : 0 < modulus)
    (modulus_le_total :
      modulus ≤ totalWeight samplingWeight)
    (strong :
      IsWeightedStronglyConvexAtGradient
        (fun coordinate =>
          smoothness coordinate / samplingWeight coordinate)
        objective gradient modulus)
    (coordinateDecrease :
      ∀ state coordinate,
        objective (step coordinate state) - objective reference ≤
          objective state - objective reference -
            gradient state coordinate ^ 2 /
              (2 * smoothness coordinate))
    (rounds : ℕ) (state : Coordinate → ℝ) :
    weightedMeanGapAfter samplingWeight step
        (fun point => objective point - objective reference)
        rounds state ≤
      (1 - modulus / totalWeight samplingWeight) ^ rounds *
        (objective state - objective reference) := by
  apply weightedCoordinate_meanGap_le
    samplingWeight smoothness gradient step
    (fun point => objective point - objective reference) modulus
    positiveSamplingWeight positiveSmoothness modulus_le_total
    coordinateDecrease
  intro point
  rw [weightedGradientSq_eq_dualRatio
    samplingWeight smoothness (gradient point)
    positiveSamplingWeight positiveSmoothness]
  exact weightedStrongConvexity_gradientDominance
    (fun coordinate =>
      smoothness coordinate / samplingWeight coordinate)
    objective gradient reference point modulus
    (fun coordinate =>
      div_pos (positiveSmoothness coordinate)
        (positiveSamplingWeight coordinate))
    positiveModulus strong

end Nonempty

/-! ## Exact anisotropic fixture -/

def unitBoolWeight (_coordinate : Bool) : ℝ := 1

def zeroBoolState (_coordinate : Bool) : ℝ := 0

/-- The anisotropic quadratic from the coordinate-descent module is
one-strongly convex in the ordinary coordinate geometry. -/
theorem anisotropic_weightedStrongConvexity :
    IsWeightedStronglyConvexAtGradient
      unitBoolWeight anisotropicGap anisotropicGradient 1 := by
  intro x y
  simp [weightedDot, weightedNormSq, anisotropicGap,
    anisotropicGradient, anisotropicSmoothness, unitBoolWeight]
  nlinarith [sq_nonneg (x true - y true)]

/-- Importance sampling by the anisotropic smoothness induces unit primal
weights, so the weighted strong-convexity fixture applies exactly. -/
theorem anisotropic_ratioStrongConvexity :
    IsWeightedStronglyConvexAtGradient
      (fun coordinate =>
        anisotropicSmoothness coordinate /
          anisotropicSmoothness coordinate)
      anisotropicGap anisotropicGradient 1 := by
  have weightsEqual :
      (fun coordinate =>
        anisotropicSmoothness coordinate /
          anisotropicSmoothness coordinate) =
        unitBoolWeight := by
    funext coordinate
    cases coordinate <;>
      norm_num [anisotropicSmoothness, unitBoolWeight]
  rw [weightsEqual]
  exact anisotropic_weightedStrongConvexity

/-- The three-quarters rate is now obtained from weighted strong convexity,
not from a separately assumed gradient-dominance theorem. -/
theorem anisotropic_meanGap_le_fromStrongConvexity
    (rounds : ℕ) (state : Bool → ℝ) :
    weightedMeanGapAfter anisotropicSmoothness
        zeroSelectedCoordinate
        (fun point =>
          anisotropicGap point - anisotropicGap zeroBoolState)
        rounds state ≤
      (3 / 4 : ℝ) ^ rounds *
        (anisotropicGap state - anisotropicGap zeroBoolState) := by
  have theoremInstance :=
    weightedStronglyConvex_meanGap_le
      anisotropicSmoothness anisotropicSmoothness
      anisotropicGap anisotropicGradient zeroSelectedCoordinate
      zeroBoolState 1
      (by
        intro coordinate
        cases coordinate <;>
          norm_num [anisotropicSmoothness])
      (by
        intro coordinate
        cases coordinate <;>
          norm_num [anisotropicSmoothness])
      (by norm_num)
      (by
        rw [anisotropic_totalWeight]
        norm_num)
      anisotropic_ratioStrongConvexity
      (by
        intro point coordinate
        rw [anisotropic_coordinateDecrease_exact]
        norm_num [anisotropicGap, zeroBoolState])
      rounds state
  rw [anisotropic_totalWeight] at theoremInstance
  norm_num at theoremInstance ⊢
  exact theoremInstance

/-! ## Negative boundary -/

def unitCoordinateWeight (_coordinate : Unit) : ℝ := 1

noncomputable def constantZeroObjective
    (_state : Unit → ℝ) : ℝ := 0

noncomputable def zeroGradient
    (_state : Unit → ℝ) (_coordinate : Unit) : ℝ := 0

/-- A constant objective cannot be assigned a positive strong-convexity
modulus merely because its coordinate weight is positive. -/
theorem constantObjective_not_oneStrong :
    ¬ IsWeightedStronglyConvexAtGradient
      unitCoordinateWeight constantZeroObjective zeroGradient 1 := by
  intro model
  have contradiction := model (fun _ => 1) (fun _ => 0)
  norm_num [weightedDot, weightedNormSq, unitCoordinateWeight,
    constantZeroObjective, zeroGradient] at contradiction

#print axioms weightedYoungTerm
#print axioms weightedYoung
#print axioms objectiveGap_le_weightedDualGradient
#print axioms weightedStrongConvexity_gradientDominance
#print axioms weightedGradientSq_eq_dualRatio
#print axioms weightedStronglyConvex_hasContraction
#print axioms weightedStronglyConvex_meanGap_le
#print axioms anisotropic_weightedStrongConvexity
#print axioms anisotropic_meanGap_le_fromStrongConvexity
#print axioms constantObjective_not_oneStrong

end WeightedStrongConvexity

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
