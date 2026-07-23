import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointMatrix
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SiLUTransitionBounds
import Mathlib.Tactic

/-!
# Checkpoint-bound affine and SiLU geometry

The checkpoint decoder already turns every finite binary32 word into an exact
real matrix.  This file turns that matrix into the exact Euclidean continuous
linear map used by the adapter calculus, retains the source-visible bias, and
derives conservative regional SiLU constants from finite entrywise sums.

The entrywise sums are deliberately conservative.  Their role is to make the
numeric certificate reducible to exact finite arithmetic, not to approximate
a spectral computation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32CheckpointGeometry

noncomputable section

open scoped Matrix.Norms.L2Operator
open CompositionalJacobianBounds
open FiniteMatrixOperatorBounds
open Float32CheckpointMatrix
open SiLUTransitionBounds

/-- Exact continuous linear map represented by a row-major binary32 weight
tensor with PyTorch shape `[output, input]`. -/
noncomputable def decodedLinear {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    EuclideanSpace ℝ (Fin columns) →L[ℝ] EuclideanSpace ℝ (Fin rows) :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin rows) (n := Fin columns)).trans
    LinearMap.toContinuousLinearMap) (decodedRowMajorMatrix entries)

/-- Exact Euclidean bias vector decoded from binary32 words. -/
noncomputable def decodedBias {rows : ℕ}
    (entries : Fin rows → FiniteFloat32Word) :
    EuclideanSpace ℝ (Fin rows) :=
  WithLp.toLp 2 fun row => (entries row).toReal

/-- Auditable upper bound for the decoded weight operator norm. -/
noncomputable def decodedWeightL1 {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) : ℝ :=
  entrywiseL1Bound (decodedRowMajorMatrix entries)

/-- Auditable upper bound for the decoded bias norm. -/
noncomputable def decodedBiasL1 {rows : ℕ}
    (entries : Fin rows → FiniteFloat32Word) : ℝ :=
  ∑ row, |(entries row).toReal|

theorem decodedWeightL1_nonneg {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    0 ≤ decodedWeightL1 entries :=
  entrywiseL1Bound_nonneg _

theorem decodedBiasL1_nonneg {rows : ℕ}
    (entries : Fin rows → FiniteFloat32Word) :
    0 ≤ decodedBiasL1 entries :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The exact continuous linear map inherits the matrix's finite entrywise
operator-norm certificate. -/
theorem decodedLinear_norm_le_weightL1 {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    ‖decodedLinear entries‖ ≤ decodedWeightL1 entries := by
  change ‖decodedRowMajorMatrix entries‖ ≤
    entrywiseL1Bound (decodedRowMajorMatrix entries)
  exact decodedRowMajorMatrix_operatorNorm_le_entrywiseL1 entries

/-- The Euclidean bias norm is likewise bounded by its finite entrywise
one-norm. -/
theorem decodedBias_norm_le_biasL1 {rows : ℕ}
    (entries : Fin rows → FiniteFloat32Word) :
    ‖decodedBias entries‖ ≤ decodedBiasL1 entries := by
  exact euclidean_norm_le_entrywiseL1 (decodedBias entries)

/-- A complete affine checkpoint layer: exact word-level weight and bias
payloads with source row-major semantics. -/
structure Float32AffineLayer (rows columns : ℕ) where
  weight : Fin (rows * columns) → FiniteFloat32Word
  bias : Fin rows → FiniteFloat32Word

namespace Float32AffineLayer

noncomputable def linear {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    EuclideanSpace ℝ (Fin columns) →L[ℝ] EuclideanSpace ℝ (Fin rows) :=
  decodedLinear layer.weight

noncomputable def biasVector {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    EuclideanSpace ℝ (Fin rows) :=
  decodedBias layer.bias

noncomputable def weightBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) : ℝ :=
  decodedWeightL1 layer.weight

noncomputable def biasBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) : ℝ :=
  decodedBiasL1 layer.bias

noncomputable def map {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    EuclideanSpace ℝ (Fin columns) → EuclideanSpace ℝ (Fin rows) :=
  affineMap layer.linear layer.biasVector

theorem linear_norm_le_weightBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    ‖layer.linear‖ ≤ layer.weightBound :=
  decodedLinear_norm_le_weightL1 layer.weight

theorem biasVector_norm_le_biasBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    ‖layer.biasVector‖ ≤ layer.biasBound :=
  decodedBias_norm_le_biasL1 layer.bias

theorem weightBound_nonneg {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    0 ≤ layer.weightBound :=
  decodedWeightL1_nonneg layer.weight

theorem biasBound_nonneg {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    0 ≤ layer.biasBound :=
  decodedBiasL1_nonneg layer.bias

/-- Conservative bound for every preactivation reached from a centered input
ball. -/
noncomputable def preactivationBound {dimension : ℕ}
    (layer : Float32AffineLayer dimension dimension)
    (centerBound radius : ℝ) : ℝ :=
  layer.weightBound * (centerBound + radius) + layer.biasBound

/-- Conservative checkpoint-facing forward and Jacobian bound for the
masked affine-SiLU transition. -/
noncomputable def transitionBound {dimension : ℕ}
    (layer : Float32AffineLayer dimension dimension)
    (centerBound radius : ℝ) : ℝ :=
  (1 + layer.preactivationBound centerBound radius / 4) *
    layer.weightBound

/-- Conservative checkpoint-facing Jacobian-variation bound. -/
noncomputable def transitionVariationBound {dimension : ℕ}
    (layer : Float32AffineLayer dimension dimension)
    (centerBound radius : ℝ) : ℝ :=
  (1 / 2 + layer.preactivationBound centerBound radius / 4) *
    layer.weightBound * layer.weightBound

theorem preactivationBound_nonneg {dimension : ℕ}
    (layer : Float32AffineLayer dimension dimension)
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius) :
    0 ≤ layer.preactivationBound centerBound radius := by
  exact add_nonneg
    (mul_nonneg layer.weightBound_nonneg
      (add_nonneg hcenterBound hradius))
    layer.biasBound_nonneg

theorem actualPreactivationBound_le {dimension : ℕ}
    (layer : Float32AffineLayer dimension dimension)
    (center : HiddenState (Fin dimension))
    (centerBound radius : ℝ)
    (_hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius)
    (hcenter : ‖center‖ ≤ centerBound) :
    ‖layer.linear‖ * (‖center‖ + radius) + ‖layer.biasVector‖ ≤
      layer.preactivationBound centerBound radius := by
  have hcenterRadius :
      ‖center‖ + radius ≤ centerBound + radius :=
    add_le_add hcenter (le_refl radius)
  have hcenterRadius_nonneg : 0 ≤ ‖center‖ + radius :=
    add_nonneg (norm_nonneg _) hradius
  calc
    ‖layer.linear‖ * (‖center‖ + radius) + ‖layer.biasVector‖ ≤
        layer.weightBound * (centerBound + radius) + layer.biasBound := by
      exact add_le_add
        (mul_le_mul layer.linear_norm_le_weightBound hcenterRadius
          hcenterRadius_nonneg layer.weightBound_nonneg)
        layer.biasVector_norm_le_biasBound
    _ = layer.preactivationBound centerBound radius := rfl

theorem actualTransitionBound_le {dimension : ℕ}
    (layer : Float32AffineLayer dimension dimension)
    (center : HiddenState (Fin dimension))
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius)
    (hcenter : ‖center‖ ≤ centerBound) :
    (1 + (‖layer.linear‖ * (‖center‖ + radius) +
          ‖layer.biasVector‖) / 4) * ‖layer.linear‖ ≤
      layer.transitionBound centerBound radius := by
  have hpre := layer.actualPreactivationBound_le center centerBound radius
    hcenterBound hradius hcenter
  have hfactor :
      1 + (‖layer.linear‖ * (‖center‖ + radius) +
          ‖layer.biasVector‖) / 4 ≤
        1 + layer.preactivationBound centerBound radius / 4 := by
    linarith
  have hupperFactorNonneg :
      0 ≤ 1 + layer.preactivationBound centerBound radius / 4 := by
    have := layer.preactivationBound_nonneg centerBound radius
      hcenterBound hradius
    linarith
  exact mul_le_mul hfactor layer.linear_norm_le_weightBound
    (norm_nonneg _) hupperFactorNonneg

theorem actualTransitionVariationBound_le {dimension : ℕ}
    (layer : Float32AffineLayer dimension dimension)
    (center : HiddenState (Fin dimension))
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius)
    (hcenter : ‖center‖ ≤ centerBound) :
    (1 / 2 + (‖layer.linear‖ * (‖center‖ + radius) +
          ‖layer.biasVector‖) / 4) *
        ‖layer.linear‖ * ‖layer.linear‖ ≤
      layer.transitionVariationBound centerBound radius := by
  have hpre := layer.actualPreactivationBound_le center centerBound radius
    hcenterBound hradius hcenter
  have hfactor :
      1 / 2 + (‖layer.linear‖ * (‖center‖ + radius) +
          ‖layer.biasVector‖) / 4 ≤
        1 / 2 + layer.preactivationBound centerBound radius / 4 := by
    linarith
  have hupperFactorNonneg :
      0 ≤ 1 / 2 + layer.preactivationBound centerBound radius / 4 := by
    have := layer.preactivationBound_nonneg centerBound radius
      hcenterBound hradius
    linarith
  have hfirst :
      (1 / 2 + (‖layer.linear‖ * (‖center‖ + radius) +
          ‖layer.biasVector‖) / 4) * ‖layer.linear‖ ≤
        (1 / 2 + layer.preactivationBound centerBound radius / 4) *
          layer.weightBound := by
    exact mul_le_mul hfactor layer.linear_norm_le_weightBound
      (norm_nonneg _) hupperFactorNonneg
  have hupperFirstNonneg :
      0 ≤ (1 / 2 + layer.preactivationBound centerBound radius / 4) *
        layer.weightBound :=
    mul_nonneg hupperFactorNonneg layer.weightBound_nonneg
  exact mul_le_mul hfirst layer.linear_norm_le_weightBound
    (norm_nonneg _) hupperFirstNonneg

/-- Exact source transition with conservative constants computed only from
decoded checkpoint words, a certified center-norm bound, and a declared input
radius. -/
noncomputable def maskedSiLUBudget {dimension : ℕ}
    (layer : Float32AffineLayer dimension dimension)
    (mask : Fin dimension → Prop) [DecidablePred mask]
    (center : HiddenState (Fin dimension))
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius)
    (hcenter : ‖center‖ ≤ centerBound) :
    RegionalJacobianBudget
      (maskedAffineSiLU mask layer.linear layer.biasVector)
      (maskedAffineSiLUJacobian mask layer.linear layer.biasVector)
      (fun input => ‖input - center‖ ≤ radius)
      (layer.transitionBound centerBound radius)
      (layer.transitionBound centerBound radius)
      (layer.transitionVariationBound centerBound radius) :=
  (SiLUTransitionBounds.maskedAffineSiLUBudget
      mask layer.linear layer.biasVector center radius hradius).weaken
    (layer.actualTransitionBound_le center centerBound radius
      hcenterBound hradius hcenter)
    (layer.actualTransitionBound_le center centerBound radius
      hcenterBound hradius hcenter)
    (layer.actualTransitionVariationBound_le center centerBound radius
      hcenterBound hradius hcenter)

end Float32AffineLayer

/-! ## Exact fixtures -/

def singletonLayer : Float32AffineLayer 1 1 where
  weight := fun _ => positiveOne
  bias := fun _ => negativeHalf

theorem singletonLayer_weightBound :
    singletonLayer.weightBound = 1 := by
  norm_num [Float32AffineLayer.weightBound, decodedWeightL1,
    entrywiseL1Bound, decodedRowMajorMatrix, rowMajorMatrix,
    rowMajorIndex, singletonLayer, positiveOne_toReal]

theorem singletonLayer_biasBound :
    singletonLayer.biasBound = 1 / 2 := by
  norm_num [Float32AffineLayer.biasBound, decodedBiasL1,
    singletonLayer, negativeHalf_toReal]

theorem singletonLayer_map_zero :
    singletonLayer.map 0 =
      WithLp.toLp 2 (fun _ : Fin 1 => -(1 / 2 : ℝ)) := by
  ext row
  fin_cases row
  norm_num [Float32AffineLayer.map, affineMap,
    Float32AffineLayer.linear, decodedLinear,
    Float32AffineLayer.biasVector, decodedBias,
    decodedRowMajorMatrix, rowMajorMatrix, rowMajorIndex, singletonLayer,
    negativeHalf_toReal, Matrix.toLpLin_apply]

def allActive (_ : Fin 1) : Prop := True

instance allActiveDecidable : DecidablePred allActive :=
  fun _ => isTrue trivial

/-- The complete regional budget for the exact singleton checkpoint layer is
computed from its word-level weight and bias bounds. -/
noncomputable def singletonLayerTransitionBudget :
    RegionalJacobianBudget
      (maskedAffineSiLU allActive singletonLayer.linear
        singletonLayer.biasVector)
      (maskedAffineSiLUJacobian allActive singletonLayer.linear
        singletonLayer.biasVector)
      (fun input : HiddenState (Fin 1) => ‖input‖ ≤ 1)
      (11 / 8) (11 / 8) (7 / 8) := by
  convert singletonLayer.maskedSiLUBudget allActive 0 0 1
    (by norm_num) (by norm_num) (by norm_num) using 1 <;>
      norm_num [Float32AffineLayer.transitionBound,
        Float32AffineLayer.transitionVariationBound,
        Float32AffineLayer.preactivationBound,
        singletonLayer_weightBound, singletonLayer_biasBound]

/-- The singleton's decoded bias makes its zero-input preactivation nonzero,
so a zero-bias regional calculation would not describe this checkpoint. -/
theorem singletonLayer_bias_prevents_zero_preactivation :
    singletonLayer.map 0 ≠ 0 := by
  rw [singletonLayer_map_zero]
  intro hzero
  have hcoordinate := congrFun (congrArg WithLp.ofLp hzero) (0 : Fin 1)
  norm_num at hcoordinate

/-- The max-entry shortcut remains unsound after checkpoint decoding: the
all-ones `2 × 2` word matrix has operator norm greater than one. -/
theorem decodedAllOnes_maxEntry_fails :
    ¬ ‖decodedLinear (rows := 2) (columns := 2)
        (fun _ => positiveOne)‖ ≤ 1 := by
  intro h
  let vector : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 fun _ : Fin 2 => (1 : ℝ)
  have happly :=
    (decodedLinear (rows := 2) (columns := 2)
      (fun _ => positiveOne)).le_opNorm vector
  have hbound :
      ‖decodedLinear (rows := 2) (columns := 2)
          (fun _ => positiveOne) vector‖ ≤ ‖vector‖ := by
    calc
      ‖decodedLinear (rows := 2) (columns := 2)
          (fun _ => positiveOne) vector‖ ≤
          ‖decodedLinear (rows := 2) (columns := 2)
            (fun _ => positiveOne)‖ * ‖vector‖ := happly
      _ ≤ 1 * ‖vector‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg vector)
      _ = ‖vector‖ := one_mul _
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hbound
  norm_num [vector, decodedLinear, decodedRowMajorMatrix, rowMajorMatrix,
    rowMajorIndex, positiveOne_toReal, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, EuclideanSpace.real_norm_sq_eq] at hsquare

#print axioms decodedLinear_norm_le_weightL1
#print axioms decodedBias_norm_le_biasL1
#print axioms Float32AffineLayer.linear_norm_le_weightBound
#print axioms Float32AffineLayer.maskedSiLUBudget
#print axioms singletonLayer_map_zero
#print axioms singletonLayerTransitionBudget
#print axioms singletonLayer_bias_prevents_zero_preactivation
#print axioms decodedAllOnes_maxEntry_fails

end

end Float32CheckpointGeometry

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
