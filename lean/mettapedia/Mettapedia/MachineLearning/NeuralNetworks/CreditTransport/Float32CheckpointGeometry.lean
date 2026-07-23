import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32CheckpointMatrix
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32AffineReplayCertificate
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
open Float32AffineReplayCertificate
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

/-- The replay certificate's row-wise exact affine map is extensionally the
same map as the checkpoint geometry's decoded continuous linear map plus
decoded bias. -/
theorem replayIdealAffine_eq_decodedAffine {rows columns : ℕ}
    (replay : Float32AffineReplay rows columns)
    (value : EuclideanSpace ℝ (Fin columns)) :
    replay.idealAffine value =
      affineMap (decodedLinear replay.weight) (decodedBias replay.bias) value := by
  ext row
  simp [Float32AffineReplay.idealAffine, affineMap, decodedLinear,
    decodedBias, decodedRowMajorMatrix, rowMajorMatrix,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, add_comm]

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
noncomputable def preactivationBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (centerBound radius : ℝ) : ℝ :=
  layer.weightBound * (centerBound + radius) + layer.biasBound

/-- Conservative checkpoint-facing forward and Jacobian bound for the
masked affine-SiLU transition. -/
noncomputable def transitionBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (centerBound radius : ℝ) : ℝ :=
  (1 + layer.preactivationBound centerBound radius / 4) *
    layer.weightBound

/-- Conservative checkpoint-facing Jacobian-variation bound. -/
noncomputable def transitionVariationBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (centerBound radius : ℝ) : ℝ :=
  (1 / 2 + layer.preactivationBound centerBound radius / 4) *
    layer.weightBound * layer.weightBound

theorem preactivationBound_nonneg {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius) :
    0 ≤ layer.preactivationBound centerBound radius := by
  exact add_nonneg
    (mul_nonneg layer.weightBound_nonneg
      (add_nonneg hcenterBound hradius))
    layer.biasBound_nonneg

theorem actualPreactivationBound_le {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (center : HiddenState (Fin columns))
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

theorem actualTransitionBound_le {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (center : HiddenState (Fin columns))
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

theorem actualTransitionVariationBound_le {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (center : HiddenState (Fin columns))
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
noncomputable def maskedSiLUBudget {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (mask : Fin rows → Prop) [DecidablePred mask]
    (center : HiddenState (Fin columns))
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius)
    (hcenter : ‖center‖ ≤ centerBound) :
    RegionalJacobianBudget
      (rectangularMaskedAffineSiLU mask layer.linear layer.biasVector)
      (rectangularMaskedAffineSiLUJacobian
        mask layer.linear layer.biasVector)
      (fun input => ‖input - center‖ ≤ radius)
      (layer.transitionBound centerBound radius)
      (layer.transitionBound centerBound radius)
      (layer.transitionVariationBound centerBound radius) :=
  (SiLUTransitionBounds.rectangularMaskedAffineSiLUBudget
      mask layer.linear layer.biasVector center radius hradius).weaken
    (layer.actualTransitionBound_le center centerBound radius
      hcenterBound hradius hcenter)
    (layer.actualTransitionBound_le center centerBound radius
      hcenterBound hradius hcenter)
    (layer.actualTransitionVariationBound_le center centerBound radius
      hcenterBound hradius hcenter)

end Float32AffineLayer

/-! ## Shared-node lifting

PyTorch applies every registered hidden affine layer independently at each
graph node.  The following construction represents that operation as one
block-diagonal Euclidean map.  Its bound is deliberately recomputed from the
whole finite matrix rather than inferred informally from the one-node layer.
-/

variable {Node : Type*} [Fintype Node] [DecidableEq Node]

/-- Restrict a whole graph state to the feature vector stored at one node. -/
private noncomputable def nodeSlice {width : ℕ}
    (vector : EuclideanSpace ℝ (Node × Fin width)) (node : Node) :
    EuclideanSpace ℝ (Fin width) :=
  WithLp.toLp 2 fun feature => vector (node, feature)

omit [DecidableEq Node] in
/-- The squared Euclidean norm of a graph state is the sum of the squared
norms of its node-local feature vectors. -/
private theorem norm_sq_eq_sum_nodeSlice_sq {width : ℕ}
    (vector : EuclideanSpace ℝ (Node × Fin width)) :
    ‖vector‖ ^ 2 = ∑ node, ‖nodeSlice vector node‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro node _
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Exact block-diagonal matrix obtained by sharing one decoded affine weight
over every node. -/
def sharedDecodedMatrix {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    Matrix (Node × Fin rows) (Node × Fin columns) ℝ :=
  fun output input =>
    if output.1 = input.1 then
      decodedRowMajorMatrix entries output.2 input.2
    else 0

/-- Exact continuous linear map for a feature layer shared independently over
all nodes. -/
noncomputable def decodedSharedLinear {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    EuclideanSpace ℝ (Node × Fin columns) →L[ℝ]
      EuclideanSpace ℝ (Node × Fin rows) :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Node × Fin rows)
      (n := Node × Fin columns)).trans LinearMap.toContinuousLinearMap)
    (sharedDecodedMatrix entries)

private theorem decodedSharedLinear_nodeSlice {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word)
    (vector : EuclideanSpace ℝ (Node × Fin columns)) (node : Node) :
    nodeSlice (decodedSharedLinear (Node := Node) entries vector) node =
      decodedLinear (rows := rows) (columns := columns) entries
        (nodeSlice vector node) := by
  ext row
  simp [nodeSlice, decodedSharedLinear, decodedLinear, sharedDecodedMatrix,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-- Exact bias obtained by repeating one decoded feature bias at every node. -/
noncomputable def decodedSharedBias {rows : ℕ}
    (entries : Fin rows → FiniteFloat32Word) :
    EuclideanSpace ℝ (Node × Fin rows) :=
  WithLp.toLp 2 fun output => (entries output.2).toReal

/-- Auditable whole-state bound for the shared weight map. -/
noncomputable def decodedSharedWeightL1 {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) : ℝ :=
  entrywiseL1Bound (sharedDecodedMatrix (Node := Node) entries)

/-- Auditable whole-state bound for the repeated bias. -/
noncomputable def decodedSharedBiasL1 {rows : ℕ}
    (entries : Fin rows → FiniteFloat32Word) : ℝ :=
  ∑ output : Node × Fin rows, |(entries output.2).toReal|

theorem decodedSharedWeightL1_nonneg {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    0 ≤ decodedSharedWeightL1 (Node := Node) entries :=
  entrywiseL1Bound_nonneg _

omit [DecidableEq Node] in
theorem decodedSharedBiasL1_nonneg {rows : ℕ}
    (entries : Fin rows → FiniteFloat32Word) :
    0 ≤ decodedSharedBiasL1 (Node := Node) entries :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem decodedSharedLinear_norm_le_weightL1 {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    ‖decodedSharedLinear (Node := Node) entries‖ ≤
      decodedSharedWeightL1 (Node := Node) entries := by
  change ‖sharedDecodedMatrix (Node := Node) entries‖ ≤
    entrywiseL1Bound (sharedDecodedMatrix (Node := Node) entries)
  exact l2OperatorNorm_le_entrywiseL1 _

/-- Sharing a layer independently over graph nodes does not amplify its
Euclidean operator bound.  Unlike the entrywise bound of the expanded matrix,
this certificate is independent of the number of nodes. -/
theorem decodedSharedLinear_norm_le_singleNodeWeightL1 {rows columns : ℕ}
    (entries : Fin (rows * columns) → FiniteFloat32Word) :
    ‖decodedSharedLinear (Node := Node) entries‖ ≤
      decodedWeightL1 (rows := rows) (columns := columns) entries := by
  apply ContinuousLinearMap.opNorm_le_bound _ (decodedWeightL1_nonneg entries)
  intro vector
  have hslice (node : Node) :
      ‖decodedLinear (rows := rows) (columns := columns) entries
          (nodeSlice vector node)‖ ≤
        decodedWeightL1 (rows := rows) (columns := columns) entries *
          ‖nodeSlice vector node‖ := by
    calc
      ‖decodedLinear (rows := rows) (columns := columns) entries
          (nodeSlice vector node)‖ ≤
          ‖decodedLinear (rows := rows) (columns := columns) entries‖ *
            ‖nodeSlice vector node‖ :=
        (decodedLinear entries).le_opNorm _
      _ ≤ decodedWeightL1 entries * ‖nodeSlice vector node‖ :=
        mul_le_mul_of_nonneg_right
          (decodedLinear_norm_le_weightL1 entries) (norm_nonneg _)
  have hsq :
      ‖decodedSharedLinear (Node := Node) entries vector‖ ^ 2 ≤
        (decodedWeightL1 entries * ‖vector‖) ^ 2 := by
    rw [norm_sq_eq_sum_nodeSlice_sq]
    simp_rw [decodedSharedLinear_nodeSlice]
    calc
      ∑ node, ‖decodedLinear entries (nodeSlice vector node)‖ ^ 2 ≤
          ∑ node,
            (decodedWeightL1 entries * ‖nodeSlice vector node‖) ^ 2 := by
        gcongr with node
        exact hslice node
      _ = (decodedWeightL1 entries) ^ 2 *
          ∑ node, ‖nodeSlice vector node‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      _ = (decodedWeightL1 entries) ^ 2 * ‖vector‖ ^ 2 := by
        rw [norm_sq_eq_sum_nodeSlice_sq]
      _ = (decodedWeightL1 entries * ‖vector‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (decodedWeightL1_nonneg entries) (norm_nonneg _))).1 hsq

theorem decodedSharedBias_norm_le_biasL1 {rows : ℕ}
    (entries : Fin rows → FiniteFloat32Word) :
    ‖decodedSharedBias (Node := Node) entries‖ ≤
      decodedSharedBiasL1 (Node := Node) entries :=
  euclidean_norm_le_entrywiseL1 _

namespace Float32AffineLayer

noncomputable def sharedLinear {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    HiddenState (Node × Fin columns) →L[ℝ]
      HiddenState (Node × Fin rows) :=
  decodedSharedLinear (Node := Node) layer.weight

noncomputable def sharedBiasVector {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    HiddenState (Node × Fin rows) :=
  decodedSharedBias (Node := Node) layer.bias

noncomputable def sharedWeightBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) : ℝ :=
  layer.weightBound

noncomputable def sharedBiasBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) : ℝ :=
  decodedSharedBiasL1 (Node := Node) layer.bias

theorem sharedLinear_norm_le_weightBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    ‖layer.sharedLinear (Node := Node)‖ ≤
      layer.sharedWeightBound :=
  decodedSharedLinear_norm_le_singleNodeWeightL1 layer.weight

theorem sharedBiasVector_norm_le_biasBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    ‖layer.sharedBiasVector (Node := Node)‖ ≤
      layer.sharedBiasBound (Node := Node) :=
  decodedSharedBias_norm_le_biasL1 layer.bias

theorem sharedWeightBound_nonneg {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    0 ≤ layer.sharedWeightBound :=
  layer.weightBound_nonneg

omit [DecidableEq Node] in
theorem sharedBiasBound_nonneg {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns) :
    0 ≤ layer.sharedBiasBound (Node := Node) :=
  decodedSharedBiasL1_nonneg layer.bias

/-- Whole-state checkpoint-facing preactivation bound for a layer shared over
all nodes. -/
noncomputable def sharedPreactivationBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (centerBound radius : ℝ) : ℝ :=
  layer.sharedWeightBound * (centerBound + radius) +
    layer.sharedBiasBound (Node := Node)

noncomputable def sharedTransitionBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (centerBound radius : ℝ) : ℝ :=
  (1 + layer.sharedPreactivationBound (Node := Node)
      centerBound radius / 4) *
    layer.sharedWeightBound

noncomputable def sharedTransitionVariationBound {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (centerBound radius : ℝ) : ℝ :=
  (1 / 2 + layer.sharedPreactivationBound (Node := Node)
      centerBound radius / 4) *
    layer.sharedWeightBound *
    layer.sharedWeightBound

omit [DecidableEq Node] in
theorem sharedPreactivationBound_nonneg {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius) :
    0 ≤ layer.sharedPreactivationBound (Node := Node)
      centerBound radius := by
  exact add_nonneg
    (mul_nonneg layer.sharedWeightBound_nonneg
      (add_nonneg hcenterBound hradius))
    layer.sharedBiasBound_nonneg

theorem actualSharedPreactivationBound_le {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (center : HiddenState (Node × Fin columns))
    (centerBound radius : ℝ)
    (_hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius)
    (hcenter : ‖center‖ ≤ centerBound) :
    ‖layer.sharedLinear (Node := Node)‖ * (‖center‖ + radius) +
        ‖layer.sharedBiasVector (Node := Node)‖ ≤
      layer.sharedPreactivationBound (Node := Node)
        centerBound radius := by
  have hcenterRadius :
      ‖center‖ + radius ≤ centerBound + radius :=
    add_le_add hcenter (le_refl radius)
  have hcenterRadius_nonneg : 0 ≤ ‖center‖ + radius :=
    add_nonneg (norm_nonneg _) hradius
  calc
    ‖layer.sharedLinear (Node := Node)‖ * (‖center‖ + radius) +
        ‖layer.sharedBiasVector (Node := Node)‖ ≤
      layer.sharedWeightBound * (centerBound + radius) +
        layer.sharedBiasBound (Node := Node) := by
      exact add_le_add
        (mul_le_mul layer.sharedLinear_norm_le_weightBound hcenterRadius
          hcenterRadius_nonneg layer.sharedWeightBound_nonneg)
        layer.sharedBiasVector_norm_le_biasBound
    _ = layer.sharedPreactivationBound (Node := Node)
        centerBound radius := rfl

theorem actualSharedTransitionBound_le {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (center : HiddenState (Node × Fin columns))
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius)
    (hcenter : ‖center‖ ≤ centerBound) :
    (1 + (‖layer.sharedLinear (Node := Node)‖ *
        (‖center‖ + radius) +
        ‖layer.sharedBiasVector (Node := Node)‖) / 4) *
        ‖layer.sharedLinear (Node := Node)‖ ≤
      layer.sharedTransitionBound (Node := Node)
        centerBound radius := by
  have hpre := layer.actualSharedPreactivationBound_le
    (Node := Node) center centerBound radius hcenterBound hradius hcenter
  have hfactor :
      1 + (‖layer.sharedLinear (Node := Node)‖ *
          (‖center‖ + radius) +
          ‖layer.sharedBiasVector (Node := Node)‖) / 4 ≤
        1 + layer.sharedPreactivationBound (Node := Node)
          centerBound radius / 4 := by
    linarith
  have hupperFactorNonneg :
      0 ≤ 1 + layer.sharedPreactivationBound (Node := Node)
        centerBound radius / 4 := by
    have := layer.sharedPreactivationBound_nonneg (Node := Node)
      centerBound radius hcenterBound hradius
    linarith
  exact mul_le_mul hfactor layer.sharedLinear_norm_le_weightBound
    (norm_nonneg _) hupperFactorNonneg

theorem actualSharedTransitionVariationBound_le {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (center : HiddenState (Node × Fin columns))
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius)
    (hcenter : ‖center‖ ≤ centerBound) :
    (1 / 2 + (‖layer.sharedLinear (Node := Node)‖ *
        (‖center‖ + radius) +
        ‖layer.sharedBiasVector (Node := Node)‖) / 4) *
        ‖layer.sharedLinear (Node := Node)‖ *
        ‖layer.sharedLinear (Node := Node)‖ ≤
      layer.sharedTransitionVariationBound (Node := Node)
        centerBound radius := by
  have hpre := layer.actualSharedPreactivationBound_le
    (Node := Node) center centerBound radius hcenterBound hradius hcenter
  have hfactor :
      1 / 2 + (‖layer.sharedLinear (Node := Node)‖ *
          (‖center‖ + radius) +
          ‖layer.sharedBiasVector (Node := Node)‖) / 4 ≤
        1 / 2 + layer.sharedPreactivationBound (Node := Node)
          centerBound radius / 4 := by
    linarith
  have hupperFactorNonneg :
      0 ≤ 1 / 2 + layer.sharedPreactivationBound (Node := Node)
        centerBound radius / 4 := by
    have := layer.sharedPreactivationBound_nonneg (Node := Node)
      centerBound radius hcenterBound hradius
    linarith
  have hfirst :
      (1 / 2 + (‖layer.sharedLinear (Node := Node)‖ *
          (‖center‖ + radius) +
          ‖layer.sharedBiasVector (Node := Node)‖) / 4) *
          ‖layer.sharedLinear (Node := Node)‖ ≤
        (1 / 2 + layer.sharedPreactivationBound (Node := Node)
          centerBound radius / 4) *
          layer.sharedWeightBound := by
    exact mul_le_mul hfactor layer.sharedLinear_norm_le_weightBound
      (norm_nonneg _) hupperFactorNonneg
  have hupperFirstNonneg :
      0 ≤ (1 / 2 + layer.sharedPreactivationBound (Node := Node)
          centerBound radius / 4) *
        layer.sharedWeightBound :=
    mul_nonneg hupperFactorNonneg layer.sharedWeightBound_nonneg
  exact mul_le_mul hfirst layer.sharedLinear_norm_le_weightBound
    (norm_nonneg _) hupperFirstNonneg

/-- Regional `R/J/H` certificate for the exact checkpoint layer as it is
shared over every graph node. -/
noncomputable def sharedMaskedSiLUBudget {rows columns : ℕ}
    (layer : Float32AffineLayer rows columns)
    (mask : Node × Fin rows → Prop) [DecidablePred mask]
    (center : HiddenState (Node × Fin columns))
    (centerBound radius : ℝ)
    (hcenterBound : 0 ≤ centerBound)
    (hradius : 0 ≤ radius)
    (hcenter : ‖center‖ ≤ centerBound) :
    RegionalJacobianBudget
      (rectangularMaskedAffineSiLU
        mask (layer.sharedLinear (Node := Node))
        (layer.sharedBiasVector (Node := Node)))
      (rectangularMaskedAffineSiLUJacobian
        mask (layer.sharedLinear (Node := Node))
        (layer.sharedBiasVector (Node := Node)))
      (fun input => ‖input - center‖ ≤ radius)
      (layer.sharedTransitionBound (Node := Node) centerBound radius)
      (layer.sharedTransitionBound (Node := Node) centerBound radius)
      (layer.sharedTransitionVariationBound (Node := Node)
        centerBound radius) :=
  (SiLUTransitionBounds.rectangularMaskedAffineSiLUBudget
      mask (layer.sharedLinear (Node := Node))
      (layer.sharedBiasVector (Node := Node)) center radius hradius).weaken
    (layer.actualSharedTransitionBound_le
      (Node := Node) center centerBound radius hcenterBound hradius hcenter)
    (layer.actualSharedTransitionBound_le
      (Node := Node) center centerBound radius hcenterBound hradius hcenter)
    (layer.actualSharedTransitionVariationBound_le
      (Node := Node) center centerBound radius hcenterBound hradius hcenter)

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
      (rectangularMaskedAffineSiLU allActive singletonLayer.linear
        singletonLayer.biasVector)
      (rectangularMaskedAffineSiLUJacobian allActive singletonLayer.linear
        singletonLayer.biasVector)
      (fun input : HiddenState (Fin 1) => ‖input‖ ≤ 1)
      (11 / 8) (11 / 8) (7 / 8) := by
  convert singletonLayer.maskedSiLUBudget allActive 0 0 1
    (by norm_num) (by norm_num) (by norm_num) using 1 <;>
      norm_num [Float32AffineLayer.transitionBound,
        Float32AffineLayer.transitionVariationBound,
        Float32AffineLayer.preactivationBound,
        singletonLayer_weightBound, singletonLayer_biasBound]

/-- Exact rectangular fixture with one output and two input features. -/
def twoInputLayer : Float32AffineLayer 1 2 where
  weight := fun _ => positiveOne
  bias := fun _ => negativeHalf

theorem twoInputLayer_weightBound :
    twoInputLayer.weightBound = 2 := by
  norm_num [Float32AffineLayer.weightBound, decodedWeightL1,
    entrywiseL1Bound, decodedRowMajorMatrix, rowMajorMatrix,
    rowMajorIndex, twoInputLayer, positiveOne_toReal]

theorem twoInputLayer_biasBound :
    twoInputLayer.biasBound = 1 / 2 := by
  norm_num [Float32AffineLayer.biasBound, decodedBiasL1,
    twoInputLayer, negativeHalf_toReal]

/-- The rectangular checkpoint path supplies a complete regional budget for
the registered first-hidden-layer shape, where input and output widths differ. -/
noncomputable def twoInputLayerTransitionBudget :
    RegionalJacobianBudget
      (rectangularMaskedAffineSiLU allActive twoInputLayer.linear
        twoInputLayer.biasVector)
      (rectangularMaskedAffineSiLUJacobian allActive twoInputLayer.linear
        twoInputLayer.biasVector)
      (fun input : HiddenState (Fin 2) => ‖input‖ ≤ 1)
      (13 / 4) (13 / 4) (9 / 2) := by
  convert twoInputLayer.maskedSiLUBudget allActive 0 0 1
    (by norm_num) (by norm_num) (by norm_num) using 1 <;>
      norm_num [Float32AffineLayer.transitionBound,
        Float32AffineLayer.transitionVariationBound,
        Float32AffineLayer.preactivationBound,
        twoInputLayer_weightBound, twoInputLayer_biasBound]

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

/-- Positive shared-node fixture: the decoded unit weight remains one within
one node's block. -/
theorem sharedSingleton_sameNode_weight :
    sharedDecodedMatrix (Node := Fin 2) singletonLayer.weight
      (0, 0) (0, 0) = 1 := by
  norm_num [sharedDecodedMatrix, singletonLayer, decodedRowMajorMatrix,
    rowMajorMatrix, rowMajorIndex, positiveOne_toReal]

/-- Negative coupling fixture: sharing a feature layer does not introduce an
off-diagonal edge between distinct graph nodes. -/
theorem sharedSingleton_crossNode_weight_is_zero :
    sharedDecodedMatrix (Node := Fin 2) singletonLayer.weight
      (0, 0) (1, 0) = 0 := by
  norm_num [sharedDecodedMatrix]

/-- The sharp shared-layer certificate is independent of the number of graph
nodes: two copies of the decoded unit layer still have operator norm at most
one. -/
theorem sharedSingleton_operatorNorm_le_one :
    ‖singletonLayer.sharedLinear (Node := Fin 2)‖ ≤ 1 := by
  simpa [Float32AffineLayer.sharedWeightBound,
    singletonLayer_weightBound] using
    (singletonLayer.sharedLinear_norm_le_weightBound (Node := Fin 2))

/-- A single-block bound cannot be reused after introducing cross-node
coupling.  The all-ones two-node matrix has norm greater than one, so the
block-diagonal premise of the sharp shared-layer theorem is essential. -/
def crossNodeCoupledMatrix :
    Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℝ :=
  fun _ _ => 1

theorem crossNodeCoupling_breaks_singleBlockBound :
    ¬ ‖(Matrix.toEuclideanCLM (n := Fin 2 × Fin 1) (𝕜 := ℝ)
      crossNodeCoupledMatrix)‖ ≤ 1 := by
  intro h
  let vector : EuclideanSpace ℝ (Fin 2 × Fin 1) :=
    WithLp.toLp 2 fun _ => (1 : ℝ)
  have happly :=
    (Matrix.toEuclideanCLM (n := Fin 2 × Fin 1) (𝕜 := ℝ)
      crossNodeCoupledMatrix).le_opNorm vector
  have hbound :
      ‖(Matrix.toEuclideanCLM (n := Fin 2 × Fin 1) (𝕜 := ℝ)
          crossNodeCoupledMatrix) vector‖ ≤ ‖vector‖ := by
    calc
      _ ≤ ‖(Matrix.toEuclideanCLM (n := Fin 2 × Fin 1) (𝕜 := ℝ)
          crossNodeCoupledMatrix)‖ * ‖vector‖ := happly
      _ ≤ 1 * ‖vector‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg vector)
      _ = ‖vector‖ := one_mul _
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hbound
  norm_num [vector, crossNodeCoupledMatrix, Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    EuclideanSpace.real_norm_sq_eq] at hsquare

#print axioms decodedLinear_norm_le_weightL1
#print axioms decodedBias_norm_le_biasL1
#print axioms replayIdealAffine_eq_decodedAffine
#print axioms Float32AffineLayer.linear_norm_le_weightBound
#print axioms Float32AffineLayer.maskedSiLUBudget
#print axioms decodedSharedLinear_norm_le_weightL1
#print axioms decodedSharedLinear_norm_le_singleNodeWeightL1
#print axioms decodedSharedBias_norm_le_biasL1
#print axioms Float32AffineLayer.sharedMaskedSiLUBudget
#print axioms sharedSingleton_sameNode_weight
#print axioms sharedSingleton_crossNode_weight_is_zero
#print axioms sharedSingleton_operatorNorm_le_one
#print axioms crossNodeCoupling_breaks_singleBlockBound
#print axioms singletonLayer_map_zero
#print axioms singletonLayerTransitionBudget
#print axioms twoInputLayerTransitionBudget
#print axioms singletonLayer_bias_prevents_zero_preactivation
#print axioms decodedAllOnes_maxEntry_fails

end

end Float32CheckpointGeometry

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
