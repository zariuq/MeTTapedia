import Mettapedia.MachineLearning.NeuralNetworks.LayeredNeuralFunctionalTransposeSymmetry

/-!
# Orientation-aware repair of isolated-square transpose symmetry

The source neural-functional attention layer adds its row and column heads
with identical coefficients.  On an isolated square matrix, transpose
therefore exchanges two indistinguishable summands.

This module introduces the smallest algebraic repair: independent row- and
column-head coefficients.  The exact transpose law swaps those coefficients.
The source layer is recovered at coefficients `(1, 1)`; asymmetric
coefficients can distinguish orientation.  No claim of universal minimal
equivariance is made here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

open Architecture

noncomputable section

universe u uChannel

/-- Neural-functional attention on one square matrix with independently
weighted row and column heads.  The global point head is unchanged. -/
def singleSquareHeadWeightedAttention
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel} [Fintype Channel]
    (rowCoefficient columnCoefficient : ℝ)
    (queries keys values :
      LayeredWeightFeatures [layer, layer] Channel) :
    LayeredWeightFeatures [layer, layer] Channel
  | Sum.inl (row, column), channel =>
      rowCoefficient *
          rowSliceAttention
            (firstWeightMatrix queries)
            (emptyPreviousWeight
              (Middle := layer.carrier) (Channel := Channel) :
                layer.carrier → PEmpty.{u + 1} → Channel → ℝ)
            (firstWeightMatrix keys)
            (emptyPreviousWeight
              (Middle := layer.carrier) (Channel := Channel) :
                layer.carrier → PEmpty.{u + 1} → Channel → ℝ)
            (firstWeightMatrix values) row (column, channel) +
        columnCoefficient *
          columnSliceAttention
            (firstWeightMatrix queries)
            (firstWeightMatrix keys)
            (emptyNextWeight
              (Current := layer.carrier) (Channel := Channel) :
                PEmpty.{u + 1} → layer.carrier → Channel → ℝ)
            (firstWeightMatrix values)
            (emptyNextWeight
              (Current := layer.carrier) (Channel := Channel) :
                PEmpty.{u + 1} → layer.carrier → Channel → ℝ)
            column (row, channel) +
        pointWeightAttention queries keys values
          (Sum.inl (row, column)) channel
  | Sum.inr empty, _ => nomatch empty

/-- Equal unit coefficients recover the executable source attention layer
exactly on a one-matrix network. -/
theorem singleSquareHeadWeightedAttention_one_one
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel} [Fintype Channel]
    (queries keys values :
      LayeredWeightFeatures [layer, layer] Channel) :
    singleSquareHeadWeightedAttention layer 1 1
        queries keys values =
      layeredNeuralFunctionalAttention [layer, layer]
        queries keys values := by
  funext coordinate channel
  rcases coordinate with pair | empty
  · rcases pair with ⟨row, column⟩
    unfold singleSquareHeadWeightedAttention
      layeredNeuralFunctionalAttention
      layeredNeuralFunctionalAttentionFrom
      neuralFunctionalAttentionEntry
    simp
  · exact nomatch empty

/-- Exact repair law: transposing the matrix exchanges the row and column
coefficients.  Hence transpose is an internal symmetry only at the symmetric
coefficient boundary, or on inputs whose two head values coincide. -/
theorem singleSquareHeadWeightedAttention_transpose
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel} [Fintype Channel]
    (rowCoefficient columnCoefficient : ℝ)
    (queries keys values :
      LayeredWeightFeatures [layer, layer] Channel)
    (coordinate : LayeredWeightCoordinate [layer, layer])
    (channel : Channel) :
    singleSquareHeadWeightedAttention layer
        rowCoefficient columnCoefficient
        (transportRows (singleSquareTransposeEquiv layer) queries)
        (transportRows (singleSquareTransposeEquiv layer) keys)
        (transportRows (singleSquareTransposeEquiv layer) values)
        (singleSquareTransposeEquiv layer coordinate) channel =
      singleSquareHeadWeightedAttention layer
        columnCoefficient rowCoefficient
        queries keys values coordinate channel := by
  rcases coordinate with pair | empty
  · rcases pair with ⟨row, column⟩
    unfold singleSquareHeadWeightedAttention
    change
      rowCoefficient *
          rowSliceAttention
            (transposeSquareMatrix (firstWeightMatrix queries))
            (emptyPreviousWeight
              (Middle := layer.carrier) (Channel := Channel) :
                layer.carrier → PEmpty.{u + 1} → Channel → ℝ)
            (transposeSquareMatrix (firstWeightMatrix keys))
            (emptyPreviousWeight
              (Middle := layer.carrier) (Channel := Channel) :
                layer.carrier → PEmpty.{u + 1} → Channel → ℝ)
            (transposeSquareMatrix (firstWeightMatrix values))
            column (row, channel) +
        columnCoefficient *
          columnSliceAttention
            (transposeSquareMatrix (firstWeightMatrix queries))
            (transposeSquareMatrix (firstWeightMatrix keys))
            (emptyNextWeight
              (Current := layer.carrier) (Channel := Channel) :
                PEmpty.{u + 1} → layer.carrier → Channel → ℝ)
            (transposeSquareMatrix (firstWeightMatrix values))
            (emptyNextWeight
              (Current := layer.carrier) (Channel := Channel) :
                PEmpty.{u + 1} → layer.carrier → Channel → ℝ)
            row (column, channel) +
        pointWeightAttention
          (transportRows (singleSquareTransposeEquiv layer) queries)
          (transportRows (singleSquareTransposeEquiv layer) keys)
          (transportRows (singleSquareTransposeEquiv layer) values)
          (singleSquareTransposeEquiv layer (Sum.inl (row, column)))
          channel =
      columnCoefficient *
          rowSliceAttention
            (firstWeightMatrix queries)
            (emptyPreviousWeight
              (Middle := layer.carrier) (Channel := Channel) :
                layer.carrier → PEmpty.{u + 1} → Channel → ℝ)
            (firstWeightMatrix keys)
            (emptyPreviousWeight
              (Middle := layer.carrier) (Channel := Channel) :
                layer.carrier → PEmpty.{u + 1} → Channel → ℝ)
            (firstWeightMatrix values) row (column, channel) +
        rowCoefficient *
          columnSliceAttention
            (firstWeightMatrix queries)
            (firstWeightMatrix keys)
            (emptyNextWeight
              (Current := layer.carrier) (Channel := Channel) :
                PEmpty.{u + 1} → layer.carrier → Channel → ℝ)
            (firstWeightMatrix values)
            (emptyNextWeight
              (Current := layer.carrier) (Channel := Channel) :
                PEmpty.{u + 1} → layer.carrier → Channel → ℝ)
            column (row, channel) +
        pointWeightAttention queries keys values
          (Sum.inl (row, column)) channel
    rw [rowSliceAttention_transpose_single]
    rw [columnSliceAttention_transpose_single]
    rw [pointWeightAttention_transport]
    ring
  · exact nomatch empty

/-- `LayerEnc → pointwise QKV → orientation-aware attention` on one square
matrix.  This is a minimal repair candidate for the isolated-square
transpose boundary, not a replacement for the arbitrary-depth source
construction. -/
def singleSquareOrientationAwareTransformer
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel} [Fintype Channel]
    (rowCoefficient columnCoefficient : ℝ)
    (encoding : ℕ → Channel → ℝ)
    (queryProjection keyProjection valueProjection :
      (Channel → ℝ) → Channel → ℝ)
    (features : LayeredWeightFeatures [layer, layer] Channel) :
    LayeredWeightFeatures [layer, layer] Channel :=
  let encoded :=
    layeredWeightLayerEncoding [layer, layer] encoding features
  singleSquareHeadWeightedAttention layer
    rowCoefficient columnCoefficient
    (layeredPointwiseChannelMap queryProjection encoded)
    (layeredPointwiseChannelMap keyProjection encoded)
    (layeredPointwiseChannelMap valueProjection encoded)

/-- Unit row and column coefficients recover the executable source
transformer exactly. -/
theorem singleSquareOrientationAwareTransformer_one_one
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel} [Fintype Channel]
    (encoding : ℕ → Channel → ℝ)
    (queryProjection keyProjection valueProjection :
      (Channel → ℝ) → Channel → ℝ)
    (features : LayeredWeightFeatures [layer, layer] Channel) :
    singleSquareOrientationAwareTransformer layer 1 1 encoding
        queryProjection keyProjection valueProjection features =
      layeredNeuralFunctionalTransformer [layer, layer] encoding
        queryProjection keyProjection valueProjection features := by
  unfold singleSquareOrientationAwareTransformer
    layeredNeuralFunctionalTransformer
  exact singleSquareHeadWeightedAttention_one_one layer _ _ _

/-- The full repaired candidate transports transpose by exchanging its two
orientation coefficients. -/
theorem singleSquareOrientationAwareTransformer_transpose
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel} [Fintype Channel]
    (rowCoefficient columnCoefficient : ℝ)
    (encoding : ℕ → Channel → ℝ)
    (queryProjection keyProjection valueProjection :
      (Channel → ℝ) → Channel → ℝ)
    (features : LayeredWeightFeatures [layer, layer] Channel)
    (coordinate : LayeredWeightCoordinate [layer, layer])
    (channel : Channel) :
    singleSquareOrientationAwareTransformer layer
        rowCoefficient columnCoefficient encoding
        queryProjection keyProjection valueProjection
        (transportRows (singleSquareTransposeEquiv layer) features)
        (singleSquareTransposeEquiv layer coordinate) channel =
      singleSquareOrientationAwareTransformer layer
        columnCoefficient rowCoefficient encoding
        queryProjection keyProjection valueProjection
        features coordinate channel := by
  unfold singleSquareOrientationAwareTransformer
  rw [layeredWeightLayerEncoding_singleSquareTranspose]
  rw [layeredPointwiseChannelMap_transport]
  rw [layeredPointwiseChannelMap_transport]
  rw [layeredPointwiseChannelMap_transport]
  exact singleSquareHeadWeightedAttention_transpose
    layer rowCoefficient columnCoefficient _ _ _ coordinate channel

namespace LayeredNeuralFunctionalOrientationRepairFixtures

open LayeredWeightSpaceFixtures
open LayeredNeuralFunctionalTransformerFixtures

/-- Exact symbolic value of the orientation-aware transformer on the
first-row witness.  This exposes the two head coefficients independently. -/
theorem firstRowFeatures_orientation_value
    (rowCoefficient columnCoefficient : ℝ) :
    singleSquareOrientationAwareTransformer (finLayer 2)
        rowCoefficient columnCoefficient
        zeroLayerEncoding zeroProjection zeroProjection identityProjection
        firstRowFeatures grid00 0 =
      rowCoefficient / 2 + columnCoefficient + 1 / 2 := by
  norm_num
    [singleSquareOrientationAwareTransformer,
      singleSquareHeadWeightedAttention, layeredWeightLayerEncoding,
      addLayerVectorEncoding, layeredPointwiseChannelMap,
      rowSliceAttention, columnSliceAttention, pointWeightAttention,
      scaledDotProductAttention, softmaxAttention, attentionWeight,
      attentionMass, scaledAttentionDotScore, attentionDotScore,
      rowFeatureSlice, columnFeatureSlice, rowNeighborhoodSlices,
      columnNeighborhoodSlices, firstWeightMatrix, firstRowFeatures,
      squareShape, grid00, zeroLayerEncoding, zeroProjection,
      identityProjection]
  rw [show Fintype.card (finLayer 2).carrier = 2 by rfl]
  rw [show
    Fintype.card (LayeredWeightCoordinate squareShape) = 4 by rfl]
  rw [← Finset.mul_sum]
  change
    (rowCoefficient * (2 : ℝ)⁻¹ + columnCoefficient +
      (4 : ℝ)⁻¹ *
        ∑ coordinate, firstRowFeatures coordinate 0) =
      rowCoefficient / 2 + columnCoefficient + 1 / 2
  rw [firstRowFeatures_sum]
  ring

/-- With only the row head enabled, a first-row indicator returns one at the
upper-left coordinate: one half from the row head and one half from the
unchanged global head. -/
theorem firstRowFeatures_row_only_value :
    singleSquareOrientationAwareTransformer (finLayer 2) 1 0
        zeroLayerEncoding zeroProjection zeroProjection identityProjection
        firstRowFeatures grid00 0 =
      1 := by
  norm_num
    [singleSquareOrientationAwareTransformer,
      singleSquareHeadWeightedAttention, layeredWeightLayerEncoding,
      addLayerVectorEncoding, layeredPointwiseChannelMap,
      rowSliceAttention, columnSliceAttention, pointWeightAttention,
      scaledDotProductAttention, softmaxAttention, attentionWeight,
      attentionMass, scaledAttentionDotScore, attentionDotScore,
      rowFeatureSlice, columnFeatureSlice, rowNeighborhoodSlices,
      columnNeighborhoodSlices, firstWeightMatrix, firstRowFeatures,
      squareShape, grid00, zeroLayerEncoding, zeroProjection,
      identityProjection]
  rw [show Fintype.card (finLayer 2).carrier = 2 by rfl]
  rw [show
    Fintype.card (LayeredWeightCoordinate squareShape) = 4 by rfl]
  rw [← Finset.mul_sum]
  change
    ((2 : ℝ)⁻¹ +
      (4 : ℝ)⁻¹ *
        ∑ coordinate, firstRowFeatures coordinate 0) = 1
  rw [firstRowFeatures_sum]
  norm_num

/-- Swapping the row and column coefficients changes the same exact input:
the column-only head contributes one and the global head contributes one
half. -/
theorem firstRowFeatures_column_only_value :
    singleSquareOrientationAwareTransformer (finLayer 2) 0 1
        zeroLayerEncoding zeroProjection zeroProjection identityProjection
        firstRowFeatures grid00 0 =
      3 / 2 := by
  norm_num
    [singleSquareOrientationAwareTransformer,
      singleSquareHeadWeightedAttention, layeredWeightLayerEncoding,
      addLayerVectorEncoding, layeredPointwiseChannelMap,
      rowSliceAttention, columnSliceAttention, pointWeightAttention,
      scaledDotProductAttention, softmaxAttention, attentionWeight,
      attentionMass, scaledAttentionDotScore, attentionDotScore,
      rowFeatureSlice, columnFeatureSlice, rowNeighborhoodSlices,
      columnNeighborhoodSlices, firstWeightMatrix, firstRowFeatures,
      squareShape, grid00, zeroLayerEncoding, zeroProjection,
      identityProjection]
  rw [show
    Fintype.card (LayeredWeightCoordinate squareShape) = 4 by rfl]
  rw [← Finset.mul_sum]
  change
    (1 +
      (4 : ℝ)⁻¹ *
        ∑ coordinate, firstRowFeatures coordinate 0) = 3 / 2
  rw [firstRowFeatures_sum]
  norm_num

/-- On the exact first-row witness, transpose invariance holds precisely at
the symmetric coefficient boundary. -/
theorem firstRowFeatures_transpose_eq_iff_coefficients_equal
    (rowCoefficient columnCoefficient : ℝ) :
    singleSquareOrientationAwareTransformer (finLayer 2)
        rowCoefficient columnCoefficient
        zeroLayerEncoding zeroProjection zeroProjection identityProjection
        (transportRows (singleSquareTransposeEquiv (finLayer 2))
          firstRowFeatures)
        (singleSquareTransposeEquiv (finLayer 2) grid00) 0 =
      singleSquareOrientationAwareTransformer (finLayer 2)
        rowCoefficient columnCoefficient
        zeroLayerEncoding zeroProjection zeroProjection identityProjection
        firstRowFeatures grid00 0 ↔
      rowCoefficient = columnCoefficient := by
  rw [singleSquareOrientationAwareTransformer_transpose]
  rw [firstRowFeatures_orientation_value,
    firstRowFeatures_orientation_value]
  constructor
  · intro equality
    linarith
  · rintro rfl
    rfl

/-- Asymmetric head coefficients strictly break the extra transpose
symmetry on an exact `2 × 2` witness. -/
theorem row_only_is_not_transpose_equivariant :
    singleSquareOrientationAwareTransformer (finLayer 2) 1 0
        zeroLayerEncoding zeroProjection zeroProjection identityProjection
        (transportRows (singleSquareTransposeEquiv (finLayer 2))
          firstRowFeatures)
        (singleSquareTransposeEquiv (finLayer 2) grid00) 0 ≠
      singleSquareOrientationAwareTransformer (finLayer 2) 1 0
        zeroLayerEncoding zeroProjection zeroProjection identityProjection
        firstRowFeatures grid00 0 := by
  rw [singleSquareOrientationAwareTransformer_transpose]
  rw [firstRowFeatures_column_only_value, firstRowFeatures_row_only_value]
  norm_num

end LayeredNeuralFunctionalOrientationRepairFixtures

#print axioms singleSquareHeadWeightedAttention_one_one
#print axioms singleSquareHeadWeightedAttention_transpose
#print axioms singleSquareOrientationAwareTransformer_one_one
#print axioms singleSquareOrientationAwareTransformer_transpose
#print axioms
  LayeredNeuralFunctionalOrientationRepairFixtures.firstRowFeatures_orientation_value
#print axioms
  LayeredNeuralFunctionalOrientationRepairFixtures.firstRowFeatures_row_only_value
#print axioms
  LayeredNeuralFunctionalOrientationRepairFixtures.firstRowFeatures_column_only_value
#print axioms
  LayeredNeuralFunctionalOrientationRepairFixtures.firstRowFeatures_transpose_eq_iff_coefficients_equal
#print axioms
  LayeredNeuralFunctionalOrientationRepairFixtures.row_only_is_not_transpose_equivariant

end

end Mettapedia.MachineLearning.NeuralNetworks
