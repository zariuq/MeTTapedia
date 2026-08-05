import Mettapedia.MachineLearning.NeuralNetworks.LayeredNeuralFunctionalAttention
import Mettapedia.MachineLearning.NeuralNetworks.LayeredWeightSpaceMinimality

/-!
# Layer-encoded neural functional self-attention

This module composes the boundary-aware arbitrary-depth implementation of
Neural Functional Transformer self-attention with the source construction's
learned matrix-layer encoding and pointwise query, key, and value
projections.

The positive theorem proves equivariance of the actual composition under
every genuine neuron permutation.  Exact-real fixtures then give one
non-equivariance witness for each false-symmetry class used in the source
minimality proof: moving weights across matrices, using a row action that
depends on the column, and decoupling the two appearances of a shared hidden
layer.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

open Architecture

noncomputable section

universe u uChannel

/-- Apply one channel projection independently at every coordinate of a
heterogeneous weight space. -/
def layeredPointwiseChannelMap
    {layers : List (FiniteNeuronLayer.{u})}
    {Channel : Type uChannel}
    (projection : (Channel → ℝ) → Channel → ℝ)
    (features : LayeredWeightFeatures layers Channel) :
    LayeredWeightFeatures layers Channel :=
  fun coordinate => projection (features coordinate)

/-- Pointwise channel projections commute with every weight-coordinate
relabeling. -/
theorem layeredPointwiseChannelMap_transport
    {layers : List (FiniteNeuronLayer.{u})}
    {Channel : Type uChannel}
    (coordinateRelabel : Equiv.Perm (LayeredWeightCoordinate layers))
    (projection : (Channel → ℝ) → Channel → ℝ)
    (features : LayeredWeightFeatures layers Channel) :
    layeredPointwiseChannelMap projection
        (transportRows coordinateRelabel features) =
      transportRows coordinateRelabel
        (layeredPointwiseChannelMap projection features) := by
  funext transportedCoordinate channel
  obtain ⟨coordinate, rfl⟩ :=
    coordinateRelabel.surjective transportedCoordinate
  simp [layeredPointwiseChannelMap, transportRows]

/-- Add the source's learned vector encoding for the matrix layer. -/
def layeredWeightLayerEncoding
    {Channel : Type uChannel}
    (layers : List (FiniteNeuronLayer.{u}))
    (encoding : ℕ → Channel → ℝ)
    (features : LayeredWeightFeatures layers Channel) :
    LayeredWeightFeatures layers Channel :=
  addLayerVectorEncoding
    (layeredWeightLayer layers) encoding features

/-- Layer encoding commutes with every genuine neuron relabeling. -/
theorem layeredWeightLayerEncoding_transport
    {Channel : Type uChannel}
    (layers : List (FiniteNeuronLayer.{u}))
    (permutation : LayerNeuronPermutation layers)
    (encoding : ℕ → Channel → ℝ)
    (features : LayeredWeightFeatures layers Channel) :
    layeredWeightLayerEncoding layers encoding
        (transportRows
          (genuineLayerWeightEquiv layers permutation) features) =
      transportRows
        (genuineLayerWeightEquiv layers permutation)
        (layeredWeightLayerEncoding layers encoding features) := by
  funext transportedCoordinate channel
  obtain ⟨coordinate, rfl⟩ :=
    (genuineLayerWeightEquiv layers permutation).surjective
      transportedCoordinate
  simpa [layeredWeightLayerEncoding, transportRows] using
    genuineLayerWeightEquiv_layerEncoding_transport
      permutation encoding features coordinate channel

/-- Source-level `SA ∘ LayerEnc`: add the learned matrix-layer encoding,
project queries, keys, and values pointwise, and apply boundary-aware
arbitrary-depth neural-functional self-attention. -/
def layeredNeuralFunctionalTransformer
    {Channel : Type uChannel} [Fintype Channel]
    (layers : List (FiniteNeuronLayer.{u}))
    (encoding : ℕ → Channel → ℝ)
    (queryProjection keyProjection valueProjection :
      (Channel → ℝ) → Channel → ℝ)
    (features : LayeredWeightFeatures layers Channel) :
    LayeredWeightFeatures layers Channel :=
  let encoded :=
    layeredWeightLayerEncoding layers encoding features
  layeredNeuralFunctionalAttention layers
    (layeredPointwiseChannelMap queryProjection encoded)
    (layeredPointwiseChannelMap keyProjection encoded)
    (layeredPointwiseChannelMap valueProjection encoded)

/-- The actual layer-encoded, pointwise-projected arbitrary-depth
construction is equivariant under every genuine neuron permutation. -/
theorem layeredNeuralFunctionalTransformer_transport
    {Channel : Type uChannel} [Fintype Channel]
    (layers : List (FiniteNeuronLayer.{u}))
    (permutation : LayerNeuronPermutation layers)
    (encoding : ℕ → Channel → ℝ)
    (queryProjection keyProjection valueProjection :
      (Channel → ℝ) → Channel → ℝ)
    (features : LayeredWeightFeatures layers Channel)
    (coordinate : LayeredWeightCoordinate layers)
    (channel : Channel) :
    layeredNeuralFunctionalTransformer layers encoding
        queryProjection keyProjection valueProjection
        (transportRows
          (genuineLayerWeightEquiv layers permutation) features)
        (genuineLayerWeightEquiv layers permutation coordinate)
        channel =
      layeredNeuralFunctionalTransformer layers encoding
        queryProjection keyProjection valueProjection
        features coordinate channel := by
  unfold layeredNeuralFunctionalTransformer
  rw [layeredWeightLayerEncoding_transport
    layers permutation encoding features]
  rw [layeredPointwiseChannelMap_transport]
  rw [layeredPointwiseChannelMap_transport]
  rw [layeredPointwiseChannelMap_transport]
  exact
    layeredNeuralFunctionalAttention_transport
      layers permutation
      (layeredPointwiseChannelMap queryProjection
        (layeredWeightLayerEncoding layers encoding features))
      (layeredPointwiseChannelMap keyProjection
        (layeredWeightLayerEncoding layers encoding features))
      (layeredPointwiseChannelMap valueProjection
        (layeredWeightLayerEncoding layers encoding features))
      coordinate channel

namespace LayeredNeuralFunctionalTransformerFixtures

open LayeredWeightSpaceFixtures
open LayeredWeightSpaceMinimalityFixtures

/-- A zero query/key projection gives exact uniform attention. -/
def zeroProjection {Channel : Type*} :
    (Channel → ℝ) → Channel → ℝ :=
  fun _ _ => 0

/-- Identity value projection. -/
def identityProjection {Channel : Type*} :
    (Channel → ℝ) → Channel → ℝ :=
  id

/-- No layer encoding. -/
def zeroLayerEncoding {Channel : Type*} :
    ℕ → Channel → ℝ :=
  fun _ _ => 0

/-- Distinguish the first two matrix layers by exact values zero and one. -/
def binaryLayerEncoding :
    ℕ → Fin 1 → ℝ :=
  fun layer _ => if layer = 0 then 0 else 1

/-! ## Exact positive and negative fixtures -/

/-! ### A row action cannot depend on the column -/

abbrev squareShape : List FiniteNeuronLayer :=
  [finLayer 2, finLayer 2]

def grid00 : LayeredWeightCoordinate squareShape :=
  Sum.inl (0, 0)

def grid01 : LayeredWeightCoordinate squareShape :=
  Sum.inl (0, 1)

def grid10 : LayeredWeightCoordinate squareShape :=
  Sum.inl (1, 0)

def grid11 : LayeredWeightCoordinate squareShape :=
  Sum.inl (1, 1)

/-- Swap one cell between rows while leaving the other column fixed. -/
def partialRowCellSwap :
    Equiv.Perm (LayeredWeightCoordinate squareShape) :=
  Equiv.swap grid00 grid10

/-- The first row of the `2 × 2` matrix has value one; the second has value
zero. -/
def firstRowFeatures :
    LayeredWeightFeatures squareShape (Fin 1)
  | Sum.inl (row, _), _ => if row = 0 then 1 else 0
  | Sum.inr empty, _ => nomatch empty

def movedFirstRowFeatures :
    LayeredWeightFeatures squareShape (Fin 1) :=
  transportRows partialRowCellSwap firstRowFeatures

theorem movedFirstRowFeatures_grid00 :
    movedFirstRowFeatures grid00 0 = 0 := by
  simp
    [movedFirstRowFeatures, transportRows, partialRowCellSwap,
      firstRowFeatures, grid00, grid10]

theorem movedFirstRowFeatures_grid10 :
    movedFirstRowFeatures grid10 0 = 1 := by
  simp
    [movedFirstRowFeatures, transportRows, partialRowCellSwap,
      firstRowFeatures, grid00, grid10]

theorem movedFirstRowFeatures_grid11 :
    movedFirstRowFeatures grid11 0 = 0 := by
  unfold movedFirstRowFeatures transportRows
  rw [show partialRowCellSwap.symm grid11 = grid11 by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro equality
      change
        Sum.inl ((1 : Fin 2), (1 : Fin 2)) =
          Sum.inl (0, 0) at equality
      simp at equality
    · intro equality
      change
        Sum.inl ((1 : Fin 2), (1 : Fin 2)) =
          Sum.inl (1, 0) at equality
      simp at equality]
  norm_num [firstRowFeatures, grid11]

theorem firstRowFeatures_sum :
    (∑ coordinate : LayeredWeightCoordinate squareShape,
      firstRowFeatures coordinate 0) = 2 := by
  change
    (∑ coordinate : (Fin 2 × Fin 2) ⊕ PEmpty,
      firstRowFeatures coordinate 0) = 2
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  simp [firstRowFeatures]

theorem movedFirstRowFeatures_sum :
    (∑ coordinate : LayeredWeightCoordinate squareShape,
      movedFirstRowFeatures coordinate 0) = 2 := by
  unfold movedFirstRowFeatures
  change
    (∑ coordinate,
      transportRows partialRowCellSwap
        (fun source => firstRowFeatures source 0) coordinate) = 2
  calc
    _ = ∑ coordinate, firstRowFeatures coordinate 0 := by
      symm
      apply Fintype.sum_equiv partialRowCellSwap
      intro coordinate
      simp [transportRows]
    _ = 2 := firstRowFeatures_sum

theorem firstRowFeatures_transformer_value :
    layeredNeuralFunctionalTransformer squareShape zeroLayerEncoding
        zeroProjection zeroProjection identityProjection
        firstRowFeatures grid00 0 =
      2 := by
  norm_num
    [layeredNeuralFunctionalTransformer, layeredWeightLayerEncoding,
      addLayerVectorEncoding, layeredPointwiseChannelMap,
      layeredNeuralFunctionalAttention,
      layeredNeuralFunctionalAttentionFrom,
      neuralFunctionalAttentionEntry, rowSliceAttention,
      columnSliceAttention, pointWeightAttention,
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
    ((2 : ℝ)⁻¹ + 1 +
      (4 : ℝ)⁻¹ *
        ∑ coordinate, firstRowFeatures coordinate 0) = 2
  rw [firstRowFeatures_sum]
  norm_num

theorem movedFirstRowFeatures_transformer_value :
    layeredNeuralFunctionalTransformer squareShape zeroLayerEncoding
        zeroProjection zeroProjection identityProjection
        movedFirstRowFeatures (partialRowCellSwap grid00) 0 =
      3 / 2 := by
  rw [show partialRowCellSwap grid00 = grid10 by
    simp [partialRowCellSwap]]
  norm_num
    [layeredNeuralFunctionalTransformer, layeredWeightLayerEncoding,
      addLayerVectorEncoding, layeredPointwiseChannelMap,
      layeredNeuralFunctionalAttention,
      layeredNeuralFunctionalAttentionFrom,
      neuralFunctionalAttentionEntry, rowSliceAttention,
      columnSliceAttention, pointWeightAttention,
      scaledDotProductAttention, softmaxAttention, attentionWeight,
      attentionMass, scaledAttentionDotScore, attentionDotScore,
      rowFeatureSlice, columnFeatureSlice, rowNeighborhoodSlices,
      columnNeighborhoodSlices, firstWeightMatrix, squareShape,
      grid10, zeroLayerEncoding, zeroProjection, identityProjection]
  rw [show Fintype.card (finLayer 2).carrier = 2 by rfl]
  rw [show
    Fintype.card (LayeredWeightCoordinate squareShape) = 4 by rfl]
  simp only [Fin.sum_univ_two]
  change
    ((2 : ℝ)⁻¹ * movedFirstRowFeatures grid00 0 +
        (2 : ℝ)⁻¹ * movedFirstRowFeatures grid10 0 +
        ((2 : ℝ)⁻¹ * movedFirstRowFeatures grid10 0 +
          (2 : ℝ)⁻¹ * movedFirstRowFeatures grid11 0) +
        ∑ coordinate,
          (4 : ℝ)⁻¹ * movedFirstRowFeatures coordinate 0) =
      3 / 2
  rw [movedFirstRowFeatures_grid00, movedFirstRowFeatures_grid10,
    movedFirstRowFeatures_grid11]
  rw [← Finset.mul_sum, movedFirstRowFeatures_sum]
  norm_num

/-- The actual layer-encoded transformer is not equivariant under a cell
swap whose row action depends on the column. -/
theorem partialRowCellSwap_is_not_transformer_equivariant :
    layeredNeuralFunctionalTransformer squareShape zeroLayerEncoding
        zeroProjection zeroProjection identityProjection
        movedFirstRowFeatures (partialRowCellSwap grid00) 0 ≠
      layeredNeuralFunctionalTransformer squareShape zeroLayerEncoding
        zeroProjection zeroProjection identityProjection
        firstRowFeatures grid00 0 := by
  rw [movedFirstRowFeatures_transformer_value,
    firstRowFeatures_transformer_value]
  norm_num

/-! ### Adjacent matrices must share one hidden-neuron action -/

def secondOutgoing :
    LayeredWeightCoordinate tinyThreeLayerShape :=
  Sum.inr (Sum.inl (0, 1))

/-- Put value one at one incoming and the incident outgoing hidden weight. -/
def coupledPairFeatures :
    LayeredWeightFeatures tinyThreeLayerShape (Fin 1)
  | Sum.inl (row, _), _ => if row = 0 then 1 else 0
  | Sum.inr (Sum.inl (_, column)), _ =>
      if column = 0 then 1 else 0
  | Sum.inr (Sum.inr empty), _ => nomatch empty

def decoupledWeightEquiv :
    Equiv.Perm (LayeredWeightCoordinate tinyThreeLayerShape) :=
  layerwiseMatrixWeightEquiv
    tinyThreeLayerShape tinyDecoupledHiddenSwap

def decoupledPairFeatures :
    LayeredWeightFeatures tinyThreeLayerShape (Fin 1) :=
  transportRows decoupledWeightEquiv coupledPairFeatures

theorem decoupledWeightEquiv_symm_firstIncoming :
    decoupledWeightEquiv.symm firstIncoming = secondIncoming := by
  change
    Sum.inl ((Equiv.swap (0 : Fin 2) 1) 0, (0 : Fin 1)) =
      Sum.inl (1, 0)
  simp

theorem decoupledPairFeatures_firstIncoming :
    decoupledPairFeatures firstIncoming 0 = 0 := by
  unfold decoupledPairFeatures transportRows
  rw [decoupledWeightEquiv_symm_firstIncoming]
  norm_num [coupledPairFeatures, secondIncoming]

theorem decoupledPairFeatures_firstOutgoing :
    decoupledPairFeatures firstOutgoing 0 = 1 := by
  rfl

theorem decoupledPairFeatures_secondOutgoing :
    decoupledPairFeatures secondOutgoing 0 = 0 := by
  rfl

theorem coupledPairFeatures_sum :
    (∑ coordinate : LayeredWeightCoordinate tinyThreeLayerShape,
      coupledPairFeatures coordinate 0) = 2 := by
  change
    (∑ coordinate :
        (Fin 2 × Fin 1) ⊕ ((Fin 1 × Fin 2) ⊕ PEmpty),
      coupledPairFeatures coordinate 0) = 2
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  simp [coupledPairFeatures]
  norm_num

theorem decoupledPairFeatures_sum :
    (∑ coordinate : LayeredWeightCoordinate tinyThreeLayerShape,
      decoupledPairFeatures coordinate 0) = 2 := by
  unfold decoupledPairFeatures
  change
    (∑ coordinate,
      transportRows decoupledWeightEquiv
        (fun source => coupledPairFeatures source 0) coordinate) = 2
  calc
    _ = ∑ coordinate, coupledPairFeatures coordinate 0 := by
      symm
      apply Fintype.sum_equiv decoupledWeightEquiv
      intro coordinate
      simp [transportRows]
    _ = 2 := coupledPairFeatures_sum

theorem coupledPairFeatures_transformer_value :
    layeredNeuralFunctionalTransformer tinyThreeLayerShape
        zeroLayerEncoding zeroProjection zeroProjection
        identityProjection coupledPairFeatures firstOutgoing 0 =
      2 := by
  norm_num
    [layeredNeuralFunctionalTransformer, layeredWeightLayerEncoding,
      addLayerVectorEncoding, layeredPointwiseChannelMap,
      layeredNeuralFunctionalAttention,
      layeredNeuralFunctionalAttentionFrom,
      neuralFunctionalAttentionEntry, rowSliceAttention,
      columnSliceAttention, pointWeightAttention,
      scaledDotProductAttention, softmaxAttention, attentionWeight,
      attentionMass, scaledAttentionDotScore, attentionDotScore,
      rowFeatureSlice, columnFeatureSlice, rowNeighborhoodSlices,
      columnNeighborhoodSlices, firstWeightMatrix,
      tailWeightFeatures, coupledPairFeatures, tinyThreeLayerShape,
      firstOutgoing, zeroLayerEncoding, zeroProjection,
      identityProjection]
  rw [show Fintype.card (finLayer 2).carrier = 2 by rfl]
  rw [show
    Fintype.card
      (LayeredWeightCoordinate tinyThreeLayerShape) = 4 by rfl]
  rw [← Finset.mul_sum]
  change
    (1 + (2 : ℝ)⁻¹ +
      (4 : ℝ)⁻¹ *
        ∑ coordinate, coupledPairFeatures coordinate 0) = 2
  rw [coupledPairFeatures_sum]
  norm_num

theorem decoupledPairFeatures_transformer_value :
    layeredNeuralFunctionalTransformer tinyThreeLayerShape
        zeroLayerEncoding zeroProjection zeroProjection
        identityProjection decoupledPairFeatures
        (decoupledWeightEquiv firstOutgoing) 0 =
      3 / 2 := by
  rw [show
    decoupledWeightEquiv firstOutgoing = firstOutgoing by rfl]
  norm_num
    [layeredNeuralFunctionalTransformer, layeredWeightLayerEncoding,
      addLayerVectorEncoding, layeredPointwiseChannelMap,
      layeredNeuralFunctionalAttention,
      layeredNeuralFunctionalAttentionFrom,
      neuralFunctionalAttentionEntry, rowSliceAttention,
      columnSliceAttention, pointWeightAttention,
      scaledDotProductAttention, softmaxAttention, attentionWeight,
      attentionMass, scaledAttentionDotScore, attentionDotScore,
      rowFeatureSlice, columnFeatureSlice, rowNeighborhoodSlices,
      columnNeighborhoodSlices, firstWeightMatrix,
      tailWeightFeatures, tinyThreeLayerShape, firstOutgoing,
      zeroLayerEncoding, zeroProjection, identityProjection]
  rw [show Fintype.card (finLayer 2).carrier = 2 by rfl]
  rw [show
    Fintype.card
      (LayeredWeightCoordinate tinyThreeLayerShape) = 4 by rfl]
  simp only [Fin.sum_univ_two]
  rw [show
    (Sum.inl ((0 : Fin 2), default) :
      LayeredWeightCoordinate tinyThreeLayerShape) =
        firstIncoming by rfl]
  rw [show
    (Sum.inr (Sum.inl (default, (0 : Fin 2))) :
      LayeredWeightCoordinate tinyThreeLayerShape) =
        firstOutgoing by rfl]
  change
    ((1 : ℝ) / 2 * decoupledPairFeatures firstIncoming 0 +
        1 / 2 * decoupledPairFeatures firstOutgoing 0 +
        ((2 : ℝ)⁻¹ * decoupledPairFeatures firstOutgoing 0 +
          (2 : ℝ)⁻¹ * decoupledPairFeatures secondOutgoing 0) +
        ∑ coordinate,
          (4 : ℝ)⁻¹ * decoupledPairFeatures coordinate 0) =
      3 / 2
  rw [decoupledPairFeatures_firstIncoming,
    decoupledPairFeatures_firstOutgoing,
    decoupledPairFeatures_secondOutgoing]
  rw [← Finset.mul_sum, decoupledPairFeatures_sum]
  norm_num

/-- Swapping a hidden row in the incoming matrix while leaving its outgoing
column fixed changes the actual transformer output. -/
theorem decoupledHiddenSwap_is_not_transformer_equivariant :
    layeredNeuralFunctionalTransformer tinyThreeLayerShape
        zeroLayerEncoding zeroProjection zeroProjection
        identityProjection decoupledPairFeatures
        (decoupledWeightEquiv firstOutgoing) 0 ≠
      layeredNeuralFunctionalTransformer tinyThreeLayerShape
        zeroLayerEncoding zeroProjection zeroProjection
        identityProjection coupledPairFeatures firstOutgoing 0 := by
  rw [decoupledPairFeatures_transformer_value,
    coupledPairFeatures_transformer_value]
  norm_num

/-! ### Matrix-layer encoding excludes cross-matrix permutations -/

def zeroWeightFeatures :
    LayeredWeightFeatures tinyThreeLayerShape (Fin 1) :=
  fun _ _ => 0

theorem binaryLayerWeightedGlobalSum :
    (∑ coordinate :
        LayeredWeightCoordinate tinyThreeLayerShape,
      if layeredWeightLayer tinyThreeLayerShape coordinate = 0
      then (0 : ℝ)
      else (1 : ℝ) / 4) =
      1 / 2 := by
  change
    (∑ coordinate :
        (Fin 2 × Fin 1) ⊕ ((Fin 1 × Fin 2) ⊕ PEmpty),
      if layeredWeightLayer tinyThreeLayerShape coordinate = 0
      then (0 : ℝ)
      else (1 : ℝ) / 4) =
      1 / 2
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [layeredWeightLayer, tinyThreeLayerShape]

theorem binaryLayerEncoding_firstIncoming_value :
    layeredNeuralFunctionalTransformer tinyThreeLayerShape
        binaryLayerEncoding zeroProjection zeroProjection
        identityProjection zeroWeightFeatures firstIncoming 0 =
      1 := by
  norm_num
    [layeredNeuralFunctionalTransformer, layeredWeightLayerEncoding,
      addLayerVectorEncoding, layeredPointwiseChannelMap,
      layeredNeuralFunctionalAttention,
      layeredNeuralFunctionalAttentionFrom,
      neuralFunctionalAttentionEntry, rowSliceAttention,
      columnSliceAttention, pointWeightAttention,
      scaledDotProductAttention, softmaxAttention, attentionWeight,
      attentionMass, scaledAttentionDotScore, attentionDotScore,
      rowFeatureSlice, columnFeatureSlice, rowNeighborhoodSlices,
      columnNeighborhoodSlices, firstWeightMatrix,
      tailWeightFeatures, zeroWeightFeatures, tinyThreeLayerShape,
      firstIncoming, layeredWeightLayer, binaryLayerEncoding,
      zeroProjection, identityProjection]
  rw [show
    Fintype.card
      (LayeredWeightCoordinate tinyThreeLayerShape) = 4 by rfl]
  norm_num
  rw [binaryLayerWeightedGlobalSum]
  norm_num

theorem binaryLayerEncoding_firstOutgoing_value :
    layeredNeuralFunctionalTransformer tinyThreeLayerShape
        binaryLayerEncoding zeroProjection zeroProjection
        identityProjection zeroWeightFeatures firstOutgoing 0 =
      2 := by
  norm_num
    [layeredNeuralFunctionalTransformer, layeredWeightLayerEncoding,
      addLayerVectorEncoding, layeredPointwiseChannelMap,
      layeredNeuralFunctionalAttention,
      layeredNeuralFunctionalAttentionFrom,
      neuralFunctionalAttentionEntry, rowSliceAttention,
      columnSliceAttention, pointWeightAttention,
      scaledDotProductAttention, softmaxAttention, attentionWeight,
      attentionMass, scaledAttentionDotScore, attentionDotScore,
      rowFeatureSlice, columnFeatureSlice, rowNeighborhoodSlices,
      columnNeighborhoodSlices, firstWeightMatrix,
      tailWeightFeatures, zeroWeightFeatures, tinyThreeLayerShape,
      firstOutgoing, layeredWeightLayer, binaryLayerEncoding,
      zeroProjection, identityProjection]
  rw [show
    Fintype.card
      (LayeredWeightCoordinate tinyThreeLayerShape) = 4 by rfl]
  norm_num
  rw [binaryLayerWeightedGlobalSum]
  norm_num

theorem crossLayerSwap_transports_zeroWeightFeatures :
    transportRows crossLayerSwap zeroWeightFeatures =
      zeroWeightFeatures := by
  funext coordinate channel
  simp [transportRows, zeroWeightFeatures]

/-- Moving a zero-valued weight across matrix layers changes which learned
layer vector it receives, and therefore changes the source transformer. -/
theorem crossLayerSwap_is_not_transformer_equivariant :
    layeredNeuralFunctionalTransformer tinyThreeLayerShape
        binaryLayerEncoding zeroProjection zeroProjection
        identityProjection
        (transportRows crossLayerSwap zeroWeightFeatures)
        (crossLayerSwap firstIncoming) 0 ≠
      layeredNeuralFunctionalTransformer tinyThreeLayerShape
        binaryLayerEncoding zeroProjection zeroProjection
        identityProjection zeroWeightFeatures firstIncoming 0 := by
  rw [crossLayerSwap_transports_zeroWeightFeatures]
  rw [show crossLayerSwap firstIncoming = firstOutgoing by
    simp [crossLayerSwap]]
  rw [binaryLayerEncoding_firstOutgoing_value,
    binaryLayerEncoding_firstIncoming_value]
  norm_num

/-! ### A nontrivial genuine hidden swap remains equivariant -/

theorem genuineHiddenSwap_transformer_transport :
    layeredNeuralFunctionalTransformer tinyThreeLayerShape
        zeroLayerEncoding zeroProjection zeroProjection
        identityProjection
        (transportRows
          (genuineLayerWeightEquiv
            tinyThreeLayerShape tinyHiddenSwap)
          coupledPairFeatures)
        (genuineLayerWeightEquiv
          tinyThreeLayerShape tinyHiddenSwap firstIncoming) 0 =
      layeredNeuralFunctionalTransformer tinyThreeLayerShape
        zeroLayerEncoding zeroProjection zeroProjection
        identityProjection coupledPairFeatures firstIncoming 0 := by
  exact
    layeredNeuralFunctionalTransformer_transport
      tinyThreeLayerShape tinyHiddenSwap zeroLayerEncoding
      zeroProjection zeroProjection identityProjection
      coupledPairFeatures firstIncoming 0

end LayeredNeuralFunctionalTransformerFixtures

#print axioms layeredPointwiseChannelMap_transport
#print axioms layeredWeightLayerEncoding_transport
#print axioms layeredNeuralFunctionalTransformer_transport
#print axioms
  LayeredNeuralFunctionalTransformerFixtures.partialRowCellSwap_is_not_transformer_equivariant
#print axioms
  LayeredNeuralFunctionalTransformerFixtures.decoupledHiddenSwap_is_not_transformer_equivariant
#print axioms
  LayeredNeuralFunctionalTransformerFixtures.crossLayerSwap_is_not_transformer_equivariant
#print axioms
  LayeredNeuralFunctionalTransformerFixtures.genuineHiddenSwap_transformer_transport

end

end Mettapedia.MachineLearning.NeuralNetworks
