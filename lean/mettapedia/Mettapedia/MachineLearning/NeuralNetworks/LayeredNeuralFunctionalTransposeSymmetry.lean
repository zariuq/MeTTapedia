import Mettapedia.MachineLearning.NeuralNetworks.LayeredNeuralFunctionalTransformer

/-!
# Transpose symmetry at an isolated square weight matrix

The neural-functional attention entry adds a row head and a column head
using shared query, key, and value projections.  At a network consisting of
one square weight matrix, matrix transpose exchanges those two local heads.
The absent preceding and following matrices are exchanged as well.

This module isolates that boundary symmetry before lifting it to the
layer-encoded transformer.  It is a genuine extra symmetry of the isolated
square architecture, not a neuron relabeling.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

open Architecture

noncomputable section

universe u uChannel

/-- Transpose a square matrix-valued channel feature. -/
def transposeSquareMatrix
    {Neuron : Type u} {Channel : Type uChannel}
    (matrix : Neuron → Neuron → Channel → ℝ) :
    Neuron → Neuron → Channel → ℝ :=
  fun row column => matrix column row

/-- Coordinate transposition on the single matrix of a square two-layer
network. -/
def singleSquareTransposeEquiv
    (layer : FiniteNeuronLayer.{u}) :
    Equiv.Perm (LayeredWeightCoordinate [layer, layer]) :=
  Equiv.sumCongr
    (Equiv.prodComm layer.carrier layer.carrier)
    (Equiv.refl PEmpty)

/-- For an isolated square matrix, the row head after transposition is the
original column head. -/
theorem rowSliceAttention_transpose_single
    {Neuron : Type u} {Channel : Type uChannel}
    [Fintype Neuron] [Fintype Channel]
    (queries keys values : Neuron → Neuron → Channel → ℝ)
    (row column : Neuron) (channel : Channel) :
    rowSliceAttention
        (transposeSquareMatrix queries)
        (emptyPreviousWeight
          (Middle := Neuron) (Channel := Channel) :
            Neuron → PEmpty.{u + 1} → Channel → ℝ)
        (transposeSquareMatrix keys)
        (emptyPreviousWeight
          (Middle := Neuron) (Channel := Channel) :
            Neuron → PEmpty.{u + 1} → Channel → ℝ)
        (transposeSquareMatrix values)
        column (row, channel) =
      columnSliceAttention queries keys
        (emptyNextWeight
          (Current := Neuron) (Channel := Channel) :
            PEmpty.{u + 1} → Neuron → Channel → ℝ)
        values
        (emptyNextWeight
          (Current := Neuron) (Channel := Channel) :
            PEmpty.{u + 1} → Neuron → Channel → ℝ)
        column (row, channel) := by
  unfold rowSliceAttention columnSliceAttention
  have hquery :
      transportRows (Equiv.refl (Neuron × Channel))
          (columnFeatureSlice queries column) =
        rowFeatureSlice (transposeSquareMatrix queries) column := by
    funext feature
    rfl
  have hkeys :
      transportMatrix
          (Equiv.sumComm Neuron PEmpty.{u + 1})
          (Equiv.refl (Neuron × Channel))
          (columnNeighborhoodSlices keys
            (emptyNextWeight
              (Current := Neuron) (Channel := Channel) :
                PEmpty.{u + 1} → Neuron → Channel → ℝ)) =
        rowNeighborhoodSlices
          (emptyPreviousWeight
            (Middle := Neuron) (Channel := Channel) :
              Neuron → PEmpty.{u + 1} → Channel → ℝ)
          (transposeSquareMatrix keys) := by
    funext key feature
    rcases key with empty | current
    · exact nomatch empty
    · rcases feature with ⟨neuron, featureChannel⟩
      rfl
  have hvalues :
      transportMatrix
          (Equiv.sumComm Neuron PEmpty.{u + 1})
          (Equiv.refl (Neuron × Channel))
          (columnNeighborhoodSlices values
            (emptyNextWeight
              (Current := Neuron) (Channel := Channel) :
                PEmpty.{u + 1} → Neuron → Channel → ℝ)) =
        rowNeighborhoodSlices
          (emptyPreviousWeight
            (Middle := Neuron) (Channel := Channel) :
              Neuron → PEmpty.{u + 1} → Channel → ℝ)
          (transposeSquareMatrix values) := by
    funext key feature
    rcases key with empty | current
    · exact nomatch empty
    · rcases feature with ⟨neuron, featureChannel⟩
      rfl
  rw [← hquery, ← hkeys, ← hvalues]
  exact
    scaledDotProductAttention_transport
      (Equiv.sumComm Neuron PEmpty.{u + 1})
      (Equiv.refl (Neuron × Channel))
      (Equiv.refl (Neuron × Channel))
      (columnFeatureSlice queries column)
      (columnNeighborhoodSlices keys
        (emptyNextWeight
          (Current := Neuron) (Channel := Channel) :
            PEmpty.{u + 1} → Neuron → Channel → ℝ))
      (columnNeighborhoodSlices values
        (emptyNextWeight
          (Current := Neuron) (Channel := Channel) :
            PEmpty.{u + 1} → Neuron → Channel → ℝ))
      (row, channel)

/-- For an isolated square matrix, the column head after transposition is
the original row head. -/
theorem columnSliceAttention_transpose_single
    {Neuron : Type u} {Channel : Type uChannel}
    [Fintype Neuron] [Fintype Channel]
    (queries keys values : Neuron → Neuron → Channel → ℝ)
    (row column : Neuron) (channel : Channel) :
    columnSliceAttention
        (transposeSquareMatrix queries)
        (transposeSquareMatrix keys)
        (emptyNextWeight
          (Current := Neuron) (Channel := Channel) :
            PEmpty.{u + 1} → Neuron → Channel → ℝ)
        (transposeSquareMatrix values)
        (emptyNextWeight
          (Current := Neuron) (Channel := Channel) :
            PEmpty.{u + 1} → Neuron → Channel → ℝ)
        row (column, channel) =
      rowSliceAttention queries
        (emptyPreviousWeight
          (Middle := Neuron) (Channel := Channel) :
            Neuron → PEmpty.{u + 1} → Channel → ℝ)
        keys
        (emptyPreviousWeight
          (Middle := Neuron) (Channel := Channel) :
            Neuron → PEmpty.{u + 1} → Channel → ℝ)
        values row (column, channel) := by
  unfold rowSliceAttention columnSliceAttention
  have hquery :
      transportRows (Equiv.refl (Neuron × Channel))
          (rowFeatureSlice queries row) =
        columnFeatureSlice (transposeSquareMatrix queries) row := by
    funext feature
    rfl
  have hkeys :
      transportMatrix
          (Equiv.sumComm PEmpty.{u + 1} Neuron)
          (Equiv.refl (Neuron × Channel))
          (rowNeighborhoodSlices
            (emptyPreviousWeight
              (Middle := Neuron) (Channel := Channel) :
                Neuron → PEmpty.{u + 1} → Channel → ℝ)
            keys) =
        columnNeighborhoodSlices
          (transposeSquareMatrix keys)
          (emptyNextWeight
            (Current := Neuron) (Channel := Channel) :
              PEmpty.{u + 1} → Neuron → Channel → ℝ) := by
    funext key feature
    rcases key with current | empty
    · rcases feature with ⟨neuron, featureChannel⟩
      rfl
    · exact nomatch empty
  have hvalues :
      transportMatrix
          (Equiv.sumComm PEmpty.{u + 1} Neuron)
          (Equiv.refl (Neuron × Channel))
          (rowNeighborhoodSlices
            (emptyPreviousWeight
              (Middle := Neuron) (Channel := Channel) :
                Neuron → PEmpty.{u + 1} → Channel → ℝ)
            values) =
        columnNeighborhoodSlices
          (transposeSquareMatrix values)
          (emptyNextWeight
            (Current := Neuron) (Channel := Channel) :
              PEmpty.{u + 1} → Neuron → Channel → ℝ) := by
    funext key feature
    rcases key with current | empty
    · rcases feature with ⟨neuron, featureChannel⟩
      rfl
    · exact nomatch empty
  rw [← hquery, ← hkeys, ← hvalues]
  exact
    scaledDotProductAttention_transport
      (Equiv.sumComm PEmpty.{u + 1} Neuron)
      (Equiv.refl (Neuron × Channel))
      (Equiv.refl (Neuron × Channel))
      (rowFeatureSlice queries row)
      (rowNeighborhoodSlices
        (emptyPreviousWeight
          (Middle := Neuron) (Channel := Channel) :
            Neuron → PEmpty.{u + 1} → Channel → ℝ)
        keys)
      (rowNeighborhoodSlices
        (emptyPreviousWeight
          (Middle := Neuron) (Channel := Channel) :
            Neuron → PEmpty.{u + 1} → Channel → ℝ)
        values)
      (column, channel)

/-! ## The complete boundary-aware attention layer -/

/-- Restricting transposed global features to the only weight matrix gives
the ordinary square-matrix transpose. -/
theorem firstWeightMatrix_singleSquareTranspose
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel}
    (features : LayeredWeightFeatures [layer, layer] Channel) :
    firstWeightMatrix
        (transportRows (singleSquareTransposeEquiv layer) features) =
      transposeSquareMatrix (firstWeightMatrix features) := by
  funext row column channel
  rfl

/-- The complete boundary-aware neural-functional attention layer commutes
with transpose on a network consisting of one square matrix.  The proof
uses the exchange of the row and column heads and ordinary coordinate
equivariance of the global head. -/
theorem layeredNeuralFunctionalAttention_singleSquareTranspose
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel} [Fintype Channel]
    (queries keys values :
      LayeredWeightFeatures [layer, layer] Channel)
    (coordinate : LayeredWeightCoordinate [layer, layer])
    (channel : Channel) :
    layeredNeuralFunctionalAttention [layer, layer]
        (transportRows (singleSquareTransposeEquiv layer) queries)
        (transportRows (singleSquareTransposeEquiv layer) keys)
        (transportRows (singleSquareTransposeEquiv layer) values)
        (singleSquareTransposeEquiv layer coordinate) channel =
      layeredNeuralFunctionalAttention [layer, layer]
        queries keys values coordinate channel := by
  rcases coordinate with pair | empty
  · rcases pair with ⟨row, column⟩
    unfold layeredNeuralFunctionalAttention
      layeredNeuralFunctionalAttentionFrom
      neuralFunctionalAttentionEntry
    change
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
      rowSliceAttention
          (firstWeightMatrix queries)
          (emptyPreviousWeight
            (Middle := layer.carrier) (Channel := Channel) :
              layer.carrier → PEmpty.{u + 1} → Channel → ℝ)
          (firstWeightMatrix keys)
          (emptyPreviousWeight
            (Middle := layer.carrier) (Channel := Channel) :
              layer.carrier → PEmpty.{u + 1} → Channel → ℝ)
          (firstWeightMatrix values)
          row (column, channel) +
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

/-! ## The layer-encoded transformer -/

/-- A single matrix has one layer label, so its layer encoding commutes with
transpose. -/
theorem layeredWeightLayerEncoding_singleSquareTranspose
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel}
    (encoding : ℕ → Channel → ℝ)
    (features : LayeredWeightFeatures [layer, layer] Channel) :
    layeredWeightLayerEncoding [layer, layer] encoding
        (transportRows (singleSquareTransposeEquiv layer) features) =
      transportRows (singleSquareTransposeEquiv layer)
        (layeredWeightLayerEncoding [layer, layer] encoding features) := by
  funext coordinate channel
  rcases coordinate with pair | empty
  · rcases pair with ⟨row, column⟩
    rfl
  · exact nomatch empty

/-- Transpose is an exact equivariance of the actual layer-encoded,
pointwise-projected neural-functional transformer on an isolated square
matrix, for every choice of projections, encoding, and input features. -/
theorem layeredNeuralFunctionalTransformer_singleSquareTranspose
    (layer : FiniteNeuronLayer.{u})
    {Channel : Type uChannel} [Fintype Channel]
    (encoding : ℕ → Channel → ℝ)
    (queryProjection keyProjection valueProjection :
      (Channel → ℝ) → Channel → ℝ)
    (features : LayeredWeightFeatures [layer, layer] Channel)
    (coordinate : LayeredWeightCoordinate [layer, layer])
    (channel : Channel) :
    layeredNeuralFunctionalTransformer [layer, layer] encoding
        queryProjection keyProjection valueProjection
        (transportRows (singleSquareTransposeEquiv layer) features)
        (singleSquareTransposeEquiv layer coordinate) channel =
      layeredNeuralFunctionalTransformer [layer, layer] encoding
        queryProjection keyProjection valueProjection
        features coordinate channel := by
  unfold layeredNeuralFunctionalTransformer
  rw [layeredWeightLayerEncoding_singleSquareTranspose]
  rw [layeredPointwiseChannelMap_transport]
  rw [layeredPointwiseChannelMap_transport]
  rw [layeredPointwiseChannelMap_transport]
  exact
    layeredNeuralFunctionalAttention_singleSquareTranspose layer
      (layeredPointwiseChannelMap queryProjection
        (layeredWeightLayerEncoding [layer, layer] encoding features))
      (layeredPointwiseChannelMap keyProjection
        (layeredWeightLayerEncoding [layer, layer] encoding features))
      (layeredPointwiseChannelMap valueProjection
        (layeredWeightLayerEncoding [layer, layer] encoding features))
      coordinate channel

namespace LayeredNeuralFunctionalTransposeFixtures

open LayeredWeightSpaceFixtures

abbrev transposeLayer : FiniteNeuronLayer := finLayer 2

abbrev transposeShape : List FiniteNeuronLayer :=
  [transposeLayer, transposeLayer]

/-- Transpose is nontrivial on a `2 × 2` matrix. -/
theorem singleSquareTranspose_moves_offDiagonal :
    singleSquareTransposeEquiv transposeLayer
        (Sum.inl ((0 : Fin 2), (1 : Fin 2))) =
      Sum.inl ((1 : Fin 2), (0 : Fin 2)) := by
  rfl

/-- The extra transpose symmetry is not induced by independent neuron
permutations of the input and output layers. -/
theorem singleSquareTranspose_is_not_genuine :
    ¬ ∃ permutation : LayerNeuronPermutation transposeShape,
      genuineLayerWeightEquiv transposeShape permutation =
        singleSquareTransposeEquiv transposeLayer := by
  rintro ⟨permutation, equality⟩
  have at00 := congrArg
    (fun coordinateEquiv :
        Equiv.Perm (LayeredWeightCoordinate transposeShape) =>
      coordinateEquiv (Sum.inl ((0 : Fin 2), (0 : Fin 2))))
    equality
  have at01 := congrArg
    (fun coordinateEquiv :
        Equiv.Perm (LayeredWeightCoordinate transposeShape) =>
      coordinateEquiv (Sum.inl ((0 : Fin 2), (1 : Fin 2))))
    equality
  change
    Sum.inl (permutation.2.1 0, permutation.1 0) =
      Sum.inl ((0 : Fin 2), (0 : Fin 2)) at at00
  change
    Sum.inl (permutation.2.1 0, permutation.1 1) =
      Sum.inl ((1 : Fin 2), (0 : Fin 2)) at at01
  injection at00 with pair00
  injection at01 with pair01
  have row00 : permutation.2.1 0 = (0 : Fin 2) :=
    congrArg Prod.fst pair00
  have row01 : permutation.2.1 0 = (1 : Fin 2) :=
    congrArg Prod.fst pair01
  have impossible : (0 : Fin 2) = 1 := row00.symm.trans row01
  norm_num at impossible

end LayeredNeuralFunctionalTransposeFixtures

#print axioms rowSliceAttention_transpose_single
#print axioms columnSliceAttention_transpose_single
#print axioms firstWeightMatrix_singleSquareTranspose
#print axioms
  layeredNeuralFunctionalAttention_singleSquareTranspose
#print axioms
  layeredWeightLayerEncoding_singleSquareTranspose
#print axioms
  layeredNeuralFunctionalTransformer_singleSquareTranspose
#print axioms
  LayeredNeuralFunctionalTransposeFixtures.singleSquareTranspose_moves_offDiagonal
#print axioms
  LayeredNeuralFunctionalTransposeFixtures.singleSquareTranspose_is_not_genuine

end

end Mettapedia.MachineLearning.NeuralNetworks
