import Mettapedia.MachineLearning.NeuralNetworks.Architecture.SliceAttentionEquivariance

/-!
# Equivariance of neural-functional attention slices

Zhou et al., *Neural Functional Transformers*
(NeurIPS 2023, arXiv:2305.13546), define a weight-space attention entry as
the sum of three heads:

* attention from a row of the current weight matrix to columns of the
  preceding matrix and rows of the current matrix;
* attention from a column of the current matrix to columns of the current
  matrix and rows of the following matrix;
* pointwise attention over all weight coordinates.

This file gives exact finite semantics for those three source-level heads.
Each theorem permits distinct finite neuron types in every adjacent layer.
The row and column theorems therefore cover arbitrary rectangular weight
matrices rather than a padded common-width representation.

The channel projections in the source are pointwise maps, so they commute
with neuron relabeling before attention is applied.  The final negative
fixture changes only one side of the feature coordinates and records that
the shared query/key relabeling premise is essential.

These are local slice theorems.  Enumerating and gluing every slice of an
arbitrary-depth architecture is a separate theorem.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

open scoped BigOperators

universe uPrevious uMiddle uCurrent uNext uChannel uCoordinate
  uPrevious' uMiddle' uCurrent' uNext' uCoordinate'

/-! ## Matrix slices and pointwise channel projections -/

/-- A row of a matrix-valued feature, flattened over column and channel. -/
def rowFeatureSlice
    {Row : Type*} {Column : Type*} {Channel : Type*}
    (matrix : Row → Column → Channel → ℝ)
    (row : Row) :
    Column × Channel → ℝ :=
  fun columnChannel => matrix row columnChannel.1 columnChannel.2

/-- A column of a matrix-valued feature, flattened over row and channel. -/
def columnFeatureSlice
    {Row : Type*} {Column : Type*} {Channel : Type*}
    (matrix : Row → Column → Channel → ℝ)
    (column : Column) :
    Row × Channel → ℝ :=
  fun rowChannel => matrix rowChannel.1 column rowChannel.2

/-- Apply one channel map independently at every weight coordinate.  This is
the structural content of the source's query/key/value projections. -/
def pointwiseChannelMap
    {Row Column Channel : Type*}
    (projection : (Channel → ℝ) → Channel → ℝ)
    (matrix : Row → Column → Channel → ℝ) :
    Row → Column → Channel → ℝ :=
  fun row column => projection (matrix row column)

theorem pointwiseChannelMap_transport
    {RowLeft : Type*} {RowRight : Type*}
    {ColumnLeft : Type*} {ColumnRight : Type*}
    {Channel : Type*}
    (rowRelabel : RowLeft ≃ RowRight)
    (columnRelabel : ColumnLeft ≃ ColumnRight)
    (projection : (Channel → ℝ) → Channel → ℝ)
    (matrix : RowLeft → ColumnLeft → Channel → ℝ) :
    pointwiseChannelMap projection
        (transportMatrix rowRelabel columnRelabel matrix) =
      transportMatrix rowRelabel columnRelabel
        (pointwiseChannelMap projection matrix) := by
  funext row column channel
  simp [pointwiseChannelMap, transportMatrix]

theorem rowFeatureSlice_transport
    {RowLeft : Type*} {RowRight : Type*}
    {ColumnLeft : Type*} {ColumnRight : Type*}
    {Channel : Type*}
    (rowRelabel : RowLeft ≃ RowRight)
    (columnRelabel : ColumnLeft ≃ ColumnRight)
    (matrix : RowLeft → ColumnLeft → Channel → ℝ)
    (row : RowLeft) :
    rowFeatureSlice
        (transportMatrix rowRelabel columnRelabel matrix)
        (rowRelabel row) =
      transportRows
        (Equiv.prodCongr columnRelabel (Equiv.refl Channel))
        (rowFeatureSlice matrix row) := by
  funext transportedFeature
  obtain ⟨⟨column, channel⟩, rfl⟩ :=
    (Equiv.prodCongr columnRelabel (Equiv.refl Channel)).surjective
      transportedFeature
  simp [rowFeatureSlice, transportMatrix, transportRows]

theorem columnFeatureSlice_transport
    {RowLeft : Type*} {RowRight : Type*}
    {ColumnLeft : Type*} {ColumnRight : Type*}
    {Channel : Type*}
    (rowRelabel : RowLeft ≃ RowRight)
    (columnRelabel : ColumnLeft ≃ ColumnRight)
    (matrix : RowLeft → ColumnLeft → Channel → ℝ)
    (column : ColumnLeft) :
    columnFeatureSlice
        (transportMatrix rowRelabel columnRelabel matrix)
        (columnRelabel column) =
      transportRows
        (Equiv.prodCongr rowRelabel (Equiv.refl Channel))
        (columnFeatureSlice matrix column) := by
  funext transportedFeature
  obtain ⟨⟨row, channel⟩, rfl⟩ :=
    (Equiv.prodCongr rowRelabel (Equiv.refl Channel)).surjective
      transportedFeature
  simp [columnFeatureSlice, transportMatrix, transportRows]

/-! ## The row head: source Equation (4) -/

/-- The key/value slices visible from a current-matrix row.  A left key is a
column of the preceding matrix; a right key is a row of the current matrix.
Both have feature coordinates `Middle × Channel`. -/
def rowNeighborhoodSlices
    {Previous Middle Current Channel : Type*}
    (previous : Middle → Previous → Channel → ℝ)
    (current : Current → Middle → Channel → ℝ) :
    Previous ⊕ Current → Middle × Channel → ℝ
  | Sum.inl previousColumn =>
      columnFeatureSlice previous previousColumn
  | Sum.inr currentRow =>
      rowFeatureSlice current currentRow

theorem rowNeighborhoodSlices_transport
    {PreviousLeft : Type uPrevious}
    {PreviousRight : Type uPrevious'}
    {MiddleLeft : Type uMiddle} {MiddleRight : Type uMiddle'}
    {CurrentLeft : Type uCurrent} {CurrentRight : Type uCurrent'}
    {Channel : Type uChannel}
    (previousRelabel : PreviousLeft ≃ PreviousRight)
    (middleRelabel : MiddleLeft ≃ MiddleRight)
    (currentRelabel : CurrentLeft ≃ CurrentRight)
    (previous : MiddleLeft → PreviousLeft → Channel → ℝ)
    (current : CurrentLeft → MiddleLeft → Channel → ℝ) :
    rowNeighborhoodSlices
        (transportMatrix middleRelabel previousRelabel previous)
        (transportMatrix currentRelabel middleRelabel current) =
      transportMatrix
        (Equiv.sumCongr previousRelabel currentRelabel)
        (Equiv.prodCongr middleRelabel (Equiv.refl Channel))
        (rowNeighborhoodSlices previous current) := by
  funext transportedKey transportedFeature
  obtain ⟨key, rfl⟩ :=
    (Equiv.sumCongr previousRelabel currentRelabel).surjective
      transportedKey
  obtain ⟨feature, rfl⟩ :=
    (Equiv.prodCongr middleRelabel (Equiv.refl Channel)).surjective
      transportedFeature
  rcases key with previousColumn | currentRow <;>
    rcases feature with ⟨middle, channel⟩ <;>
    simp
      [rowNeighborhoodSlices, rowFeatureSlice, columnFeatureSlice,
        transportMatrix]

/-- The row-slice attention term in Equation (4). -/
def rowSliceAttention
    {Previous Middle Current Channel : Type*}
    [Fintype Previous] [Fintype Middle] [Fintype Current]
    [Fintype Channel]
    (queryCurrent : Current → Middle → Channel → ℝ)
    (keyPrevious : Middle → Previous → Channel → ℝ)
    (keyCurrent : Current → Middle → Channel → ℝ)
    (valuePrevious : Middle → Previous → Channel → ℝ)
    (valueCurrent : Current → Middle → Channel → ℝ)
    (row : Current) :
    Middle × Channel → ℝ :=
  scaledDotProductAttention
    (rowFeatureSlice queryCurrent row)
    (rowNeighborhoodSlices keyPrevious keyCurrent)
    (rowNeighborhoodSlices valuePrevious valueCurrent)

theorem rowSliceAttention_transport
    {PreviousLeft : Type uPrevious}
    {PreviousRight : Type uPrevious'}
    {MiddleLeft : Type uMiddle} {MiddleRight : Type uMiddle'}
    {CurrentLeft : Type uCurrent} {CurrentRight : Type uCurrent'}
    {Channel : Type uChannel}
    [Fintype PreviousLeft] [Fintype PreviousRight]
    [Fintype MiddleLeft] [Fintype MiddleRight]
    [Fintype CurrentLeft] [Fintype CurrentRight]
    [Fintype Channel]
    (previousRelabel : PreviousLeft ≃ PreviousRight)
    (middleRelabel : MiddleLeft ≃ MiddleRight)
    (currentRelabel : CurrentLeft ≃ CurrentRight)
    (queryCurrent : CurrentLeft → MiddleLeft → Channel → ℝ)
    (keyPrevious : MiddleLeft → PreviousLeft → Channel → ℝ)
    (keyCurrent : CurrentLeft → MiddleLeft → Channel → ℝ)
    (valuePrevious : MiddleLeft → PreviousLeft → Channel → ℝ)
    (valueCurrent : CurrentLeft → MiddleLeft → Channel → ℝ)
    (row : CurrentLeft) (feature : MiddleLeft × Channel) :
    rowSliceAttention
        (transportMatrix currentRelabel middleRelabel queryCurrent)
        (transportMatrix middleRelabel previousRelabel keyPrevious)
        (transportMatrix currentRelabel middleRelabel keyCurrent)
        (transportMatrix middleRelabel previousRelabel valuePrevious)
        (transportMatrix currentRelabel middleRelabel valueCurrent)
        (currentRelabel row)
        ((Equiv.prodCongr middleRelabel (Equiv.refl Channel)) feature) =
      rowSliceAttention queryCurrent keyPrevious keyCurrent
        valuePrevious valueCurrent row feature := by
  unfold rowSliceAttention
  rw [rowFeatureSlice_transport]
  rw [rowNeighborhoodSlices_transport]
  rw [rowNeighborhoodSlices_transport]
  exact
    scaledDotProductAttention_transport
      (Equiv.sumCongr previousRelabel currentRelabel)
      (Equiv.prodCongr middleRelabel (Equiv.refl Channel))
      (Equiv.prodCongr middleRelabel (Equiv.refl Channel))
      (rowFeatureSlice queryCurrent row)
      (rowNeighborhoodSlices keyPrevious keyCurrent)
      (rowNeighborhoodSlices valuePrevious valueCurrent)
      feature

/-! ## The column head: source Equation (5) -/

/-- The key/value slices visible from a current-matrix column.  A left key is
a column of the current matrix; a right key is a row of the following matrix.
Both have feature coordinates `Current × Channel`. -/
def columnNeighborhoodSlices
    {Middle Current Next Channel : Type*}
    (current : Current → Middle → Channel → ℝ)
    (next : Next → Current → Channel → ℝ) :
    Middle ⊕ Next → Current × Channel → ℝ
  | Sum.inl currentColumn =>
      columnFeatureSlice current currentColumn
  | Sum.inr nextRow =>
      rowFeatureSlice next nextRow

theorem columnNeighborhoodSlices_transport
    {MiddleLeft : Type uMiddle} {MiddleRight : Type uMiddle'}
    {CurrentLeft : Type uCurrent} {CurrentRight : Type uCurrent'}
    {NextLeft : Type uNext} {NextRight : Type uNext'}
    {Channel : Type uChannel}
    (middleRelabel : MiddleLeft ≃ MiddleRight)
    (currentRelabel : CurrentLeft ≃ CurrentRight)
    (nextRelabel : NextLeft ≃ NextRight)
    (current : CurrentLeft → MiddleLeft → Channel → ℝ)
    (next : NextLeft → CurrentLeft → Channel → ℝ) :
    columnNeighborhoodSlices
        (transportMatrix currentRelabel middleRelabel current)
        (transportMatrix nextRelabel currentRelabel next) =
      transportMatrix
        (Equiv.sumCongr middleRelabel nextRelabel)
        (Equiv.prodCongr currentRelabel (Equiv.refl Channel))
        (columnNeighborhoodSlices current next) := by
  funext transportedKey transportedFeature
  obtain ⟨key, rfl⟩ :=
    (Equiv.sumCongr middleRelabel nextRelabel).surjective
      transportedKey
  obtain ⟨feature, rfl⟩ :=
    (Equiv.prodCongr currentRelabel (Equiv.refl Channel)).surjective
      transportedFeature
  rcases key with currentColumn | nextRow <;>
    rcases feature with ⟨currentRow, channel⟩ <;>
    simp
      [columnNeighborhoodSlices, rowFeatureSlice, columnFeatureSlice,
        transportMatrix]

/-- The column-slice attention term in Equation (5). -/
def columnSliceAttention
    {Middle Current Next Channel : Type*}
    [Fintype Middle] [Fintype Current] [Fintype Next]
    [Fintype Channel]
    (queryCurrent : Current → Middle → Channel → ℝ)
    (keyCurrent : Current → Middle → Channel → ℝ)
    (keyNext : Next → Current → Channel → ℝ)
    (valueCurrent : Current → Middle → Channel → ℝ)
    (valueNext : Next → Current → Channel → ℝ)
    (column : Middle) :
    Current × Channel → ℝ :=
  scaledDotProductAttention
    (columnFeatureSlice queryCurrent column)
    (columnNeighborhoodSlices keyCurrent keyNext)
    (columnNeighborhoodSlices valueCurrent valueNext)

theorem columnSliceAttention_transport
    {MiddleLeft : Type uMiddle} {MiddleRight : Type uMiddle'}
    {CurrentLeft : Type uCurrent} {CurrentRight : Type uCurrent'}
    {NextLeft : Type uNext} {NextRight : Type uNext'}
    {Channel : Type uChannel}
    [Fintype MiddleLeft] [Fintype MiddleRight]
    [Fintype CurrentLeft] [Fintype CurrentRight]
    [Fintype NextLeft] [Fintype NextRight]
    [Fintype Channel]
    (middleRelabel : MiddleLeft ≃ MiddleRight)
    (currentRelabel : CurrentLeft ≃ CurrentRight)
    (nextRelabel : NextLeft ≃ NextRight)
    (queryCurrent : CurrentLeft → MiddleLeft → Channel → ℝ)
    (keyCurrent : CurrentLeft → MiddleLeft → Channel → ℝ)
    (keyNext : NextLeft → CurrentLeft → Channel → ℝ)
    (valueCurrent : CurrentLeft → MiddleLeft → Channel → ℝ)
    (valueNext : NextLeft → CurrentLeft → Channel → ℝ)
    (column : MiddleLeft) (feature : CurrentLeft × Channel) :
    columnSliceAttention
        (transportMatrix currentRelabel middleRelabel queryCurrent)
        (transportMatrix currentRelabel middleRelabel keyCurrent)
        (transportMatrix nextRelabel currentRelabel keyNext)
        (transportMatrix currentRelabel middleRelabel valueCurrent)
        (transportMatrix nextRelabel currentRelabel valueNext)
        (middleRelabel column)
        ((Equiv.prodCongr currentRelabel (Equiv.refl Channel)) feature) =
      columnSliceAttention queryCurrent keyCurrent keyNext
        valueCurrent valueNext column feature := by
  unfold columnSliceAttention
  rw [columnFeatureSlice_transport]
  rw [columnNeighborhoodSlices_transport]
  rw [columnNeighborhoodSlices_transport]
  exact
    scaledDotProductAttention_transport
      (Equiv.sumCongr middleRelabel nextRelabel)
      (Equiv.prodCongr currentRelabel (Equiv.refl Channel))
      (Equiv.prodCongr currentRelabel (Equiv.refl Channel))
      (columnFeatureSlice queryCurrent column)
      (columnNeighborhoodSlices keyCurrent keyNext)
      (columnNeighborhoodSlices valueCurrent valueNext)
      feature

/-! ## The global point head: source Equation (6) -/

/-- Naive attention from one weight coordinate to all weight coordinates. -/
def pointWeightAttention
    {Coordinate Channel : Type*}
    [Fintype Coordinate] [Fintype Channel]
    (queries keys values : Coordinate → Channel → ℝ)
    (coordinate : Coordinate) :
    Channel → ℝ :=
  scaledDotProductAttention
    (queries coordinate) keys values

theorem pointWeightAttention_transport
    {CoordinateLeft : Type uCoordinate}
    {CoordinateRight : Type uCoordinate'}
    {Channel : Type uChannel}
    [Fintype CoordinateLeft] [Fintype CoordinateRight]
    [Fintype Channel]
    (coordinateRelabel : CoordinateLeft ≃ CoordinateRight)
    (queries keys values : CoordinateLeft → Channel → ℝ)
    (coordinate : CoordinateLeft) (channel : Channel) :
    pointWeightAttention
        (transportRows coordinateRelabel queries)
        (transportRows coordinateRelabel keys)
        (transportRows coordinateRelabel values)
        (coordinateRelabel coordinate) channel =
      pointWeightAttention queries keys values coordinate channel := by
  unfold pointWeightAttention
  have keyTransport :
      transportRows coordinateRelabel keys =
        transportMatrix coordinateRelabel (Equiv.refl Channel) keys := by
    funext transportedCoordinate transportedChannel
    simp [transportRows, transportMatrix]
  have valueTransport :
      transportRows coordinateRelabel values =
        transportMatrix coordinateRelabel (Equiv.refl Channel) values := by
    funext transportedCoordinate transportedChannel
    simp [transportRows, transportMatrix]
  rw [transportRows_apply, keyTransport, valueTransport]
  have queryTransport :
      transportRows (Equiv.refl Channel) (queries coordinate) =
        queries coordinate := by
    funext transportedChannel
    simp [transportRows]
  conv_lhs => rw [← queryTransport]
  simpa using
    scaledDotProductAttention_transport
      coordinateRelabel (Equiv.refl Channel) (Equiv.refl Channel)
      (queries coordinate) keys values channel

/-! ## The complete local entry: source Equations (4)--(6) -/

/-- One weight-space self-attention output entry is the sum of its row,
column, and global point heads. -/
def neuralFunctionalAttentionEntry
    {Previous Middle Current Next Coordinate Channel : Type*}
    [Fintype Previous] [Fintype Middle] [Fintype Current]
    [Fintype Next] [Fintype Coordinate] [Fintype Channel]
    (queryCurrent : Current → Middle → Channel → ℝ)
    (keyPrevious : Middle → Previous → Channel → ℝ)
    (keyCurrent : Current → Middle → Channel → ℝ)
    (keyNext : Next → Current → Channel → ℝ)
    (valuePrevious : Middle → Previous → Channel → ℝ)
    (valueCurrent : Current → Middle → Channel → ℝ)
    (valueNext : Next → Current → Channel → ℝ)
    (globalQueries globalKeys globalValues :
      Coordinate → Channel → ℝ)
    (row : Current) (column : Middle)
    (coordinate : Coordinate) (channel : Channel) :
    ℝ :=
  rowSliceAttention queryCurrent
      keyPrevious keyCurrent valuePrevious valueCurrent
      row (column, channel) +
    columnSliceAttention queryCurrent
      keyCurrent keyNext valueCurrent valueNext
      column (row, channel) +
    pointWeightAttention globalQueries globalKeys globalValues
      coordinate channel

/-- Equations (4)--(6), summed exactly: one local neural-functional attention
entry commutes with all genuine row, column, neighboring-layer, and global
weight-coordinate relabelings. -/
theorem neuralFunctionalAttentionEntry_transport
    {PreviousLeft : Type uPrevious}
    {PreviousRight : Type uPrevious'}
    {MiddleLeft : Type uMiddle} {MiddleRight : Type uMiddle'}
    {CurrentLeft : Type uCurrent} {CurrentRight : Type uCurrent'}
    {NextLeft : Type uNext} {NextRight : Type uNext'}
    {CoordinateLeft : Type uCoordinate}
    {CoordinateRight : Type uCoordinate'}
    {Channel : Type uChannel}
    [Fintype PreviousLeft] [Fintype PreviousRight]
    [Fintype MiddleLeft] [Fintype MiddleRight]
    [Fintype CurrentLeft] [Fintype CurrentRight]
    [Fintype NextLeft] [Fintype NextRight]
    [Fintype CoordinateLeft] [Fintype CoordinateRight]
    [Fintype Channel]
    (previousRelabel : PreviousLeft ≃ PreviousRight)
    (middleRelabel : MiddleLeft ≃ MiddleRight)
    (currentRelabel : CurrentLeft ≃ CurrentRight)
    (nextRelabel : NextLeft ≃ NextRight)
    (coordinateRelabel : CoordinateLeft ≃ CoordinateRight)
    (queryCurrent : CurrentLeft → MiddleLeft → Channel → ℝ)
    (keyPrevious : MiddleLeft → PreviousLeft → Channel → ℝ)
    (keyCurrent : CurrentLeft → MiddleLeft → Channel → ℝ)
    (keyNext : NextLeft → CurrentLeft → Channel → ℝ)
    (valuePrevious : MiddleLeft → PreviousLeft → Channel → ℝ)
    (valueCurrent : CurrentLeft → MiddleLeft → Channel → ℝ)
    (valueNext : NextLeft → CurrentLeft → Channel → ℝ)
    (globalQueries globalKeys globalValues :
      CoordinateLeft → Channel → ℝ)
    (row : CurrentLeft) (column : MiddleLeft)
    (coordinate : CoordinateLeft) (channel : Channel) :
    neuralFunctionalAttentionEntry
        (transportMatrix currentRelabel middleRelabel queryCurrent)
        (transportMatrix middleRelabel previousRelabel keyPrevious)
        (transportMatrix currentRelabel middleRelabel keyCurrent)
        (transportMatrix nextRelabel currentRelabel keyNext)
        (transportMatrix middleRelabel previousRelabel valuePrevious)
        (transportMatrix currentRelabel middleRelabel valueCurrent)
        (transportMatrix nextRelabel currentRelabel valueNext)
        (transportRows coordinateRelabel globalQueries)
        (transportRows coordinateRelabel globalKeys)
        (transportRows coordinateRelabel globalValues)
        (currentRelabel row) (middleRelabel column)
        (coordinateRelabel coordinate) channel =
      neuralFunctionalAttentionEntry
        queryCurrent keyPrevious keyCurrent keyNext
        valuePrevious valueCurrent valueNext
        globalQueries globalKeys globalValues
        row column coordinate channel := by
  unfold neuralFunctionalAttentionEntry
  have rowTransport :=
    rowSliceAttention_transport
      previousRelabel middleRelabel currentRelabel
      queryCurrent keyPrevious keyCurrent
      valuePrevious valueCurrent row (column, channel)
  have columnTransport :=
    columnSliceAttention_transport
      middleRelabel currentRelabel nextRelabel
      queryCurrent keyCurrent keyNext
      valueCurrent valueNext column (row, channel)
  have pointTransport :=
    pointWeightAttention_transport
      coordinateRelabel globalQueries globalKeys globalValues
      coordinate channel
  simpa using congrArg₂ (· + ·)
    (congrArg₂ (· + ·) rowTransport columnTransport)
    pointTransport

/-! ## Learned layer encoding: source Equation (9) -/

/-- Add a learned vector encoding determined by a weight coordinate's layer
label. -/
def addLayerVectorEncoding
    {Coordinate Layer Channel : Type*}
    (layer : Coordinate → Layer)
    (encoding : Layer → Channel → ℝ)
    (features : Coordinate → Channel → ℝ) :
    Coordinate → Channel → ℝ :=
  fun coordinate channel =>
    features coordinate channel + encoding (layer coordinate) channel

theorem addLayerVectorEncoding_transport
    {CoordinateLeft : Type*} {CoordinateRight : Type*}
    {Layer Channel : Type*}
    (coordinateRelabel : CoordinateLeft ≃ CoordinateRight)
    (leftLayer : CoordinateLeft → Layer)
    (rightLayer : CoordinateRight → Layer)
    (preservesLayer :
      ∀ coordinate,
        rightLayer (coordinateRelabel coordinate) = leftLayer coordinate)
    (encoding : Layer → Channel → ℝ)
    (features : CoordinateLeft → Channel → ℝ)
    (coordinate : CoordinateLeft) (channel : Channel) :
    addLayerVectorEncoding rightLayer encoding
        (transportRows coordinateRelabel features)
        (coordinateRelabel coordinate) channel =
      addLayerVectorEncoding leftLayer encoding features
        coordinate channel := by
  simp
    [addLayerVectorEncoding, transportRows,
      preservesLayer coordinate]

namespace NeuralFunctionalAttentionFixtures

def featureSwap : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

def singleRowMatrix : Fin 1 → Fin 2 → Fin 1 → ℝ
  | _, 0, _ => 1
  | _, 1, _ => 0

/-- A row slice is transported exactly when its matrix columns are
transported by the same permutation. -/
theorem sharedColumnSwap_transports_rowSlice :
    rowFeatureSlice
        (transportMatrix (Equiv.refl (Fin 1)) featureSwap
          singleRowMatrix)
        0 =
      transportRows
        (Equiv.prodCongr featureSwap (Equiv.refl (Fin 1)))
        (rowFeatureSlice singleRowMatrix 0) :=
  rowFeatureSlice_transport
    (Equiv.refl (Fin 1)) featureSwap singleRowMatrix 0

/-- Relabeling only the query feature coordinate changes the source
dot-product score. -/
theorem queryOnlyFeatureSwap_breaks_sourceScore :
    attentionDotScore
        (transportRows featureSwap
          SliceAttentionFixtures.firstBasis)
        SliceAttentionFixtures.firstBasis = 0 ∧
      attentionDotScore
        SliceAttentionFixtures.firstBasis
        SliceAttentionFixtures.firstBasis = 1 :=
  SliceAttentionFixtures.queryOnlySwap_changes_dotScore

end NeuralFunctionalAttentionFixtures

#print axioms pointwiseChannelMap_transport
#print axioms rowSliceAttention_transport
#print axioms columnSliceAttention_transport
#print axioms pointWeightAttention_transport
#print axioms neuralFunctionalAttentionEntry_transport
#print axioms addLayerVectorEncoding_transport
#print axioms
  NeuralFunctionalAttentionFixtures.sharedColumnSwap_transports_rowSlice
#print axioms
  NeuralFunctionalAttentionFixtures.queryOnlyFeatureSwap_breaks_sourceScore

end

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
