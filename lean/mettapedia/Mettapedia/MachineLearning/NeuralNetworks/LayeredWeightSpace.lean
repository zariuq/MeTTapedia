import Mettapedia.MachineLearning.NeuralNetworks.Architecture.NeuralFunctionalAttentionEquivariance

/-!
# Heterogeneous arbitrary-depth weight space

A feed-forward network may have a different finite neuron type at every
layer.  Padding all layers into one common type introduces coordinates that
are not present in the network and obscures its genuine permutation group.
This file instead represents a network shape as a heterogeneous list of
finite neuron types.

Weight coordinates are a nested sum of adjacent matrix grids.  A family of
neuron permutations induces a coordinate equivalence recursively: the target
permutation acts on each matrix row, the source permutation acts on each
matrix column, and the shared layer permutation is reused in the next
matrix.  The construction therefore enforces the coupling required by a
genuine neuron relabeling at every depth.

The main theorems show that this action preserves matrix-layer labels and
that global feature transport restricts exactly to row/column transport on
the first matrix and to the same recursive action on the tail network.  These
are the structural gluing laws needed to lift the local neural-functional
attention equations to arbitrary depth.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

open Architecture

noncomputable section

universe u uChannel uValue

/-- A neuron layer with finite, decidable coordinates. -/
structure FiniteNeuronLayer where
  carrier : Type u
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

attribute [instance] FiniteNeuronLayer.fintype
attribute [instance] FiniteNeuronLayer.decidableEq

/-- Weight coordinates for a heterogeneous list of neuron layers.  The first
summand is the matrix from the first layer to the second; the recursive
summand contains every later matrix. -/
def LayeredWeightCoordinate :
    List (FiniteNeuronLayer.{u}) → Type u
  | [] => PEmpty
  | [_] => PEmpty
  | input :: output :: rest =>
      (output.carrier × input.carrier) ⊕
        LayeredWeightCoordinate (output :: rest)

instance layeredWeightCoordinateFintype :
    (layers : List (FiniteNeuronLayer.{u})) →
      Fintype (LayeredWeightCoordinate layers)
  | [] => by
      simpa [LayeredWeightCoordinate] using
        (inferInstance : Fintype PEmpty)
  | [_] => by
      simpa [LayeredWeightCoordinate] using
        (inferInstance : Fintype PEmpty)
  | input :: output :: rest => by
      letI := layeredWeightCoordinateFintype (output :: rest)
      simpa [LayeredWeightCoordinate] using
        (inferInstance :
          Fintype
            ((output.carrier × input.carrier) ⊕
              LayeredWeightCoordinate (output :: rest)))

instance layeredWeightCoordinateDecidableEq :
    (layers : List (FiniteNeuronLayer.{u})) →
      DecidableEq (LayeredWeightCoordinate layers)
  | [] => by
      simpa [LayeredWeightCoordinate] using
        (inferInstance : DecidableEq PEmpty)
  | [_] => by
      simpa [LayeredWeightCoordinate] using
        (inferInstance : DecidableEq PEmpty)
  | input :: output :: rest => by
      letI := layeredWeightCoordinateDecidableEq (output :: rest)
      simpa [LayeredWeightCoordinate] using
        (inferInstance :
          DecidableEq
            ((output.carrier × input.carrier) ⊕
              LayeredWeightCoordinate (output :: rest)))

/-- One independent neuron permutation per layer. -/
def LayerNeuronPermutation :
    List (FiniteNeuronLayer.{u}) → Type u
  | [] => PUnit.{u + 1}
  | layer :: rest =>
      Equiv.Perm layer.carrier × LayerNeuronPermutation rest

/-- The genuine action of layerwise neuron permutations on every adjacent
weight matrix.  The permutation of an internal layer is shared by the
preceding matrix's rows and the following matrix's columns. -/
def genuineLayerWeightEquiv :
    (layers : List (FiniteNeuronLayer.{u})) →
      LayerNeuronPermutation layers →
      Equiv.Perm (LayeredWeightCoordinate layers)
  | [], _ => Equiv.refl PEmpty
  | [_], _ => Equiv.refl PEmpty
  | _input :: output :: rest, permutation =>
      Equiv.sumCongr
        (Equiv.prodCongr permutation.2.1 permutation.1)
        (genuineLayerWeightEquiv (output :: rest) permutation.2)

/-- Zero-based matrix-layer label of a weight coordinate. -/
def layeredWeightLayer :
    (layers : List (FiniteNeuronLayer.{u})) →
      LayeredWeightCoordinate layers → ℕ
  | [], coordinate => nomatch coordinate
  | [_], coordinate => nomatch coordinate
  | _ :: _ :: _, Sum.inl _ => 0
  | _input :: output :: rest, Sum.inr coordinate =>
      (layeredWeightLayer (output :: rest) coordinate).succ

/-- Genuine neuron relabeling never moves a weight between matrices. -/
theorem genuineLayerWeightEquiv_preserves_layer :
    ∀ (layers : List (FiniteNeuronLayer.{u}))
      (permutation : LayerNeuronPermutation layers)
      (coordinate : LayeredWeightCoordinate layers),
      layeredWeightLayer layers
          (genuineLayerWeightEquiv layers permutation coordinate) =
        layeredWeightLayer layers coordinate
  | [], _, coordinate => nomatch coordinate
  | [_], _, coordinate => nomatch coordinate
  | _ :: _ :: _, _, Sum.inl _ => rfl
  | _input :: output :: rest, permutation, Sum.inr coordinate => by
      simp only [genuineLayerWeightEquiv, layeredWeightLayer]
      exact congrArg Nat.succ
        (genuineLayerWeightEquiv_preserves_layer
          (output :: rest) permutation.2 coordinate)

/-- Multi-channel features attached to every weight coordinate. -/
abbrev LayeredWeightFeatures
    (layers : List (FiniteNeuronLayer.{u}))
    (Channel : Type uChannel) :=
  LayeredWeightCoordinate layers → Channel → ℝ

/-- Restrict global features to the first weight matrix. -/
def firstWeightMatrix
    {input output : FiniteNeuronLayer.{u}}
    {rest : List (FiniteNeuronLayer.{u})}
    {Channel : Type uChannel} {Value : Type uValue}
    (features :
      LayeredWeightCoordinate (input :: output :: rest) →
        Channel → Value) :
    output.carrier → input.carrier → Channel → Value :=
  fun row column channel =>
    features (Sum.inl (row, column)) channel

/-- Restrict global features to all matrices after the first. -/
def tailWeightFeatures
    {input output : FiniteNeuronLayer.{u}}
    {rest : List (FiniteNeuronLayer.{u})}
    {Channel : Type uChannel} {Value : Type uValue}
    (features :
      LayeredWeightCoordinate (input :: output :: rest) →
        Channel → Value) :
    LayeredWeightCoordinate (output :: rest) → Channel → Value :=
  fun coordinate channel =>
    features (Sum.inr coordinate) channel

/-- Transporting global features by a genuine neuron relabeling restricts on
the first matrix to the ordinary row/column matrix transport. -/
theorem firstWeightMatrix_transport
    {input output : FiniteNeuronLayer.{u}}
    {rest : List (FiniteNeuronLayer.{u})}
    {Channel : Type uChannel} {Value : Type uValue}
    (permutation :
      Equiv.Perm input.carrier ×
        LayerNeuronPermutation (output :: rest))
    (features :
      LayeredWeightCoordinate (input :: output :: rest) →
        Channel → Value) :
    firstWeightMatrix
        (transportRows
          (genuineLayerWeightEquiv
            (input :: output :: rest) permutation)
          features) =
      transportMatrix permutation.2.1 permutation.1
        (firstWeightMatrix features) := by
  rfl

/-- The tail restriction of genuine global transport is exactly the genuine
transport for the tail network. -/
theorem tailWeightFeatures_transport
    {input output : FiniteNeuronLayer.{u}}
    {rest : List (FiniteNeuronLayer.{u})}
    {Channel : Type uChannel} {Value : Type uValue}
    (permutation :
      Equiv.Perm input.carrier ×
        LayerNeuronPermutation (output :: rest))
    (features :
      LayeredWeightCoordinate (input :: output :: rest) →
        Channel → Value) :
    tailWeightFeatures
        (transportRows
          (genuineLayerWeightEquiv
            (input :: output :: rest) permutation)
          features) =
      transportRows
        (genuineLayerWeightEquiv (output :: rest) permutation.2)
        (tailWeightFeatures features) := by
  rfl

/-- Learned vector layer encodings commute with every genuine arbitrary-depth
neuron relabeling. -/
theorem genuineLayerWeightEquiv_layerEncoding_transport
    {layers : List (FiniteNeuronLayer.{u})}
    {Channel : Type uChannel}
    (permutation : LayerNeuronPermutation layers)
    (encoding : ℕ → Channel → ℝ)
    (features : LayeredWeightFeatures layers Channel)
    (coordinate : LayeredWeightCoordinate layers)
    (channel : Channel) :
    addLayerVectorEncoding
        (layeredWeightLayer layers) encoding
        (transportRows
          (genuineLayerWeightEquiv layers permutation) features)
        (genuineLayerWeightEquiv layers permutation coordinate)
        channel =
      addLayerVectorEncoding
        (layeredWeightLayer layers) encoding
        features coordinate channel := by
  exact
    addLayerVectorEncoding_transport
      (genuineLayerWeightEquiv layers permutation)
      (layeredWeightLayer layers)
      (layeredWeightLayer layers)
      (genuineLayerWeightEquiv_preserves_layer layers permutation)
      encoding features coordinate channel

namespace LayeredWeightSpaceFixtures

abbrev finLayer (width : ℕ) : FiniteNeuronLayer where
  carrier := Fin width
  fintype := inferInstance
  decidableEq := inferInstance

abbrev tinyThreeLayerShape : List FiniteNeuronLayer :=
  [finLayer 1, finLayer 2, finLayer 1]

def tinyHiddenSwap :
    LayerNeuronPermutation tinyThreeLayerShape :=
  (Equiv.refl (Fin 1),
    (Equiv.swap 0 1,
      (Equiv.refl (Fin 1), PUnit.unit)))

def firstIncoming :
    LayeredWeightCoordinate tinyThreeLayerShape :=
  Sum.inl (0, 0)

def secondIncoming :
    LayeredWeightCoordinate tinyThreeLayerShape :=
  Sum.inl (1, 0)

def firstOutgoing :
    LayeredWeightCoordinate tinyThreeLayerShape :=
  Sum.inr (Sum.inl (0, 0))

def crossLayerSwap :
    Equiv.Perm (LayeredWeightCoordinate tinyThreeLayerShape) :=
  Equiv.swap firstIncoming firstOutgoing

/-- The hidden swap moves the first matrix's row. -/
theorem hiddenSwap_moves_firstMatrix_row :
    genuineLayerWeightEquiv tinyThreeLayerShape tinyHiddenSwap
        firstIncoming =
      secondIncoming := by
  change
    Sum.inl ((Equiv.swap (0 : Fin 2) 1) 0, (0 : Fin 1)) =
      Sum.inl ((1 : Fin 2), (0 : Fin 1))
  simp

/-- The same hidden swap moves the second matrix's column, exhibiting the
required adjacent-layer coupling. -/
theorem hiddenSwap_moves_secondMatrix_column :
    genuineLayerWeightEquiv tinyThreeLayerShape tinyHiddenSwap
        firstOutgoing =
      Sum.inr (Sum.inl (0, 1)) := by
  change
    Sum.inr
        (Sum.inl
          ((0 : Fin 1), (Equiv.swap (0 : Fin 2) 1) 0)) =
      Sum.inr (Sum.inl ((0 : Fin 1), (1 : Fin 2)))
  simp

/-- An arbitrary cross-layer coordinate swap violates the matrix-layer label
preserved by every genuine neuron relabeling. -/
theorem crossLayerSwap_changes_layer :
    layeredWeightLayer tinyThreeLayerShape
        (crossLayerSwap firstIncoming) = 1 ∧
      layeredWeightLayer tinyThreeLayerShape firstIncoming = 0 := by
  norm_num
    [tinyThreeLayerShape, crossLayerSwap, firstIncoming,
      firstOutgoing, layeredWeightLayer, Equiv.swap_apply_def]

end LayeredWeightSpaceFixtures

#print axioms genuineLayerWeightEquiv_preserves_layer
#print axioms firstWeightMatrix_transport
#print axioms tailWeightFeatures_transport
#print axioms genuineLayerWeightEquiv_layerEncoding_transport
#print axioms LayeredWeightSpaceFixtures.hiddenSwap_moves_firstMatrix_row
#print axioms
  LayeredWeightSpaceFixtures.hiddenSwap_moves_secondMatrix_column
#print axioms LayeredWeightSpaceFixtures.crossLayerSwap_changes_layer

end

end Mettapedia.MachineLearning.NeuralNetworks
