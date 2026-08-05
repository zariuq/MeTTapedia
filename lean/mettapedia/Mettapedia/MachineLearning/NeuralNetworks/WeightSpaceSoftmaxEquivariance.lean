import Mettapedia.MachineLearning.NeuralNetworks.RelationSoftmaxSymmetry
import Mettapedia.MachineLearning.NeuralNetworks.WeightSpaceRelationEquivariance

/-!
# Nonlinear softmax realization of the two-layer weight-space signature

The complete two-layer structural signature consists of a layer label, the
row and column incidences of both weight matrices, and the hidden-neuron
incidence shared by adjacent matrices.  This file realizes every incidence as
a relation-masked softmax head and the layer label as a learned additive
encoding.

An arbitrary coordinate permutation commutes with the resulting family
exactly when it is induced by genuine input, hidden, and output neuron
permutations.  This is a nonlinear strengthening of the relation-kernel
classification.  It realizes the same structural boundary as slice
attention, but does not identify this family with the full arbitrary-depth
Neural Functional Transformer equations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

open Architecture

noncomputable section

section LabelEncoding

variable {Coordinate Label : Type*}

/-- A learned additive coordinate-label encoding commutes with one fixed
coordinate permutation for every natural-valued encoding and input feature. -/
def PermutationLabelEncodingEquivariant
    (permutation : Equiv.Perm Coordinate)
    (label : Coordinate → Label) : Prop :=
  ∀ (encoding : Label → ℕ) (features : Coordinate → ℕ) coordinate,
    addCoordinateEncoding label encoding
        (transportRows permutation features) (permutation coordinate) =
      addCoordinateEncoding label encoding features coordinate

theorem labelPreserved_implies_permutationLabelEncodingEquivariant
    (permutation : Equiv.Perm Coordinate)
    (label : Coordinate → Label)
    (preserves : ∀ coordinate,
      label (permutation coordinate) = label coordinate) :
    PermutationLabelEncodingEquivariant permutation label := by
  intro encoding features coordinate
  simp [addCoordinateEncoding, transportRows, preserves coordinate]

theorem permutationLabelEncodingEquivariant_implies_labelPreserved
    [DecidableEq Label]
    (permutation : Equiv.Perm Coordinate)
    (label : Coordinate → Label)
    (equivariant :
      PermutationLabelEncodingEquivariant permutation label) :
    ∀ coordinate, label (permutation coordinate) = label coordinate := by
  intro coordinate
  by_contra labelChanged
  let encoding : Label → ℕ :=
    fun candidate =>
      if candidate = label (permutation coordinate) then 1 else 0
  have reverse :
      label coordinate ≠ label (permutation coordinate) :=
    Ne.symm labelChanged
  have equality :=
    equivariant encoding (fun _ => 0) coordinate
  simp [addCoordinateEncoding, transportRows, encoding, reverse]
    at equality

/-- Exact boundary for the learned encoding family under one permutation. -/
theorem permutationLabelEncodingEquivariant_iff_labelPreserved
    [DecidableEq Label]
    (permutation : Equiv.Perm Coordinate)
    (label : Coordinate → Label) :
    PermutationLabelEncodingEquivariant permutation label ↔
      ∀ coordinate, label (permutation coordinate) = label coordinate :=
  ⟨permutationLabelEncodingEquivariant_implies_labelPreserved
      permutation label,
    labelPreserved_implies_permutationLabelEncodingEquivariant
      permutation label⟩

end LabelEncoding

section TwoLayerSoftmax

/-- The nonlinear two-layer structural family: a learned layer encoding and
five relation-masked softmax heads. -/
def CompleteTwoLayerRelationSoftmaxEquivariant
    {Input Hidden Output : Type*}
    [Fintype Input] [Fintype Hidden] [Fintype Output]
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output)) : Prop :=
  PermutationLabelEncodingEquivariant permutation twoLayerWeightLayer ∧
    RelationSoftmaxEquivariant permutation
      (SameIncomingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    RelationSoftmaxEquivariant permutation
      (SameIncomingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    RelationSoftmaxEquivariant permutation
      (SameOutgoingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    RelationSoftmaxEquivariant permutation
      (SameOutgoingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    RelationSoftmaxEquivariant permutation
      (SharesHidden
        (Input := Input) (Hidden := Hidden) (Output := Output))

theorem twoLayerLabelEncodingEquivariant_iff_preservesSumSide
    {Input Hidden Output : Type*}
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output)) :
    PermutationLabelEncodingEquivariant
        permutation twoLayerWeightLayer ↔
      PreservesSumSide permutation := by
  rw [permutationLabelEncodingEquivariant_iff_labelPreserved]
  exact
    (preservesSumSide_iff_preservesTwoLayerWeightLayer permutation).symm

/-- The nonlinear family and the underlying six structural observables have
the same exact permutation group. -/
theorem completeTwoLayerRelationSoftmaxEquivariant_iff_preservesStructure
    {Input Hidden Output : Type*}
    [Fintype Input] [Fintype Hidden] [Fintype Output]
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output)) :
    CompleteTwoLayerRelationSoftmaxEquivariant permutation ↔
      PreservesCompleteTwoLayerStructure permutation := by
  unfold CompleteTwoLayerRelationSoftmaxEquivariant
  unfold PreservesCompleteTwoLayerStructure
  rw [twoLayerLabelEncodingEquivariant_iff_preservesSumSide]
  rw [relationSoftmaxEquivariant_iff_preservesRelation]
  rw [relationSoftmaxEquivariant_iff_preservesRelation]
  rw [relationSoftmaxEquivariant_iff_preservesRelation]
  rw [relationSoftmaxEquivariant_iff_preservesRelation]
  rw [relationSoftmaxEquivariant_iff_preservesRelation]

/-- Nonlinear two-layer minimal-equivariance crown: the complete relation
softmax family admits exactly the genuine neuron-permutation group. -/
theorem completeTwoLayerRelationSoftmaxEquivariant_iff_genuine
    {Input Hidden Output : Type*}
    [Fintype Input] [Fintype Hidden] [Fintype Output]
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    (inputAnchor : Input) (hiddenAnchor : Hidden)
    (outputAnchor : Output)
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output)) :
    CompleteTwoLayerRelationSoftmaxEquivariant permutation ↔
      IsGenuineTwoLayerNeuronPermutation permutation := by
  rw [
    completeTwoLayerRelationSoftmaxEquivariant_iff_preservesStructure,
    preservesCompleteTwoLayerStructure_iff_genuine
      inputAnchor hiddenAnchor outputAnchor]

end TwoLayerSoftmax

namespace WeightSpaceSoftmaxFixtures

open Fixtures

/-- The genuine hidden-neuron swap acts on both adjacent matrices. -/
def genuineHiddenSwap : Equiv.Perm TinyWeightCoordinate :=
  layerwiseTwoLayerWeightPermutation
    (Equiv.prodCongr hiddenSwap (Equiv.refl (Fin 1)))
    (Equiv.prodCongr (Equiv.refl (Fin 1)) hiddenSwap)

theorem genuineHiddenSwap_relationSoftmaxEquivariant :
    CompleteTwoLayerRelationSoftmaxEquivariant genuineHiddenSwap := by
  apply
    (completeTwoLayerRelationSoftmaxEquivariant_iff_genuine
      (0 : Fin 1) (0 : Fin 2) (0 : Fin 1) genuineHiddenSwap).2
  exact
    ⟨Equiv.refl (Fin 1), hiddenSwap, Equiv.refl (Fin 1), rfl⟩

/-- Decoupling the adjacent hidden permutations breaks the shared-hidden
softmax head. -/
theorem falseIncomingSwap_not_completeRelationSoftmaxEquivariant :
    ¬ CompleteTwoLayerRelationSoftmaxEquivariant falseIncomingSwap := by
  intro equivariant
  rcases equivariant with
    ⟨layerEncoding, incomingRows, incomingColumns, outgoingRows,
      outgoingColumns, hiddenIncidence⟩
  have preservesHidden :=
    (relationSoftmaxEquivariant_iff_preservesRelation
      falseIncomingSwap
      (SharesHidden
        (Input := Fin 1) (Hidden := Fin 2) (Output := Fin 1))).1
      hiddenIncidence
  exact false_swap_breaks_selected_pair
    ((preservesHidden incomingZero outgoingZero).2
      original_pair_shares_hidden)

/-- Moving a coordinate across weight matrices breaks the learned layer
encoding component. -/
theorem crossLayerSwap_not_completeRelationSoftmaxEquivariant :
    ¬ CompleteTwoLayerRelationSoftmaxEquivariant crossLayerSwap := by
  intro equivariant
  have layerPreserved :=
    (permutationLabelEncodingEquivariant_iff_labelPreserved
      crossLayerSwap
      (twoLayerWeightLayer
        (Input := Fin 1) (Hidden := Fin 2) (Output := Fin 1))).1
      equivariant.1
  exact crossLayerSwap_changes_label
    (layerPreserved incomingZero)

end WeightSpaceSoftmaxFixtures

#print axioms
  completeTwoLayerRelationSoftmaxEquivariant_iff_preservesStructure
#print axioms completeTwoLayerRelationSoftmaxEquivariant_iff_genuine
#print axioms
  WeightSpaceSoftmaxFixtures.genuineHiddenSwap_relationSoftmaxEquivariant
#print axioms
  WeightSpaceSoftmaxFixtures.falseIncomingSwap_not_completeRelationSoftmaxEquivariant
#print axioms
  WeightSpaceSoftmaxFixtures.crossLayerSwap_not_completeRelationSoftmaxEquivariant

end

end Mettapedia.MachineLearning.NeuralNetworks
