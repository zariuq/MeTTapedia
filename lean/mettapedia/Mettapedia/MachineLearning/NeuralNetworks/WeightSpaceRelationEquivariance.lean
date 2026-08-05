import Mettapedia.MachineLearning.NeuralNetworks.EquivariantLinearKernel
import Mettapedia.MachineLearning.NeuralNetworks.GridRelationSymmetry
import Mettapedia.MachineLearning.NeuralNetworks.SumLabelSymmetry

/-!
# Relation-aware weight-space equivariance

Zhou et al., *Neural Functional Transformers*
(NeurIPS 2023, arXiv:2305.13546), distinguish neuron permutations from
arbitrary permutations of individual weight coordinates.  Their structured
attention couples rows and columns of adjacent weight matrices, so a genuine
neuron relabeling preserves the operator while a decoupled row/column
permutation need not.

This file isolates that structural mechanism for finite linear kernels.  A
zero-one relation kernel is equivariant exactly when the coordinate action
preserves the relation.  The result applies to any finite relation, not only
weight space.

For a two-layer network, coordinates are incoming and outgoing weights.
Their shared-hidden-neuron relation is preserved by simultaneous input,
hidden, and output neuron permutations.  Conversely, every layerwise
coordinate permutation preserving both matrix grids and their shared-hidden
incidence is induced by exactly this kind of neuron relabeling.  Cross-layer,
column-dependent-row, row-dependent-column, and uncoupled-hidden
permutations have separate executable counterexamples.

The results do not formalize the source's complete multi-layer softmax
attention equations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks

open scoped BigOperators

noncomputable section

section RelationKernels

variable {G Coordinate R : Type*}
  [Group G] [MulAction G Coordinate]

/-- A binary relation is invariant when simultaneous transport of both
coordinates preserves and reflects it. -/
def RelationInvariant
    (G : Type*) [Group G] [MulAction G Coordinate]
    (relation : Coordinate → Coordinate → Prop) : Prop :=
  ∀ (g : G) (left right : Coordinate),
    relation (g • left) (g • right) ↔ relation left right

/-- The zero-one kernel induced by a decidable binary relation. -/
def relationKernel [Zero R] [One R]
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation] :
    Coordinate → Coordinate → R :=
  fun left right => if relation left right then 1 else 0

theorem relationInvariant_implies_kernelInvariant
    [Zero R] [One R]
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (invariant : RelationInvariant G relation) :
    KernelInvariant G (relationKernel (R := R) relation) := by
  intro g left right
  by_cases original : relation left right
  · have transported := (invariant g left right).2 original
    simp [relationKernel, original, transported]
  · have transported : ¬ relation (g • left) (g • right) := by
      intro transported
      exact original ((invariant g left right).1 transported)
    simp [relationKernel, original, transported]

theorem kernelInvariant_relationKernel_implies_relationInvariant
    [Zero R] [One R] [Nontrivial R] [NeZero (1 : R)]
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation]
    (invariant :
      KernelInvariant G (relationKernel (R := R) relation)) :
    RelationInvariant G relation := by
  intro g left right
  constructor
  · intro transported
    by_contra original
    have equality := invariant g left right
    simp [relationKernel, transported, original] at equality
  · intro original
    by_contra transported
    have equality := invariant g left right
    simp [relationKernel, transported, original] at equality

variable [Fintype Coordinate] [DecidableEq Coordinate]
  [Semiring R] [Nontrivial R]

/-- Exact structural boundary: a zero-one relation kernel is equivariant if
and only if the coordinate action preserves the relation. -/
theorem relationInvariant_iff_relationKernel_equivariant
    (relation : Coordinate → Coordinate → Prop)
    [DecidableRel relation] :
    RelationInvariant G relation ↔
      KernelEquivariant G (relationKernel (R := R) relation) := by
  constructor
  · intro relationInvariant
    exact kernelInvariant_implies_kernelEquivariant
      (relationInvariant_implies_kernelInvariant relation relationInvariant)
  · intro kernelEquivariant
    exact kernelInvariant_relationKernel_implies_relationInvariant relation
      (kernelEquivariant_implies_kernelInvariant kernelEquivariant)

end RelationKernels

section CoordinateEncodings

variable {G Coordinate Label : Type*}
  [Group G] [MulAction G Coordinate]

/-- A coordinate label is invariant when the action never moves a coordinate
between label classes. -/
def LabelInvariant
    (G : Type*) [Group G] [MulAction G Coordinate]
    (label : Coordinate → Label) : Prop :=
  ∀ (g : G) (coordinate : Coordinate),
    label (g • coordinate) = label coordinate

/-- Add a learned label-dependent position encoding to every coordinate. -/
def addCoordinateEncoding
    {R : Type*} [Add R]
    (label : Coordinate → Label)
    (encoding : Label → R)
    (features : Coordinate → R) :
    Coordinate → R :=
  fun coordinate => features coordinate + encoding (label coordinate)

/-- Every natural-valued label encoding commutes with coordinate transport.
Quantifying over the whole encoding family exposes whether the labels
themselves are preserved. -/
def CoordinateEncodingFamilyEquivariant
    (G : Type*) [Group G] [MulAction G Coordinate]
    (label : Coordinate → Label) : Prop :=
  ∀ (encoding : Label → ℕ) (g : G)
    (features : Coordinate → ℕ) (coordinate : Coordinate),
    addCoordinateEncoding label encoding
        (actVector g features) (g • coordinate) =
      addCoordinateEncoding label encoding features coordinate

theorem labelInvariant_implies_coordinateEncodingFamilyEquivariant
    (label : Coordinate → Label)
    (invariant : LabelInvariant G label) :
    CoordinateEncodingFamilyEquivariant G label := by
  intro encoding g features coordinate
  simp [addCoordinateEncoding, actVector, invariant g coordinate]

theorem coordinateEncodingFamilyEquivariant_implies_labelInvariant
    [DecidableEq Label]
    (label : Coordinate → Label)
    (equivariant : CoordinateEncodingFamilyEquivariant G label) :
    LabelInvariant G label := by
  intro g coordinate
  by_contra labelChanged
  let encoding : Label → ℕ :=
    fun candidate =>
      if candidate = label (g • coordinate) then 1 else 0
  have reverse :
      label coordinate ≠ label (g • coordinate) :=
    Ne.symm labelChanged
  have equality :=
    equivariant encoding g (fun _ => 0) coordinate
  simp [addCoordinateEncoding, actVector, encoding, reverse]
    at equality

/-- Exact position-encoding boundary: every learned label encoding is
equivariant if and only if the coordinate action preserves the label. -/
theorem labelInvariant_iff_coordinateEncodingFamilyEquivariant
    [DecidableEq Label]
    (label : Coordinate → Label) :
    LabelInvariant G label ↔
      CoordinateEncodingFamilyEquivariant G label :=
  ⟨labelInvariant_implies_coordinateEncodingFamilyEquivariant label,
    coordinateEncodingFamilyEquivariant_implies_labelInvariant label⟩

end CoordinateEncodings

section TwoLayerWeightSpace

/-- Weight coordinates of a two-layer network.  The left summand indexes
incoming weights by `(hidden, input)`; the right summand indexes outgoing
weights by `(output, hidden)`. -/
abbrev TwoLayerWeightCoordinate
    (Input Hidden Output : Type*) :=
  (Hidden × Input) ⊕ (Output × Hidden)

/-- Independent neuron permutations at the input, hidden, and output
layers. -/
abbrev TwoLayerNeuronPermutation
    (Input Hidden Output : Type*) :=
  Equiv.Perm Input × Equiv.Perm Hidden × Equiv.Perm Output

/-- A genuine neuron permutation acts on both appearances of every neuron
coordinate.  In particular, the hidden permutation is shared by the incoming
row and outgoing column. -/
instance twoLayerWeightCoordinateMulAction
    (Input Hidden Output : Type*) :
    MulAction
      (TwoLayerNeuronPermutation Input Hidden Output)
      (TwoLayerWeightCoordinate Input Hidden Output) where
  smul permutation coordinate :=
    match coordinate with
    | Sum.inl (hidden, input) =>
        Sum.inl (permutation.2.1 hidden, permutation.1 input)
    | Sum.inr (output, hidden) =>
        Sum.inr (permutation.2.2 output, permutation.2.1 hidden)
  one_smul coordinate := by
    rcases coordinate with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;> rfl
  mul_smul first second coordinate := by
    rcases coordinate with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;> rfl

@[simp]
theorem twoLayerNeuronPermutation_smul_incoming
    {Input Hidden Output : Type*}
    (permutation : TwoLayerNeuronPermutation Input Hidden Output)
    (hidden : Hidden) (input : Input) :
    permutation •
        (Sum.inl (hidden, input) :
          TwoLayerWeightCoordinate Input Hidden Output) =
      Sum.inl (permutation.2.1 hidden, permutation.1 input) := by
  rfl

@[simp]
theorem twoLayerNeuronPermutation_smul_outgoing
    {Input Hidden Output : Type*}
    (permutation : TwoLayerNeuronPermutation Input Hidden Output)
    (output : Output) (hidden : Hidden) :
    permutation •
        (Sum.inr (output, hidden) :
          TwoLayerWeightCoordinate Input Hidden Output) =
      Sum.inr (permutation.2.2 output, permutation.2.1 hidden) := by
  rfl

/-- Incoming and outgoing weights are adjacent when they meet at the same
hidden neuron.  The relation is symmetric and excludes pairs within one
weight matrix. -/
def SharesHidden
    {Input Hidden Output : Type*} [DecidableEq Hidden] :
    TwoLayerWeightCoordinate Input Hidden Output →
      TwoLayerWeightCoordinate Input Hidden Output → Prop
  | Sum.inl (hidden, _), Sum.inr (_, hidden') => hidden = hidden'
  | Sum.inr (_, hidden), Sum.inl (hidden', _) => hidden = hidden'
  | _, _ => False

/-! The two grid relations below expose whether an incoming weight
permutation factors into one hidden-row permutation and one input-column
permutation. -/

/-- Two incoming weights lie in the same hidden row. -/
def SameIncomingRow
    {Input Hidden Output : Type*} [DecidableEq Hidden] :
    TwoLayerWeightCoordinate Input Hidden Output →
      TwoLayerWeightCoordinate Input Hidden Output → Prop
  | Sum.inl (hidden, _), Sum.inl (hidden', _) => hidden = hidden'
  | _, _ => False

instance sameIncomingRowDecidableRel
    {Input Hidden Output : Type*} [DecidableEq Hidden] :
    DecidableRel
      (SameIncomingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
  · exact decEq hidden hidden'
  · exact isFalse id
  · exact isFalse id
  · exact isFalse id

/-- Two incoming weights lie in the same input column. -/
def SameIncomingColumn
    {Input Hidden Output : Type*} [DecidableEq Input] :
    TwoLayerWeightCoordinate Input Hidden Output →
      TwoLayerWeightCoordinate Input Hidden Output → Prop
  | Sum.inl (_, input), Sum.inl (_, input') => input = input'
  | _, _ => False

instance sameIncomingColumnDecidableRel
    {Input Hidden Output : Type*} [DecidableEq Input] :
    DecidableRel
      (SameIncomingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
  · exact decEq input input'
  · exact isFalse id
  · exact isFalse id
  · exact isFalse id

/-- Two outgoing weights lie in the same output row. -/
def SameOutgoingRow
    {Input Hidden Output : Type*} [DecidableEq Output] :
    TwoLayerWeightCoordinate Input Hidden Output →
      TwoLayerWeightCoordinate Input Hidden Output → Prop
  | Sum.inr (output, _), Sum.inr (output', _) => output = output'
  | _, _ => False

instance sameOutgoingRowDecidableRel
    {Input Hidden Output : Type*} [DecidableEq Output] :
    DecidableRel
      (SameOutgoingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
  · exact isFalse id
  · exact isFalse id
  · exact isFalse id
  · exact decEq output output'

/-- Two outgoing weights lie in the same hidden column. -/
def SameOutgoingColumn
    {Input Hidden Output : Type*} [DecidableEq Hidden] :
    TwoLayerWeightCoordinate Input Hidden Output →
      TwoLayerWeightCoordinate Input Hidden Output → Prop
  | Sum.inr (_, hidden), Sum.inr (_, hidden') => hidden = hidden'
  | _, _ => False

instance sameOutgoingColumnDecidableRel
    {Input Hidden Output : Type*} [DecidableEq Hidden] :
    DecidableRel
      (SameOutgoingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
  · exact isFalse id
  · exact isFalse id
  · exact isFalse id
  · exact decEq hidden hidden'

/-- The two weight matrices have distinct layer labels. -/
inductive TwoLayerWeightLayer where
  | incoming
  | outgoing
  deriving DecidableEq

/-- Layer label of a two-layer weight coordinate. -/
def twoLayerWeightLayer
    {Input Hidden Output : Type*} :
    TwoLayerWeightCoordinate Input Hidden Output →
      TwoLayerWeightLayer
  | Sum.inl _ => TwoLayerWeightLayer.incoming
  | Sum.inr _ => TwoLayerWeightLayer.outgoing

/-! ## Exact layerwise structural classification -/

/-- Apply one coordinate permutation inside each weight matrix, without
moving weights across the layer boundary. -/
def layerwiseTwoLayerWeightPermutation
    {Input Hidden Output : Type*}
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) :
    Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output) :=
  Equiv.sumCongr incoming outgoing

/-- The incoming row chosen for a hidden neuron and the outgoing column
chosen for that same neuron must be transported by one shared permutation. -/
def PreservesTwoLayerHiddenIncidence
    {Input Hidden Output : Type*}
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) : Prop :=
  ∀ hidden input output hidden',
    (incoming (hidden, input)).1 =
        (outgoing (output, hidden')).2 ↔
      hidden = hidden'

/-- A pair of layerwise weight-coordinate permutations is induced by one
input, one shared hidden, and one output neuron permutation. -/
def IsTwoLayerNeuronProduct
    {Input Hidden Output : Type*}
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) : Prop :=
  ∃ inputPermutation : Equiv.Perm Input,
    ∃ hiddenPermutation : Equiv.Perm Hidden,
      ∃ outputPermutation : Equiv.Perm Output,
        (∀ hidden input,
          incoming (hidden, input) =
            (hiddenPermutation hidden, inputPermutation input)) ∧
        (∀ output hidden,
          outgoing (output, hidden) =
            (outputPermutation output, hiddenPermutation hidden))

theorem layerwise_preservesSharesHidden_iff
    {Input Hidden Output : Type*} [DecidableEq Hidden]
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) :
    EquivPreservesRelation
        (layerwiseTwoLayerWeightPermutation incoming outgoing)
        (SharesHidden
          (Input := Input) (Hidden := Hidden) (Output := Output)) ↔
      PreservesTwoLayerHiddenIncidence incoming outgoing := by
  constructor
  · intro preserves hidden input output hidden'
    simpa [layerwiseTwoLayerWeightPermutation, SharesHidden] using
      preserves
        (Sum.inl (hidden, input)) (Sum.inr (output, hidden'))
  · intro preserves left right
    rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
      rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
    · simp [layerwiseTwoLayerWeightPermutation, SharesHidden]
    · simpa [layerwiseTwoLayerWeightPermutation, SharesHidden] using
        preserves hidden input output' hidden'
    · simpa [layerwiseTwoLayerWeightPermutation, SharesHidden, eq_comm] using
        preserves hidden' input' output hidden
    · simp [layerwiseTwoLayerWeightPermutation, SharesHidden]

theorem layerwise_preservesSameIncomingRow_iff
    {Input Hidden Output : Type*} [DecidableEq Hidden]
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) :
    EquivPreservesRelation
        (layerwiseTwoLayerWeightPermutation incoming outgoing)
        (SameIncomingRow
          (Input := Input) (Hidden := Hidden) (Output := Output)) ↔
      EquivPreservesRelation incoming SameFirst := by
  constructor
  · intro preserves left right
    simpa
        [layerwiseTwoLayerWeightPermutation, SameIncomingRow, SameFirst]
      using preserves (Sum.inl left) (Sum.inl right)
  · intro preserves left right
    rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
      rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
    · simpa
          [layerwiseTwoLayerWeightPermutation, SameIncomingRow, SameFirst]
        using preserves (hidden, input) (hidden', input')
    · simp [layerwiseTwoLayerWeightPermutation, SameIncomingRow]
    · simp [layerwiseTwoLayerWeightPermutation, SameIncomingRow]
    · simp [layerwiseTwoLayerWeightPermutation, SameIncomingRow]

theorem layerwise_preservesSameIncomingColumn_iff
    {Input Hidden Output : Type*} [DecidableEq Input]
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) :
    EquivPreservesRelation
        (layerwiseTwoLayerWeightPermutation incoming outgoing)
        (SameIncomingColumn
          (Input := Input) (Hidden := Hidden) (Output := Output)) ↔
      EquivPreservesRelation incoming SameSecond := by
  constructor
  · intro preserves left right
    simpa
        [layerwiseTwoLayerWeightPermutation, SameIncomingColumn, SameSecond]
      using preserves (Sum.inl left) (Sum.inl right)
  · intro preserves left right
    rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
      rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
    · simpa
          [layerwiseTwoLayerWeightPermutation, SameIncomingColumn,
            SameSecond]
        using preserves (hidden, input) (hidden', input')
    · simp [layerwiseTwoLayerWeightPermutation, SameIncomingColumn]
    · simp [layerwiseTwoLayerWeightPermutation, SameIncomingColumn]
    · simp [layerwiseTwoLayerWeightPermutation, SameIncomingColumn]

theorem layerwise_preservesSameOutgoingRow_iff
    {Input Hidden Output : Type*} [DecidableEq Output]
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) :
    EquivPreservesRelation
        (layerwiseTwoLayerWeightPermutation incoming outgoing)
        (SameOutgoingRow
          (Input := Input) (Hidden := Hidden) (Output := Output)) ↔
      EquivPreservesRelation outgoing SameFirst := by
  constructor
  · intro preserves left right
    simpa
        [layerwiseTwoLayerWeightPermutation, SameOutgoingRow, SameFirst]
      using preserves (Sum.inr left) (Sum.inr right)
  · intro preserves left right
    rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
      rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
    · simp [layerwiseTwoLayerWeightPermutation, SameOutgoingRow]
    · simp [layerwiseTwoLayerWeightPermutation, SameOutgoingRow]
    · simp [layerwiseTwoLayerWeightPermutation, SameOutgoingRow]
    · simpa
          [layerwiseTwoLayerWeightPermutation, SameOutgoingRow, SameFirst]
        using preserves (output, hidden) (output', hidden')

theorem layerwise_preservesSameOutgoingColumn_iff
    {Input Hidden Output : Type*} [DecidableEq Hidden]
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) :
    EquivPreservesRelation
        (layerwiseTwoLayerWeightPermutation incoming outgoing)
        (SameOutgoingColumn
          (Input := Input) (Hidden := Hidden) (Output := Output)) ↔
      EquivPreservesRelation outgoing SameSecond := by
  constructor
  · intro preserves left right
    simpa
        [layerwiseTwoLayerWeightPermutation, SameOutgoingColumn, SameSecond]
      using preserves (Sum.inr left) (Sum.inr right)
  · intro preserves left right
    rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
      rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
    · simp [layerwiseTwoLayerWeightPermutation, SameOutgoingColumn]
    · simp [layerwiseTwoLayerWeightPermutation, SameOutgoingColumn]
    · simp [layerwiseTwoLayerWeightPermutation, SameOutgoingColumn]
    · simpa
          [layerwiseTwoLayerWeightPermutation, SameOutgoingColumn,
            SameSecond]
        using preserves (output, hidden) (output', hidden')

/-- Grid preservation in both matrices, together with shared-hidden
incidence, constructively recovers the three neuron permutations. -/
theorem structuredTwoLayerGrids_imply_neuronProduct
    {Input Hidden Output : Type*}
    (inputAnchor : Input) (hiddenAnchor : Hidden)
    (outputAnchor : Output)
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden))
    (incomingRows : EquivPreservesRelation incoming SameFirst)
    (incomingColumns : EquivPreservesRelation incoming SameSecond)
    (outgoingRows : EquivPreservesRelation outgoing SameFirst)
    (outgoingColumns : EquivPreservesRelation outgoing SameSecond)
    (hiddenIncidence :
      PreservesTwoLayerHiddenIncidence incoming outgoing) :
    IsTwoLayerNeuronProduct incoming outgoing := by
  obtain ⟨incomingHidden, inputPermutation, incomingForm⟩ :=
    preservesGridRelations_implies_isProductPermutation
      hiddenAnchor inputAnchor incoming incomingRows incomingColumns
  obtain ⟨outputPermutation, outgoingHidden, outgoingForm⟩ :=
    preservesGridRelations_implies_isProductPermutation
      outputAnchor hiddenAnchor outgoing outgoingRows outgoingColumns
  have hiddenPermutationsEqual : incomingHidden = outgoingHidden := by
    apply Equiv.ext
    intro hidden
    have coupled :=
      (hiddenIncidence
        hidden inputAnchor outputAnchor hidden).2 rfl
    simpa [incomingForm, outgoingForm] using coupled
  subst outgoingHidden
  exact
    ⟨inputPermutation, incomingHidden, outputPermutation,
      incomingForm, outgoingForm⟩

/-- Every genuine two-layer neuron product preserves the two matrix grids
and their coupled hidden incidence. -/
theorem neuronProduct_implies_structuredTwoLayerGrids
    {Input Hidden Output : Type*}
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden))
    (neuronProduct : IsTwoLayerNeuronProduct incoming outgoing) :
    EquivPreservesRelation incoming SameFirst ∧
      EquivPreservesRelation incoming SameSecond ∧
      EquivPreservesRelation outgoing SameFirst ∧
      EquivPreservesRelation outgoing SameSecond ∧
      PreservesTwoLayerHiddenIncidence incoming outgoing := by
  rcases neuronProduct with
    ⟨inputPermutation, hiddenPermutation, outputPermutation,
      incomingForm, outgoingForm⟩
  have incomingProduct : IsProductPermutation incoming :=
    ⟨hiddenPermutation, inputPermutation, incomingForm⟩
  have outgoingProduct : IsProductPermutation outgoing :=
    ⟨outputPermutation, hiddenPermutation, outgoingForm⟩
  have incomingPreserves :=
    isProductPermutation_implies_preservesGridRelations
      incoming incomingProduct
  have outgoingPreserves :=
    isProductPermutation_implies_preservesGridRelations
      outgoing outgoingProduct
  refine ⟨incomingPreserves.1, incomingPreserves.2,
    outgoingPreserves.1, outgoingPreserves.2, ?_⟩
  intro hidden input output hidden'
  rw [incomingForm, outgoingForm]
  simp

/-- Exact two-layer minimal-symmetry boundary for nonempty layer index
types.  All five structural incidences are preserved exactly by the genuine
neuron-product permutations. -/
theorem structuredTwoLayerGrids_iff_neuronProduct
    {Input Hidden Output : Type*}
    (inputAnchor : Input) (hiddenAnchor : Hidden)
    (outputAnchor : Output)
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) :
    (EquivPreservesRelation incoming SameFirst ∧
        EquivPreservesRelation incoming SameSecond ∧
        EquivPreservesRelation outgoing SameFirst ∧
        EquivPreservesRelation outgoing SameSecond ∧
        PreservesTwoLayerHiddenIncidence incoming outgoing) ↔
      IsTwoLayerNeuronProduct incoming outgoing := by
  constructor
  · intro structured
    exact
      structuredTwoLayerGrids_imply_neuronProduct
        inputAnchor hiddenAnchor outputAnchor incoming outgoing
        structured.1 structured.2.1 structured.2.2.1
        structured.2.2.2.1 structured.2.2.2.2
  · exact
      neuronProduct_implies_structuredTwoLayerGrids incoming outgoing

/-- Preservation of the five actual weight-coordinate relations used by the
two-layer construction. -/
def PreservesMinimalTwoLayerRelations
    {Input Hidden Output : Type*}
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) : Prop :=
  let layerwise :=
    layerwiseTwoLayerWeightPermutation incoming outgoing
  EquivPreservesRelation layerwise
      (SameIncomingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    EquivPreservesRelation layerwise
      (SameIncomingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    EquivPreservesRelation layerwise
      (SameOutgoingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    EquivPreservesRelation layerwise
      (SameOutgoingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    EquivPreservesRelation layerwise
      (SharesHidden
        (Input := Input) (Hidden := Hidden) (Output := Output))

/-- Crown theorem: among layer-preserving coordinate permutations, the five
minimal incidence relations characterize genuine neuron permutations
exactly. -/
theorem preservesMinimalTwoLayerRelations_iff_neuronProduct
    {Input Hidden Output : Type*}
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    (inputAnchor : Input) (hiddenAnchor : Hidden)
    (outputAnchor : Output)
    (incoming : Equiv.Perm (Hidden × Input))
    (outgoing : Equiv.Perm (Output × Hidden)) :
    PreservesMinimalTwoLayerRelations incoming outgoing ↔
      IsTwoLayerNeuronProduct incoming outgoing := by
  rw [PreservesMinimalTwoLayerRelations,
    layerwise_preservesSameIncomingRow_iff,
    layerwise_preservesSameIncomingColumn_iff,
    layerwise_preservesSameOutgoingRow_iff,
    layerwise_preservesSameOutgoingColumn_iff,
    layerwise_preservesSharesHidden_iff]
  exact
    structuredTwoLayerGrids_iff_neuronProduct
      inputAnchor hiddenAnchor outputAnchor incoming outgoing

/-! ## Complete arbitrary-coordinate classification -/

/-- The six structural observables on the complete two-layer weight
coordinate type: layer side, both grids, and shared-hidden incidence. -/
def PreservesCompleteTwoLayerStructure
    {Input Hidden Output : Type*}
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output)) : Prop :=
  PreservesSumSide permutation ∧
    EquivPreservesRelation permutation
      (SameIncomingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    EquivPreservesRelation permutation
      (SameIncomingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    EquivPreservesRelation permutation
      (SameOutgoingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    EquivPreservesRelation permutation
      (SameOutgoingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) ∧
    EquivPreservesRelation permutation
      (SharesHidden
        (Input := Input) (Hidden := Hidden) (Output := Output))

/-- A coordinate permutation is genuine when it comes from independent input
and output neuron relabelings and one hidden relabeling shared across adjacent
matrices. -/
def IsGenuineTwoLayerNeuronPermutation
    {Input Hidden Output : Type*}
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output)) : Prop :=
  ∃ inputPermutation : Equiv.Perm Input,
    ∃ hiddenPermutation : Equiv.Perm Hidden,
      ∃ outputPermutation : Equiv.Perm Output,
        permutation =
          layerwiseTwoLayerWeightPermutation
            (Equiv.prodCongr hiddenPermutation inputPermutation)
            (Equiv.prodCongr outputPermutation hiddenPermutation)

/-- Side preservation is the same whether the two sides are named
generically or as incoming and outgoing weight layers. -/
theorem preservesSumSide_iff_preservesTwoLayerWeightLayer
    {Input Hidden Output : Type*}
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output)) :
    PreservesSumSide permutation ↔
      ∀ coordinate,
        twoLayerWeightLayer (permutation coordinate) =
          twoLayerWeightLayer coordinate := by
  constructor <;> intro preserves coordinate
  · have sameSide := preserves coordinate
    rcases coordinate with incoming | outgoing <;>
      rcases imageEq : permutation _ with transportedIncoming |
        transportedOutgoing <;>
      simp [sumSide, twoLayerWeightLayer, imageEq] at sameSide ⊢
  · have sameLayer := preserves coordinate
    rcases coordinate with incoming | outgoing <;>
      rcases imageEq : permutation _ with transportedIncoming |
        transportedOutgoing <;>
      simp [sumSide, twoLayerWeightLayer, imageEq] at sameLayer ⊢

/-- Every arbitrary coordinate permutation preserving the six observables
is constructively a genuine neuron permutation. -/
theorem preservesCompleteTwoLayerStructure_implies_genuine
    {Input Hidden Output : Type*}
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    (inputAnchor : Input) (hiddenAnchor : Hidden)
    (outputAnchor : Output)
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output))
    (preserves : PreservesCompleteTwoLayerStructure permutation) :
    IsGenuineTwoLayerNeuronPermutation permutation := by
  obtain ⟨incoming, outgoing, sumForm⟩ :=
    preservesSumSide_implies_isSumPermutation
      permutation preserves.1
  have minimal :
      PreservesMinimalTwoLayerRelations incoming outgoing := by
    rw [PreservesMinimalTwoLayerRelations]
    simp only [layerwiseTwoLayerWeightPermutation]
    rw [← sumForm]
    exact preserves.2
  obtain
      ⟨inputPermutation, hiddenPermutation, outputPermutation,
        incomingForm, outgoingForm⟩ :=
    (preservesMinimalTwoLayerRelations_iff_neuronProduct
      inputAnchor hiddenAnchor outputAnchor incoming outgoing).1
      minimal
  refine
    ⟨inputPermutation, hiddenPermutation, outputPermutation, ?_⟩
  rw [sumForm]
  apply Equiv.ext
  intro coordinate
  rcases coordinate with ⟨hidden, input⟩ | ⟨output, hidden⟩
  · change Sum.inl (incoming (hidden, input)) = _
    rw [incomingForm]
    rfl
  · change Sum.inr (outgoing (output, hidden)) = _
    rw [outgoingForm]
    rfl

/-- Every genuine neuron permutation preserves the complete structural
signature. -/
theorem genuine_implies_preservesCompleteTwoLayerStructure
    {Input Hidden Output : Type*}
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    (inputAnchor : Input) (hiddenAnchor : Hidden)
    (outputAnchor : Output)
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output))
    (genuine : IsGenuineTwoLayerNeuronPermutation permutation) :
    PreservesCompleteTwoLayerStructure permutation := by
  rcases genuine with
    ⟨inputPermutation, hiddenPermutation, outputPermutation, rfl⟩
  let incoming :=
    Equiv.prodCongr hiddenPermutation inputPermutation
  let outgoing :=
    Equiv.prodCongr outputPermutation hiddenPermutation
  have minimal :
      PreservesMinimalTwoLayerRelations incoming outgoing :=
    (preservesMinimalTwoLayerRelations_iff_neuronProduct
      inputAnchor hiddenAnchor outputAnchor incoming outgoing).2
      ⟨inputPermutation, hiddenPermutation, outputPermutation,
        by intro hidden input; rfl,
        by intro output hidden; rfl⟩
  exact
    ⟨isSumPermutation_implies_preservesSumSide
        (layerwiseTwoLayerWeightPermutation incoming outgoing)
        ⟨incoming, outgoing, rfl⟩,
      minimal⟩

/-- Complete combinatorial minimal-equivariance crown: for nonempty layer
index types, the structural signature admits exactly the genuine neuron
permutation group and no larger coordinate-permutation group. -/
theorem preservesCompleteTwoLayerStructure_iff_genuine
    {Input Hidden Output : Type*}
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    (inputAnchor : Input) (hiddenAnchor : Hidden)
    (outputAnchor : Output)
    (permutation :
      Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output)) :
    PreservesCompleteTwoLayerStructure permutation ↔
      IsGenuineTwoLayerNeuronPermutation permutation :=
  ⟨preservesCompleteTwoLayerStructure_implies_genuine
      inputAnchor hiddenAnchor outputAnchor permutation,
    genuine_implies_preservesCompleteTwoLayerStructure
      inputAnchor hiddenAnchor outputAnchor permutation⟩

/-- The recovered coordinate equivalence is definitionally the existing
two-layer neuron action, not a parallel symmetry convention. -/
theorem genuineTwoLayerPermutation_eq_mulAction
    {Input Hidden Output : Type*}
    (inputPermutation : Equiv.Perm Input)
    (hiddenPermutation : Equiv.Perm Hidden)
    (outputPermutation : Equiv.Perm Output) :
    layerwiseTwoLayerWeightPermutation
        (Equiv.prodCongr hiddenPermutation inputPermutation)
        (Equiv.prodCongr outputPermutation hiddenPermutation) =
      MulAction.toPerm
        (inputPermutation, hiddenPermutation, outputPermutation) := by
  apply Equiv.ext
  intro coordinate
  rcases coordinate with
      ⟨hidden, input⟩ | ⟨output, hidden⟩ <;> rfl

instance sharesHiddenDecidableRel
    {Input Hidden Output : Type*} [DecidableEq Hidden] :
    DecidableRel
      (SharesHidden
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩
  · exact isFalse id
  · exact decEq hidden hidden'
  · exact decEq hidden hidden'
  · exact isFalse id

/-- Coupled neuron permutations preserve hidden adjacency. -/
theorem sharesHidden_relationInvariant
    {Input Hidden Output : Type*} [DecidableEq Hidden] :
    RelationInvariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (SharesHidden (Input := Input) (Hidden := Hidden)
        (Output := Output)) := by
  intro permutation left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩ <;>
    simp [SharesHidden]

/-- A genuine neuron permutation preserves incoming-row incidence. -/
theorem sameIncomingRow_relationInvariant
    {Input Hidden Output : Type*} [DecidableEq Hidden] :
    RelationInvariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (SameIncomingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro permutation left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩ <;>
    simp [SameIncomingRow]

/-- A genuine neuron permutation preserves incoming-column incidence. -/
theorem sameIncomingColumn_relationInvariant
    {Input Hidden Output : Type*} [DecidableEq Input] :
    RelationInvariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (SameIncomingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro permutation left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩ <;>
    simp [SameIncomingColumn]

/-- A genuine neuron permutation preserves outgoing-row incidence. -/
theorem sameOutgoingRow_relationInvariant
    {Input Hidden Output : Type*} [DecidableEq Output] :
    RelationInvariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (SameOutgoingRow
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro permutation left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩ <;>
    simp [SameOutgoingRow]

/-- A genuine neuron permutation preserves outgoing-column incidence. -/
theorem sameOutgoingColumn_relationInvariant
    {Input Hidden Output : Type*} [DecidableEq Hidden] :
    RelationInvariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (SameOutgoingColumn
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro permutation left right
  rcases left with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;>
    rcases right with ⟨hidden', input'⟩ | ⟨output', hidden'⟩ <;>
    simp [SameOutgoingColumn]

/-- Genuine neuron permutations never move a weight across matrices. -/
theorem twoLayerWeightLayer_labelInvariant
    {Input Hidden Output : Type*} :
    LabelInvariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (twoLayerWeightLayer
        (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro permutation coordinate
  rcases coordinate with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;> rfl

/-- Consequently every learned two-layer position encoding remains
equivariant under genuine neuron relabeling. -/
theorem twoLayerWeightLayer_encodingFamilyEquivariant
    {Input Hidden Output : Type*} :
    CoordinateEncodingFamilyEquivariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (twoLayerWeightLayer
        (Input := Input) (Hidden := Hidden) (Output := Output)) :=
  labelInvariant_implies_coordinateEncodingFamilyEquivariant _
    (twoLayerWeightLayer_labelInvariant
      (Input := Input) (Hidden := Hidden) (Output := Output))

/-- Incoming-row aggregation is equivariant under genuine neuron
relabeling. -/
theorem sameIncomingRowKernel_equivariant
    {Input Hidden Output R : Type*}
    [Fintype Input] [Fintype Hidden] [Fintype Output]
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    [Semiring R] :
    KernelEquivariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (relationKernel (R := R)
        (SameIncomingRow
          (Input := Input) (Hidden := Hidden) (Output := Output))) :=
  kernelInvariant_implies_kernelEquivariant
    (relationInvariant_implies_kernelInvariant _
      (sameIncomingRow_relationInvariant
        (Input := Input) (Hidden := Hidden) (Output := Output)))

/-- Incoming-column aggregation is equivariant under genuine neuron
relabeling. -/
theorem sameIncomingColumnKernel_equivariant
    {Input Hidden Output R : Type*}
    [Fintype Input] [Fintype Hidden] [Fintype Output]
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    [Semiring R] :
    KernelEquivariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (relationKernel (R := R)
        (SameIncomingColumn
          (Input := Input) (Hidden := Hidden) (Output := Output))) :=
  kernelInvariant_implies_kernelEquivariant
    (relationInvariant_implies_kernelInvariant _
      (sameIncomingColumn_relationInvariant
        (Input := Input) (Hidden := Hidden) (Output := Output)))

/-- Outgoing-row aggregation is equivariant under genuine neuron
relabeling. -/
theorem sameOutgoingRowKernel_equivariant
    {Input Hidden Output R : Type*}
    [Fintype Input] [Fintype Hidden] [Fintype Output]
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    [Semiring R] :
    KernelEquivariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (relationKernel (R := R)
        (SameOutgoingRow
          (Input := Input) (Hidden := Hidden) (Output := Output))) :=
  kernelInvariant_implies_kernelEquivariant
    (relationInvariant_implies_kernelInvariant _
      (sameOutgoingRow_relationInvariant
        (Input := Input) (Hidden := Hidden) (Output := Output)))

/-- Outgoing-column aggregation is equivariant under genuine neuron
relabeling. -/
theorem sameOutgoingColumnKernel_equivariant
    {Input Hidden Output R : Type*}
    [Fintype Input] [Fintype Hidden] [Fintype Output]
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    [Semiring R] :
    KernelEquivariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (relationKernel (R := R)
        (SameOutgoingColumn
          (Input := Input) (Hidden := Hidden) (Output := Output))) :=
  kernelInvariant_implies_kernelEquivariant
    (relationInvariant_implies_kernelInvariant _
      (sameOutgoingColumn_relationInvariant
        (Input := Input) (Hidden := Hidden) (Output := Output)))

/-- Therefore shared-hidden aggregation is equivariant under every genuine
two-layer neuron relabeling. -/
theorem sharesHiddenKernel_equivariant
    {Input Hidden Output R : Type*}
    [Fintype Input] [Fintype Hidden] [Fintype Output]
    [DecidableEq Input] [DecidableEq Hidden] [DecidableEq Output]
    [Semiring R] :
    KernelEquivariant
      (TwoLayerNeuronPermutation Input Hidden Output)
      (relationKernel (R := R)
        (SharesHidden (Input := Input) (Hidden := Hidden)
          (Output := Output))) :=
  kernelInvariant_implies_kernelEquivariant
    (relationInvariant_implies_kernelInvariant _
      (sharesHidden_relationInvariant
        (Input := Input) (Hidden := Hidden) (Output := Output)))

/-- Permute only incoming hidden rows while leaving outgoing hidden columns
fixed.  This is a coordinate bijection, but generally not a genuine neuron
permutation. -/
def incomingOnlyPermutation
    {Input Hidden Output : Type*}
    (permutation : Equiv.Perm Hidden) :
    Equiv.Perm (TwoLayerWeightCoordinate Input Hidden Output) where
  toFun coordinate :=
    match coordinate with
    | Sum.inl (hidden, input) =>
        Sum.inl (permutation hidden, input)
    | Sum.inr (output, hidden) =>
        Sum.inr (output, hidden)
  invFun coordinate :=
    match coordinate with
    | Sum.inl (hidden, input) =>
        Sum.inl (permutation.symm hidden, input)
    | Sum.inr (output, hidden) =>
        Sum.inr (output, hidden)
  left_inv coordinate := by
    rcases coordinate with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;> simp
  right_inv coordinate := by
    rcases coordinate with ⟨hidden, input⟩ | ⟨output, hidden⟩ <;> simp

namespace Fixtures

abbrev TinyWeightCoordinate :=
  TwoLayerWeightCoordinate (Fin 1) (Fin 2) (Fin 1)

def hiddenSwap : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

def falseIncomingSwap : Equiv.Perm TinyWeightCoordinate :=
  incomingOnlyPermutation hiddenSwap

def incomingZero : TinyWeightCoordinate :=
  Sum.inl (0, 0)

def outgoingZero : TinyWeightCoordinate :=
  Sum.inr (0, 0)

/-- A false permutation that exchanges coordinates across weight matrices. -/
def crossLayerSwap : Equiv.Perm TinyWeightCoordinate :=
  Equiv.swap incomingZero outgoingZero

/-- A concrete learned layer code that distinguishes the two matrices. -/
def binaryLayerEncoding : TwoLayerWeightLayer → ℕ
  | TwoLayerWeightLayer.incoming => 0
  | TwoLayerWeightLayer.outgoing => 1

abbrev GridWeightCoordinate :=
  TwoLayerWeightCoordinate (Fin 2) (Fin 2) (Fin 1)

def gridIncoming00 : GridWeightCoordinate :=
  Sum.inl (0, 0)

def gridIncoming01 : GridWeightCoordinate :=
  Sum.inl (0, 1)

def gridIncoming10 : GridWeightCoordinate :=
  Sum.inl (1, 0)

/-- Swap one entry between hidden rows while leaving the other input column
fixed.  The induced row permutation therefore depends on the column. -/
def columnDependentRowSwap : Equiv.Perm GridWeightCoordinate :=
  Equiv.swap gridIncoming00 gridIncoming10

/-- Swap one entry between input columns while leaving the other hidden row
fixed.  The induced column permutation therefore depends on the row. -/
def rowDependentColumnSwap : Equiv.Perm GridWeightCoordinate :=
  Equiv.swap gridIncoming00 gridIncoming01

/-- The selected incoming and outgoing coordinates initially share hidden
neuron zero. -/
theorem original_pair_shares_hidden :
    SharesHidden incomingZero outgoingZero := by
  rfl

/-- The incoming-only swap disconnects that pair. -/
theorem false_swap_breaks_selected_pair :
    ¬ SharesHidden
      (falseIncomingSwap • incomingZero)
      (falseIncomingSwap • outgoingZero) := by
  norm_num
    [SharesHidden, falseIncomingSwap, incomingOnlyPermutation,
      hiddenSwap, incomingZero, outgoingZero, Equiv.smul_def,
      Equiv.swap_apply_def]

/-- The incoming-only coordinate swap is not a symmetry of hidden
adjacency. -/
theorem falseIncomingSwap_not_relationInvariant :
    ¬ RelationInvariant
      (Equiv.Perm TinyWeightCoordinate)
      (SharesHidden
        (Input := Fin 1) (Hidden := Fin 2) (Output := Fin 1)) := by
  intro invariant
  exact false_swap_breaks_selected_pair
    ((invariant falseIncomingSwap incomingZero outgoingZero).2
      original_pair_shares_hidden)

/-- A cross-layer permutation changes the learned layer code on the selected
coordinate. -/
theorem crossLayerSwap_changes_label :
    twoLayerWeightLayer (crossLayerSwap • incomingZero) ≠
      twoLayerWeightLayer incomingZero := by
  simp
    [twoLayerWeightLayer, crossLayerSwap, incomingZero, outgoingZero]

/-- Executable position-encoding witness: transporting a zero feature through
the cross-layer swap changes its encoded value from zero to one. -/
theorem crossLayerSwap_breaks_layerEncoding :
    addCoordinateEncoding twoLayerWeightLayer binaryLayerEncoding
        (actVector crossLayerSwap (fun _ : TinyWeightCoordinate => 0))
        (crossLayerSwap • incomingZero) = 1 ∧
      addCoordinateEncoding twoLayerWeightLayer binaryLayerEncoding
        (fun _ : TinyWeightCoordinate => 0) incomingZero = 0 := by
  norm_num
    [addCoordinateEncoding, actVector, twoLayerWeightLayer,
      binaryLayerEncoding, crossLayerSwap, incomingZero, outgoingZero,
      Equiv.smul_def, Equiv.swap_apply_def]

/-- Therefore the complete family of learned layer encodings is not
equivariant under arbitrary weight-coordinate permutations. -/
theorem layerEncodingFamily_not_arbitraryPermutationEquivariant :
    ¬ CoordinateEncodingFamilyEquivariant
      (Equiv.Perm TinyWeightCoordinate)
      (twoLayerWeightLayer
        (Input := Fin 1) (Hidden := Fin 2) (Output := Fin 1)) := by
  intro equivariant
  have invariant :=
    (labelInvariant_iff_coordinateEncodingFamilyEquivariant
      (G := Equiv.Perm TinyWeightCoordinate)
      (twoLayerWeightLayer
        (Input := Fin 1) (Hidden := Fin 2) (Output := Fin 1))).2
      equivariant
  exact crossLayerSwap_changes_label
    (invariant crossLayerSwap incomingZero)

/-- The column-dependent row swap breaks a pair that originally occupied one
hidden row. -/
theorem columnDependentRowSwap_breaks_sameRow :
    SameIncomingRow gridIncoming00 gridIncoming01 ∧
      ¬ SameIncomingRow
        (columnDependentRowSwap • gridIncoming00)
        (columnDependentRowSwap • gridIncoming01) := by
  norm_num
    [SameIncomingRow, columnDependentRowSwap, gridIncoming00,
      gridIncoming01, gridIncoming10, Equiv.smul_def,
      Equiv.swap_apply_def]

/-- The row-dependent column swap breaks a pair that originally occupied one
input column. -/
theorem rowDependentColumnSwap_breaks_sameColumn :
    SameIncomingColumn gridIncoming00 gridIncoming10 ∧
      ¬ SameIncomingColumn
        (rowDependentColumnSwap • gridIncoming00)
        (rowDependentColumnSwap • gridIncoming10) := by
  norm_num
    [SameIncomingColumn, rowDependentColumnSwap, gridIncoming00,
      gridIncoming01, gridIncoming10, Equiv.smul_def,
      Equiv.swap_apply_def]

/-- Executable grid witnesses: each partial coordinate swap changes its
corresponding relation-kernel readout from one to zero. -/
theorem dependentGridSwaps_break_relationKernels :
    kernelApply
        (relationKernel (R := ℕ)
          (SameIncomingRow
            (Input := Fin 2) (Hidden := Fin 2) (Output := Fin 1)))
        (basisVector gridIncoming00) gridIncoming01 = 1 ∧
      kernelApply
        (relationKernel (R := ℕ)
          (SameIncomingRow
            (Input := Fin 2) (Hidden := Fin 2) (Output := Fin 1)))
        (actVector columnDependentRowSwap
          (basisVector gridIncoming00))
        (columnDependentRowSwap • gridIncoming01) = 0 ∧
      kernelApply
        (relationKernel (R := ℕ)
          (SameIncomingColumn
            (Input := Fin 2) (Hidden := Fin 2) (Output := Fin 1)))
        (basisVector gridIncoming00) gridIncoming10 = 1 ∧
      kernelApply
        (relationKernel (R := ℕ)
          (SameIncomingColumn
            (Input := Fin 2) (Hidden := Fin 2) (Output := Fin 1)))
        (actVector rowDependentColumnSwap
          (basisVector gridIncoming00))
        (rowDependentColumnSwap • gridIncoming10) = 0 := by
  repeat' constructor

/-- Same-row aggregation rejects arbitrary coordinate permutations. -/
theorem sameIncomingRowKernel_not_arbitraryPermutationEquivariant :
    ¬ KernelEquivariant
      (Equiv.Perm GridWeightCoordinate)
      (relationKernel (R := ℕ)
        (SameIncomingRow
          (Input := Fin 2) (Hidden := Fin 2) (Output := Fin 1))) := by
  intro equivariant
  have invariant :=
    (relationInvariant_iff_relationKernel_equivariant
      (G := Equiv.Perm GridWeightCoordinate)
      (R := ℕ)
      (SameIncomingRow
        (Input := Fin 2) (Hidden := Fin 2) (Output := Fin 1))).2
      equivariant
  exact columnDependentRowSwap_breaks_sameRow.2
    ((invariant columnDependentRowSwap gridIncoming00 gridIncoming01).2
      columnDependentRowSwap_breaks_sameRow.1)

/-- Same-column aggregation rejects arbitrary coordinate permutations. -/
theorem sameIncomingColumnKernel_not_arbitraryPermutationEquivariant :
    ¬ KernelEquivariant
      (Equiv.Perm GridWeightCoordinate)
      (relationKernel (R := ℕ)
        (SameIncomingColumn
          (Input := Fin 2) (Hidden := Fin 2) (Output := Fin 1))) := by
  intro equivariant
  have invariant :=
    (relationInvariant_iff_relationKernel_equivariant
      (G := Equiv.Perm GridWeightCoordinate)
      (R := ℕ)
      (SameIncomingColumn
        (Input := Fin 2) (Hidden := Fin 2) (Output := Fin 1))).2
      equivariant
  exact rowDependentColumnSwap_breaks_sameColumn.2
    ((invariant rowDependentColumnSwap gridIncoming00 gridIncoming10).2
      rowDependentColumnSwap_breaks_sameColumn.1)

/-- Executable operator witness: before the false swap, the relation kernel
maps the selected basis coordinate to one at the adjacent output; after
transport, it maps it to zero. -/
theorem falseIncomingSwap_kernel :
    kernelApply
        (relationKernel (R := ℕ)
          (SharesHidden
            (Input := Fin 1) (Hidden := Fin 2) (Output := Fin 1)))
        (basisVector incomingZero) outgoingZero = 1 ∧
      kernelApply
        (relationKernel (R := ℕ)
          (SharesHidden
            (Input := Fin 1) (Hidden := Fin 2) (Output := Fin 1)))
        (actVector falseIncomingSwap (basisVector incomingZero))
        (falseIncomingSwap • outgoingZero) = 0 := by
  constructor
  · rw [kernelApply_basisVector]
    simp [relationKernel, SharesHidden, outgoingZero, incomingZero]
  · rw [actVector_basisVector, kernelApply_basisVector]
    norm_num
      [relationKernel, SharesHidden, falseIncomingSwap,
        incomingOnlyPermutation, hiddenSwap, outgoingZero, incomingZero,
        Equiv.smul_def, Equiv.swap_apply_def]

/-- Hence the structured kernel is not equivariant under arbitrary weight
coordinate permutations, even though it is equivariant under genuine neuron
permutations. -/
theorem sharesHiddenKernel_not_arbitraryPermutationEquivariant :
    ¬ KernelEquivariant
      (Equiv.Perm TinyWeightCoordinate)
      (relationKernel (R := ℕ)
        (SharesHidden
          (Input := Fin 1) (Hidden := Fin 2) (Output := Fin 1))) := by
  intro equivariant
  exact falseIncomingSwap_not_relationInvariant
    ((relationInvariant_iff_relationKernel_equivariant
      (G := Equiv.Perm TinyWeightCoordinate)
      (R := ℕ)
      (SharesHidden
        (Input := Fin 1) (Hidden := Fin 2) (Output := Fin 1))).2
      equivariant)

end Fixtures

#print axioms relationInvariant_iff_relationKernel_equivariant
#print axioms labelInvariant_iff_coordinateEncodingFamilyEquivariant
#print axioms structuredTwoLayerGrids_iff_neuronProduct
#print axioms preservesMinimalTwoLayerRelations_iff_neuronProduct
#print axioms preservesCompleteTwoLayerStructure_iff_genuine
#print axioms genuineTwoLayerPermutation_eq_mulAction
#print axioms sharesHiddenKernel_equivariant
#print axioms twoLayerWeightLayer_encodingFamilyEquivariant
#print axioms sameIncomingRowKernel_equivariant
#print axioms sameIncomingColumnKernel_equivariant
#print axioms sameOutgoingRowKernel_equivariant
#print axioms sameOutgoingColumnKernel_equivariant
#print axioms Fixtures.crossLayerSwap_breaks_layerEncoding
#print axioms Fixtures.layerEncodingFamily_not_arbitraryPermutationEquivariant
#print axioms Fixtures.dependentGridSwaps_break_relationKernels
#print axioms Fixtures.sameIncomingRowKernel_not_arbitraryPermutationEquivariant
#print axioms Fixtures.sameIncomingColumnKernel_not_arbitraryPermutationEquivariant
#print axioms Fixtures.falseIncomingSwap_kernel
#print axioms Fixtures.sharesHiddenKernel_not_arbitraryPermutationEquivariant

end TwoLayerWeightSpace

end

end Mettapedia.MachineLearning.NeuralNetworks
