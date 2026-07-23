import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.RowIndexedRotary
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.TypedRelationGraph

/-!
# Equivariance of the relation-aware encoder block

This module lifts pairwise score compatibility through the operations used by
the graph encoder: target masking, row softmax, value aggregation, multi-head
assembly, rowwise maps, residual additions, and final inactive-row zeroing.

Evaluation mode is deterministic.  During training, attention and feed-forward
dropout are equivariant only when their realized multipliers are transported
with the node relabeling; a finite counterexample records this boundary.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open scoped BigOperators

universe uLeft uRight uValue uHead

/-! ## Transport laws -/

/-- Transport node-indexed rows across an equivalence of node types. -/
def transportRows {Left : Type uLeft} {Right : Type uRight}
    {Value : Type uValue} (relabel : Left ≃ Right)
    (rows : Left → Value) : Right → Value :=
  fun node => rows (relabel.symm node)

/-- Transport a pair-indexed quantity across an equivalence of node types. -/
def transportPairs {Left : Type uLeft} {Right : Type uRight}
    {Value : Type uValue} (relabel : Left ≃ Right)
    (pairs : Left → Left → Value) : Right → Right → Value :=
  fun source target => pairs (relabel.symm source) (relabel.symm target)

@[simp] theorem transportRows_apply
    {Left : Type uLeft} {Right : Type uRight} {Value : Type uValue}
    (relabel : Left ≃ Right) (rows : Left → Value) (node : Left) :
    transportRows relabel rows (relabel node) = rows node := by
  simp [transportRows]

@[simp] theorem transportPairs_apply
    {Left : Type uLeft} {Right : Type uRight} {Value : Type uValue}
    (relabel : Left ≃ Right) (pairs : Left → Left → Value)
    (source target : Left) :
    transportPairs relabel pairs (relabel source) (relabel target) =
      pairs source target := by
  simp [transportPairs]

/-- Two nodewise maps are the same computation after relabeling. -/
def PointwiseCompatible {Left : Type uLeft} {Right : Type uRight}
    {Input Output : Type*} (relabel : Left ≃ Right)
    (left : Left → Input → Output) (right : Right → Input → Output) : Prop :=
  ∀ node value, right (relabel node) value = left node value

/-- Two global node-indexed layers commute with the relabeling. -/
def LayerCompatible {Left : Type uLeft} {Right : Type uRight}
    {Value : Type uValue} (relabel : Left ≃ Right)
    (left : (Left → Value) → Left → Value)
    (right : (Right → Value) → Right → Value) : Prop :=
  ∀ rows node,
    right (transportRows relabel rows) (relabel node) = left rows node

/-- Applying compatible rowwise maps commutes with row transport. -/
theorem pointwise_transport
    {Left : Type uLeft} {Right : Type uRight}
    {Input Output : Type*} (relabel : Left ≃ Right)
    (left : Left → Input → Output) (right : Right → Input → Output)
    (compatible : PointwiseCompatible relabel left right)
    (rows : Left → Input) (node : Left) :
    right (relabel node) (transportRows relabel rows (relabel node)) =
      left node (rows node) := by
  simpa using compatible node (rows node)

/-! ## Masked row softmax and value aggregation -/

/-- The finite score kernel after applying the encoder's target-column mask. -/
noncomputable def maskedExpKernel {Node : Type*}
    (active : Node → Bool) (score : Node → Node → ℝ)
    (source target : Node) : ℝ :=
  if active target then Real.exp (score source target) else 0

/-- The denominator of one masked attention row. -/
noncomputable def maskedNormalizer {Node : Type*} [Fintype Node]
    (active : Node → Bool) (score : Node → Node → ℝ)
    (source : Node) : ℝ :=
  ∑ target, maskedExpKernel active score source target

/-- Exact finite masked-softmax weight.  A caller claiming probabilistic
normalization must separately provide a nonempty active-key premise. -/
noncomputable def maskedSoftmaxWeight {Node : Type*} [Fintype Node]
    (active : Node → Bool) (score : Node → Node → ℝ)
    (source target : Node) : ℝ :=
  maskedExpKernel active score source target /
    maskedNormalizer active score source

theorem maskedExpKernel_nonnegative {Node : Type*}
    (active : Node → Bool) (score : Node → Node → ℝ)
    (source target : Node) :
    0 ≤ maskedExpKernel active score source target := by
  by_cases enabled : active target
  · simp [maskedExpKernel, enabled, (Real.exp_pos _).le]
  · simp [maskedExpKernel, enabled]

/-- One active key makes the finite softmax denominator strictly positive. -/
theorem maskedNormalizer_positive {Node : Type*} [Fintype Node]
    (active : Node → Bool) (score : Node → Node → ℝ)
    (source : Node) (nonempty : ∃ target, active target = true) :
    0 < maskedNormalizer active score source := by
  obtain ⟨target, targetActive⟩ := nonempty
  unfold maskedNormalizer
  apply Finset.sum_pos'
  · intro candidate _
    exact maskedExpKernel_nonnegative active score source candidate
  · exact ⟨target, Finset.mem_univ target, by
      simp [maskedExpKernel, targetActive, Real.exp_pos]⟩

/-- With at least one active key, the exact finite softmax row sums to one. -/
theorem maskedSoftmaxWeight_sum_one {Node : Type*} [Fintype Node]
    (active : Node → Bool) (score : Node → Node → ℝ)
    (source : Node) (nonempty : ∃ target, active target = true) :
    ∑ target, maskedSoftmaxWeight active score source target = 1 := by
  have denominatorNonzero : maskedNormalizer active score source ≠ 0 :=
    ne_of_gt (maskedNormalizer_positive active score source nonempty)
  change (∑ target, maskedExpKernel active score source target /
    maskedNormalizer active score source) = 1
  rw [← Finset.sum_div]
  exact div_self denominatorNonzero

/-- An inactive key receives exactly zero attention weight. -/
theorem maskedSoftmaxWeight_inactive {Node : Type*} [Fintype Node]
    (active : Node → Bool) (score : Node → Node → ℝ)
    (source target : Node) (inactive : active target = false) :
    maskedSoftmaxWeight active score source target = 0 := by
  simp [maskedSoftmaxWeight, maskedExpKernel, inactive]

/-- Attention aggregation after softmax.  `multiplier` is one in evaluation
mode; in training it represents the realized attention-dropout multiplier. -/
noncomputable def attentionRead {Node : Type*} [Fintype Node]
    {Value : Type uValue} [AddCommMonoid Value] [Module ℝ Value]
    (active : Node → Bool) (score : Node → Node → ℝ)
    (multiplier : Node → Node → ℝ) (value : Node → Value)
    (source : Node) : Value :=
  ∑ target,
    (maskedSoftmaxWeight active score source target *
      multiplier source target) • value target

theorem maskedExpKernel_transport
    {Left : Type uLeft} {Right : Type uRight}
    (relabel : Left ≃ Right)
    (active : Left → Bool) (score : Left → Left → ℝ)
    (source target : Left) :
    maskedExpKernel (transportRows relabel active)
        (transportPairs relabel score) (relabel source) (relabel target) =
      maskedExpKernel active score source target := by
  simp [maskedExpKernel]

theorem maskedNormalizer_transport
    {Left : Type uLeft} {Right : Type uRight}
    [Fintype Left] [Fintype Right]
    (relabel : Left ≃ Right)
    (active : Left → Bool) (score : Left → Left → ℝ)
    (source : Left) :
    maskedNormalizer (transportRows relabel active)
        (transportPairs relabel score) (relabel source) =
      maskedNormalizer active score source := by
  unfold maskedNormalizer
  symm
  apply Fintype.sum_equiv relabel
  intro target
  exact (maskedExpKernel_transport relabel active score source target).symm

theorem maskedSoftmaxWeight_transport
    {Left : Type uLeft} {Right : Type uRight}
    [Fintype Left] [Fintype Right]
    (relabel : Left ≃ Right)
    (active : Left → Bool) (score : Left → Left → ℝ)
    (source target : Left) :
    maskedSoftmaxWeight (transportRows relabel active)
        (transportPairs relabel score) (relabel source) (relabel target) =
      maskedSoftmaxWeight active score source target := by
  rw [maskedSoftmaxWeight, maskedSoftmaxWeight,
    maskedExpKernel_transport, maskedNormalizer_transport]

/-- Masking, softmax, dropout multiplication, and value aggregation preserve
relabeling exactly when the realized stochastic multiplier is transported. -/
theorem attentionRead_transport
    {Left : Type uLeft} {Right : Type uRight}
    [Fintype Left] [Fintype Right]
    {Value : Type uValue} [AddCommMonoid Value] [Module ℝ Value]
    (relabel : Left ≃ Right)
    (active : Left → Bool) (score : Left → Left → ℝ)
    (multiplier : Left → Left → ℝ) (value : Left → Value)
    (source : Left) :
    attentionRead (transportRows relabel active)
        (transportPairs relabel score) (transportPairs relabel multiplier)
        (transportRows relabel value) (relabel source) =
      attentionRead active score multiplier value source := by
  unfold attentionRead
  symm
  apply Fintype.sum_equiv relabel
  intro target
  rw [maskedSoftmaxWeight_transport]
  simp

/-! ## Relation-aware scores -/

/-- The learned scalar contributed by one optional typed edge for one head. -/
def relationBias {Role : Type*} {Head : Type uHead}
    (embedding : Role → Head → ℝ) (role : Option Role) (head : Head) : ℝ :=
  match role with
  | none => 0
  | some edgeRole => embedding edgeRole head

/-- Content score plus the exact per-head typed-relation bias. -/
def relationAwareHeadScore {Node Role : Type*} {Head : Type uHead}
    (rawScore : Head → Node → Node → ℝ)
    (role : Node → Node → Option Role)
    (embedding : Role → Head → ℝ)
    (head : Head) (source target : Node) : ℝ :=
  rawScore head source target + relationBias embedding (role source target) head

theorem relationAwareHeadScore_transport
    {Left : Type uLeft} {Right : Type uRight}
    {Role : Type*} {Head : Type uHead}
    (relabel : Left ≃ Right)
    (rawScore : Head → Left → Left → ℝ)
    (role : Left → Left → Option Role)
    (embedding : Role → Head → ℝ)
    (head : Head) (source target : Left) :
    relationAwareHeadScore
        (fun h => transportPairs relabel (rawScore h))
        (transportPairs relabel role) embedding head
        (relabel source) (relabel target) =
      relationAwareHeadScore rawScore role embedding head source target := by
  simp [relationAwareHeadScore]

/-- A score-producing layer commutes with a node relabeling. -/
def ScoreLayerCompatible
    {Left : Type uLeft} {Right : Type uRight}
    {Model : Type uValue} {Head : Type uHead}
    (relabel : Left ≃ Right)
    (left : (Left → Model) → Head → Left → Left → ℝ)
    (right : (Right → Model) → Head → Right → Right → ℝ) : Prop :=
  ∀ rows head source target,
    right (transportRows relabel rows) head
        (relabel source) (relabel target) =
      left rows head source target

/-! ## Typed-graph score bridge -/

/-- Query-key score whose positional action is indexed by the serialized graph
row.  The pairing may include the executable `1 / sqrt(headDim)` scale. -/
def graphPositionalScore
    {Node NodeKind Feature Role Vector : Type*}
    (graph : TypedRelationGraph Node NodeKind Feature Role)
    (positionAction : Nat → Vector → Vector)
    (pairing : Vector → Vector → ℝ)
    (query key : Node → Vector) (source target : Node) : ℝ :=
  pairing (positionAction (graph.ropeIndex source) (query source))
    (positionAction (graph.ropeIndex target) (key target))

/-- The exact graph-dependent score shape: scaled positional content match
plus one learned scalar for the last written optional relation role. -/
def graphRelationAwareScore
    {Node NodeKind Feature Role Vector : Type*} {Head : Type uHead}
    (graph : TypedRelationGraph Node NodeKind Feature Role)
    (positionAction : Nat → Vector → Vector)
    (pairing : Vector → Vector → ℝ)
    (embedding : Role → Head → ℝ)
    (query key : Node → Vector) (head : Head)
    (source target : Node) : ℝ :=
  graphPositionalScore graph positionAction pairing query key source target +
    relationBias embedding (graph.lastRole? source target) head

/-- A position-preserving typed-graph isomorphism preserves the complete raw
relation-aware score after transporting query and key rows. -/
theorem graphRelationAwareScore_isomorphism
    {LeftNode : Type uLeft} {RightNode : Type uRight}
    {NodeKind Feature Role Vector : Type*} {Head : Type uHead}
    {left : TypedRelationGraph LeftNode NodeKind Feature Role}
    {right : TypedRelationGraph RightNode NodeKind Feature Role}
    (isomorphism : left.PositionPreservingIsomorphism right)
    (leftFunctional : left.relationFunctional)
    (rightFunctional : right.relationFunctional)
    (positionAction : Nat → Vector → Vector)
    (pairing : Vector → Vector → ℝ)
    (embedding : Role → Head → ℝ)
    (query key : LeftNode → Vector) (head : Head)
    (source target : LeftNode) :
    graphRelationAwareScore right positionAction pairing embedding
        (transportRows isomorphism.node query)
        (transportRows isomorphism.node key) head
        (isomorphism.node source) (isomorphism.node target) =
      graphRelationAwareScore left positionAction pairing embedding
        query key head source target := by
  unfold graphRelationAwareScore graphPositionalScore
  rw [isomorphism.ropeIndex_preserved source,
    isomorphism.ropeIndex_preserved target]
  rw [isomorphism.toIsomorphism.lastRole_preserved
    leftFunctional rightFunctional source target]
  simp [transportRows]

/-- Build every head's score from shared query/key projections, row-indexed
position, and typed relation bias. -/
def graphAttentionScore
    {Node NodeKind Feature Role Model Vector : Type*} {Head : Type uHead}
    (graph : TypedRelationGraph Node NodeKind Feature Role)
    (positionAction : Nat → Vector → Vector)
    (pairing : Vector → Vector → ℝ)
    (embedding : Role → Head → ℝ)
    (queryProjection keyProjection : Head → Model → Vector)
    (rows : Node → Model) (head : Head) (source target : Node) : ℝ :=
  graphRelationAwareScore graph positionAction pairing embedding
    (fun node => queryProjection head (rows node))
    (fun node => keyProjection head (rows node))
    head source target

/-- The typed-graph boundary discharges the score-compatibility premise used
by the complete self-attention equivariance theorem. -/
theorem graphAttentionScore_compatible
    {LeftNode : Type uLeft} {RightNode : Type uRight}
    {NodeKind Feature Role Model Vector : Type*} {Head : Type uHead}
    {left : TypedRelationGraph LeftNode NodeKind Feature Role}
    {right : TypedRelationGraph RightNode NodeKind Feature Role}
    (isomorphism : left.PositionPreservingIsomorphism right)
    (leftFunctional : left.relationFunctional)
    (rightFunctional : right.relationFunctional)
    (positionAction : Nat → Vector → Vector)
    (pairing : Vector → Vector → ℝ)
    (embedding : Role → Head → ℝ)
    (queryProjection keyProjection : Head → Model → Vector) :
    ScoreLayerCompatible isomorphism.node
      (graphAttentionScore left positionAction pairing embedding
        queryProjection keyProjection)
      (graphAttentionScore right positionAction pairing embedding
        queryProjection keyProjection) := by
  intro rows head source target
  unfold graphAttentionScore
  have queryEq :
      (fun node : RightNode =>
        queryProjection head (transportRows isomorphism.node rows node)) =
        transportRows isomorphism.node
          (fun node : LeftNode => queryProjection head (rows node)) := by
    funext node
    simp [transportRows]
  have keyEq :
      (fun node : RightNode =>
        keyProjection head (transportRows isomorphism.node rows node)) =
        transportRows isomorphism.node
          (fun node : LeftNode => keyProjection head (rows node)) := by
    funext node
    simp [transportRows]
  rw [queryEq, keyEq]
  exact graphRelationAwareScore_isomorphism isomorphism leftFunctional
    rightFunctional positionAction pairing embedding
    (fun node => queryProjection head (rows node))
    (fun node => keyProjection head (rows node))
    head source target

/-! ## Multi-head assembly -/

/-- Independent attention reads for every head. -/
noncomputable def multiHeadRead {Node : Type*} [Fintype Node]
    {Head : Type uHead} {Value : Type uValue}
    [AddCommMonoid Value] [Module ℝ Value]
    (active : Node → Bool) (score : Head → Node → Node → ℝ)
    (multiplier : Head → Node → Node → ℝ)
    (value : Head → Node → Value) (source : Node) (head : Head) : Value :=
  attentionRead active (score head) (multiplier head) (value head) source

theorem multiHeadRead_transport
    {Left : Type uLeft} {Right : Type uRight}
    [Fintype Left] [Fintype Right]
    {Head : Type uHead} {Value : Type uValue}
    [AddCommMonoid Value] [Module ℝ Value]
    (relabel : Left ≃ Right)
    (active : Left → Bool) (score : Head → Left → Left → ℝ)
    (multiplier : Head → Left → Left → ℝ)
    (value : Head → Left → Value) (source : Left) (head : Head) :
    multiHeadRead (transportRows relabel active)
        (fun h => transportPairs relabel (score h))
        (fun h => transportPairs relabel (multiplier h))
        (fun h => transportRows relabel (value h))
        (relabel source) head =
      multiHeadRead active score multiplier value source head := by
  exact attentionRead_transport relabel active (score head)
    (multiplier head) (value head) source

/-! ## A complete self-attention layer -/

/-- Multi-head self-attention before its residual addition.  Head
concatenation is represented by the finite function `Head → HeadValue`; the
shared `outputProjection` is the executable concat-plus-`W_O` row map. -/
noncomputable def selfAttentionLayer {Node : Type*} [Fintype Node]
    {Model HeadValue : Type*} {Head : Type uHead}
    [AddCommMonoid HeadValue] [Module ℝ HeadValue]
    (active : Node → Bool)
    (score : (Node → Model) → Head → Node → Node → ℝ)
    (multiplier : Head → Node → Node → ℝ)
    (valueProjection : Head → Model → HeadValue)
    (outputProjection : (Head → HeadValue) → Model)
    (rows : Node → Model) (source : Node) : Model :=
  outputProjection fun head =>
    attentionRead active (score rows head) (multiplier head)
      (fun target => valueProjection head (rows target)) source

/-- The full masked, multi-head, output-projected attention layer is
equivariant when scores and realized attention-dropout multipliers are
transported and all learned projections are shared across node rows. -/
theorem selfAttentionLayer_transport
    {Left : Type uLeft} {Right : Type uRight}
    [Fintype Left] [Fintype Right]
    {Model HeadValue : Type*} {Head : Type uHead}
    [AddCommMonoid HeadValue] [Module ℝ HeadValue]
    (relabel : Left ≃ Right)
    (active : Left → Bool)
    (leftScore : (Left → Model) → Head → Left → Left → ℝ)
    (rightScore : (Right → Model) → Head → Right → Right → ℝ)
    (scoreCompatible : ScoreLayerCompatible relabel leftScore rightScore)
    (leftMultiplier : Head → Left → Left → ℝ)
    (rightMultiplier : Head → Right → Right → ℝ)
    (multiplierCompatible : ∀ head source target,
      rightMultiplier head (relabel source) (relabel target) =
        leftMultiplier head source target)
    (valueProjection : Head → Model → HeadValue)
    (outputProjection : (Head → HeadValue) → Model)
    (rows : Left → Model) (source : Left) :
    selfAttentionLayer (transportRows relabel active) rightScore
        rightMultiplier valueProjection outputProjection
        (transportRows relabel rows) (relabel source) =
      selfAttentionLayer active leftScore leftMultiplier valueProjection
        outputProjection rows source := by
  unfold selfAttentionLayer
  congr 1
  funext head
  have scoreEq :
      rightScore (transportRows relabel rows) head =
        transportPairs relabel (leftScore rows head) := by
    funext rightSource rightTarget
    obtain ⟨leftSource, rfl⟩ := relabel.surjective rightSource
    obtain ⟨leftTarget, rfl⟩ := relabel.surjective rightTarget
    simpa [transportPairs] using
      scoreCompatible rows head leftSource leftTarget
  have multiplierEq :
      rightMultiplier head =
        transportPairs relabel (leftMultiplier head) := by
    funext rightSource rightTarget
    obtain ⟨leftSource, rfl⟩ := relabel.surjective rightSource
    obtain ⟨leftTarget, rfl⟩ := relabel.surjective rightTarget
    simpa [transportPairs] using
      multiplierCompatible head leftSource leftTarget
  have valueEq :
      (fun target : Right =>
        valueProjection head (transportRows relabel rows target)) =
        transportRows relabel
          (fun target : Left => valueProjection head (rows target)) := by
    funext target
    simp [transportRows]
  rw [scoreEq, multiplierEq, valueEq]
  exact attentionRead_transport relabel active (leftScore rows head)
    (leftMultiplier head)
    (fun target => valueProjection head (rows target)) source

/-- Self-attention specialized to a typed relation graph. -/
noncomputable def graphSelfAttentionLayer
    {Node NodeKind Feature Role Model HeadValue : Type*}
    {Head : Type uHead} [Fintype Node]
    [AddCommMonoid HeadValue] [Module ℝ HeadValue]
    (graph : TypedRelationGraph Node NodeKind Feature Role)
    (positionAction : Nat → HeadValue → HeadValue)
    (pairing : HeadValue → HeadValue → ℝ)
    (embedding : Role → Head → ℝ)
    (queryProjection keyProjection valueProjection :
      Head → Model → HeadValue)
    (outputProjection : (Head → HeadValue) → Model)
    (multiplier : Head → Node → Node → ℝ)
    (rows : Node → Model) (source : Node) : Model :=
  selfAttentionLayer graph.active
    (graphAttentionScore graph positionAction pairing embedding
      queryProjection keyProjection)
    multiplier valueProjection outputProjection rows source

/-- A position-preserving typed-graph isomorphism discharges the complete
self-attention relabeling law, including graph mask and relation bias. -/
theorem graphSelfAttentionLayer_compatible
    {LeftNode : Type uLeft} {RightNode : Type uRight}
    {NodeKind Feature Role Model HeadValue : Type*}
    {Head : Type uHead} [Fintype LeftNode] [Fintype RightNode]
    [AddCommMonoid HeadValue] [Module ℝ HeadValue]
    {left : TypedRelationGraph LeftNode NodeKind Feature Role}
    {right : TypedRelationGraph RightNode NodeKind Feature Role}
    (isomorphism : left.PositionPreservingIsomorphism right)
    (leftFunctional : left.relationFunctional)
    (rightFunctional : right.relationFunctional)
    (positionAction : Nat → HeadValue → HeadValue)
    (pairing : HeadValue → HeadValue → ℝ)
    (embedding : Role → Head → ℝ)
    (queryProjection keyProjection valueProjection :
      Head → Model → HeadValue)
    (outputProjection : (Head → HeadValue) → Model)
    (leftMultiplier : Head → LeftNode → LeftNode → ℝ)
    (rightMultiplier : Head → RightNode → RightNode → ℝ)
    (multiplierCompatible : ∀ head source target,
      rightMultiplier head (isomorphism.node source)
          (isomorphism.node target) =
        leftMultiplier head source target) :
    LayerCompatible isomorphism.node
      (graphSelfAttentionLayer left positionAction pairing embedding
        queryProjection keyProjection valueProjection outputProjection
        leftMultiplier)
      (graphSelfAttentionLayer right positionAction pairing embedding
        queryProjection keyProjection valueProjection outputProjection
        rightMultiplier) := by
  intro rows source
  unfold graphSelfAttentionLayer
  have activeEq :
      right.active = transportRows isomorphism.node left.active := by
    funext rightNode
    obtain ⟨leftNode, rfl⟩ := isomorphism.node.surjective rightNode
    simpa [transportRows] using isomorphism.active_preserved leftNode
  rw [activeEq]
  exact selfAttentionLayer_transport isomorphism.node left.active
    (graphAttentionScore left positionAction pairing embedding
      queryProjection keyProjection)
    (graphAttentionScore right positionAction pairing embedding
      queryProjection keyProjection)
    (graphAttentionScore_compatible isomorphism leftFunctional
      rightFunctional positionAction pairing embedding
      queryProjection keyProjection)
    leftMultiplier rightMultiplier multiplierCompatible valueProjection
    outputProjection rows source

/-! ## Residual block composition -/

/-- Add a global layer's refinement to the running residual stream. -/
def residualLayer {Node : Type*} {Value : Type*} [Add Value]
    (layer : (Node → Value) → Node → Value)
    (rows : Node → Value) (node : Node) : Value :=
  rows node + layer rows node

theorem residualLayer_compatible
    {Left : Type uLeft} {Right : Type uRight}
    {Value : Type uValue} [Add Value]
    (relabel : Left ≃ Right)
    (left : (Left → Value) → Left → Value)
    (right : (Right → Value) → Right → Value)
    (compatible : LayerCompatible relabel left right) :
    LayerCompatible relabel (residualLayer left) (residualLayer right) := by
  intro rows node
  simp [residualLayer, transportRows, compatible rows node]

/-- A shared deterministic row function is equivariant under every relabeling. -/
theorem sharedPointwise_compatible
    {Left : Type uLeft} {Right : Type uRight}
    {Value : Type uValue} (relabel : Left ≃ Right) (layer : Value → Value) :
    LayerCompatible relabel
      (fun rows node => layer (rows node))
      (fun rows node => layer (rows node)) := by
  intro rows node
  simp [transportRows]

/-! ## Exact rowwise operators used by the implementation -/

/-- A row of a finite real-valued activation tensor. -/
abbrev EuclideanRow (width : Nat) := Fin width → ℝ

/-- A finite affine map, matching a dense linear layer with bias. -/
def affine {inputWidth outputWidth : Nat}
    (weight : Fin outputWidth → Fin inputWidth → ℝ)
    (bias : Fin outputWidth → ℝ)
    (input : EuclideanRow inputWidth) : EuclideanRow outputWidth :=
  fun output => (∑ inputIndex, weight output inputIndex * input inputIndex) +
    bias output

/-- Mean square over one activation row.  The architecture uses positive
widths; the zero-width algebraic value is left explicit rather than hidden. -/
noncomputable def rowMeanSquare {width : Nat} (input : EuclideanRow width) : ℝ :=
  (∑ index, input index * input index) / (width : ℝ)

/-- RMSNorm with no mean subtraction, matching the executable order
`input * rsqrt(mean(input^2) + eps) * weight`. -/
noncomputable def rmsNorm {width : Nat} (eps : ℝ)
    (weight : EuclideanRow width) (input : EuclideanRow width) :
    EuclideanRow width :=
  fun index => input index * (Real.sqrt (rowMeanSquare input + eps))⁻¹ *
    weight index

/-- The scalar SiLU nonlinearity used by the feed-forward gate. -/
noncomputable def silu (value : ℝ) : ℝ :=
  value / (1 + Real.exp (-value))

/-- SwiGLU with an explicit realized dropout multiplier between the gated
hidden product and the output projection.  Evaluation mode uses multiplier
one at every hidden coordinate. -/
noncomputable def swiGLU {modelWidth hiddenWidth : Nat}
    (gateWeight valueWeight : Fin hiddenWidth → Fin modelWidth → ℝ)
    (gateBias valueBias : EuclideanRow hiddenWidth)
    (outputWeight : Fin modelWidth → Fin hiddenWidth → ℝ)
    (outputBias : EuclideanRow modelWidth)
    (dropoutMultiplier : EuclideanRow hiddenWidth)
    (input : EuclideanRow modelWidth) : EuclideanRow modelWidth :=
  fun output =>
    (∑ hidden,
      outputWeight output hidden *
        (dropoutMultiplier hidden *
          (silu (affine gateWeight gateBias input hidden) *
            affine valueWeight valueBias input hidden))) +
      outputBias output

/-- Exact RMSNorm is rowwise and hence commutes with every node relabeling. -/
theorem rmsNorm_compatible
    {Left : Type uLeft} {Right : Type uRight} {width : Nat}
    (relabel : Left ≃ Right) (eps : ℝ) (weight : EuclideanRow width) :
    LayerCompatible relabel
      (fun rows node => rmsNorm eps weight (rows node))
      (fun rows node => rmsNorm eps weight (rows node)) :=
  sharedPointwise_compatible relabel (rmsNorm eps weight)

/-- Evaluation-mode SwiGLU is rowwise and commutes with every relabeling. -/
theorem swiGLU_eval_compatible
    {Left : Type uLeft} {Right : Type uRight}
    {modelWidth hiddenWidth : Nat}
    (relabel : Left ≃ Right)
    (gateWeight valueWeight : Fin hiddenWidth → Fin modelWidth → ℝ)
    (gateBias valueBias : EuclideanRow hiddenWidth)
    (outputWeight : Fin modelWidth → Fin hiddenWidth → ℝ)
    (outputBias : EuclideanRow modelWidth) :
    LayerCompatible relabel
      (fun rows node => swiGLU gateWeight valueWeight gateBias valueBias
        outputWeight outputBias (fun _ => 1) (rows node))
      (fun rows node => swiGLU gateWeight valueWeight gateBias valueBias
        outputWeight outputBias (fun _ => 1) (rows node)) :=
  sharedPointwise_compatible relabel _

/-- Training-mode SwiGLU remains equivariant if its realized dropout rows are
transported along with the activation rows. -/
theorem swiGLU_dropout_transport
    {Left : Type uLeft} {Right : Type uRight}
    {modelWidth hiddenWidth : Nat}
    (relabel : Left ≃ Right)
    (gateWeight valueWeight : Fin hiddenWidth → Fin modelWidth → ℝ)
    (gateBias valueBias : EuclideanRow hiddenWidth)
    (outputWeight : Fin modelWidth → Fin hiddenWidth → ℝ)
    (outputBias : EuclideanRow modelWidth)
    (dropoutMultiplier : Left → EuclideanRow hiddenWidth)
    (rows : Left → EuclideanRow modelWidth) (node : Left) :
    swiGLU gateWeight valueWeight gateBias valueBias outputWeight outputBias
        (transportRows relabel dropoutMultiplier (relabel node))
        (transportRows relabel rows (relabel node)) =
      swiGLU gateWeight valueWeight gateBias valueBias outputWeight outputBias
        (dropoutMultiplier node) (rows node) := by
  simp

/-- A node-indexed stochastic row function is equivariant when its realized
randomness is transported with the node. -/
theorem transportedPointwise_compatible
    {Left : Type uLeft} {Right : Type uRight}
    {Input Output : Type*} (relabel : Left ≃ Right)
    (left : Left → Input → Output) :
    let right : Right → Input → Output :=
      fun node => left (relabel.symm node)
    ∀ rows node,
      right (relabel node) (transportRows relabel rows (relabel node)) =
        left node (rows node) := by
  intro right rows node
  simp [right, transportRows]

/-- The exact pre-norm two-residual block shape used by the encoder. -/
def encoderBlock {Node : Type*} {Value : Type*} [Add Value]
    (attentionNorm : Value → Value)
    (attention : (Node → Value) → Node → Value)
    (ffnNorm : Value → Value) (ffn : Value → Value)
    (rows : Node → Value) : Node → Value :=
  let afterAttention := fun node =>
    rows node + attention (fun row => attentionNorm (rows row)) node
  fun node => afterAttention node + ffn (ffnNorm (afterAttention node))

/-- Compatible attention plus shared rowwise normalization and feed-forward
maps imply equivariance of the complete deterministic encoder block. -/
theorem encoderBlock_transport
    {Left : Type uLeft} {Right : Type uRight}
    {Value : Type uValue} [Add Value]
    (relabel : Left ≃ Right)
    (attentionNorm : Value → Value)
    (leftAttention : (Left → Value) → Left → Value)
    (rightAttention : (Right → Value) → Right → Value)
    (attentionCompatible :
      LayerCompatible relabel leftAttention rightAttention)
    (ffnNorm : Value → Value) (ffn : Value → Value)
    (rows : Left → Value) (node : Left) :
    encoderBlock attentionNorm rightAttention ffnNorm ffn
        (transportRows relabel rows) (relabel node) =
      encoderBlock attentionNorm leftAttention ffnNorm ffn rows node := by
  simp only [encoderBlock, transportRows_apply]
  have normalizedEq :
      (fun row : Right => attentionNorm (transportRows relabel rows row)) =
        transportRows relabel (fun row => attentionNorm (rows row)) := by
    funext rightNode
    simp [transportRows]
  rw [normalizedEq]
  rw [attentionCompatible (fun row => attentionNorm (rows row)) node]

/-- One deterministic evaluation-mode graph encoder block with the exact
pre-norm attention residual followed by the pre-norm SwiGLU residual. -/
noncomputable def graphEncoderBlock
    {Node NodeKind Feature Role Model HeadValue : Type*}
    {Head : Type uHead} [Fintype Node] [Add Model]
    [AddCommMonoid HeadValue] [Module ℝ HeadValue]
    (graph : TypedRelationGraph Node NodeKind Feature Role)
    (positionAction : Nat → HeadValue → HeadValue)
    (pairing : HeadValue → HeadValue → ℝ)
    (embedding : Role → Head → ℝ)
    (queryProjection keyProjection valueProjection :
      Head → Model → HeadValue)
    (outputProjection : (Head → HeadValue) → Model)
    (multiplier : Head → Node → Node → ℝ)
    (attentionNorm ffnNorm ffn : Model → Model)
    (rows : Node → Model) : Node → Model :=
  encoderBlock attentionNorm
    (graphSelfAttentionLayer graph positionAction pairing embedding
      queryProjection keyProjection valueProjection outputProjection
      multiplier)
    ffnNorm ffn rows

/-- Position-preserving typed-graph isomorphism implies equivariance of the
complete deterministic evaluation-mode encoder block. -/
theorem graphEncoderBlock_compatible
    {LeftNode : Type uLeft} {RightNode : Type uRight}
    {NodeKind Feature Role Model HeadValue : Type*}
    {Head : Type uHead} [Fintype LeftNode] [Fintype RightNode]
    [Add Model] [AddCommMonoid HeadValue] [Module ℝ HeadValue]
    {left : TypedRelationGraph LeftNode NodeKind Feature Role}
    {right : TypedRelationGraph RightNode NodeKind Feature Role}
    (isomorphism : left.PositionPreservingIsomorphism right)
    (leftFunctional : left.relationFunctional)
    (rightFunctional : right.relationFunctional)
    (positionAction : Nat → HeadValue → HeadValue)
    (pairing : HeadValue → HeadValue → ℝ)
    (embedding : Role → Head → ℝ)
    (queryProjection keyProjection valueProjection :
      Head → Model → HeadValue)
    (outputProjection : (Head → HeadValue) → Model)
    (leftMultiplier : Head → LeftNode → LeftNode → ℝ)
    (rightMultiplier : Head → RightNode → RightNode → ℝ)
    (multiplierCompatible : ∀ head source target,
      rightMultiplier head (isomorphism.node source)
          (isomorphism.node target) =
        leftMultiplier head source target)
    (attentionNorm ffnNorm ffn : Model → Model) :
    LayerCompatible isomorphism.node
      (graphEncoderBlock left positionAction pairing embedding
        queryProjection keyProjection valueProjection outputProjection
        leftMultiplier attentionNorm ffnNorm ffn)
      (graphEncoderBlock right positionAction pairing embedding
        queryProjection keyProjection valueProjection outputProjection
        rightMultiplier attentionNorm ffnNorm ffn) := by
  intro rows node
  unfold graphEncoderBlock
  exact encoderBlock_transport isomorphism.node attentionNorm
    (graphSelfAttentionLayer left positionAction pairing embedding
      queryProjection keyProjection valueProjection outputProjection
      leftMultiplier)
    (graphSelfAttentionLayer right positionAction pairing embedding
      queryProjection keyProjection valueProjection outputProjection
      rightMultiplier)
    (graphSelfAttentionLayer_compatible isomorphism leftFunctional
      rightFunctional positionAction pairing embedding queryProjection
      keyProjection valueProjection outputProjection leftMultiplier
      rightMultiplier multiplierCompatible)
    ffnNorm ffn rows node

/-- Apply the first `layers` members of an indexed block family. -/
def iterateLayers {Node : Type*} {Value : Type*}
    (layer : Nat → (Node → Value) → Node → Value) :
    Nat → (Node → Value) → Node → Value
  | 0, rows => rows
  | layers + 1, rows => layer layers (iterateLayers layer layers rows)

/-- Applying a finite list of compatible blocks preserves equivariance. -/
theorem iterateLayer_transport
    {Left : Type uLeft} {Right : Type uRight}
    {Value : Type uValue}
    (relabel : Left ≃ Right)
    (leftLayer : Nat → (Left → Value) → Left → Value)
    (rightLayer : Nat → (Right → Value) → Right → Value)
    (compatible : ∀ layer,
      LayerCompatible relabel (leftLayer layer) (rightLayer layer))
    (rows : Left → Value) :
    ∀ (layers : Nat) (node : Left),
      iterateLayers rightLayer layers (transportRows relabel rows)
          (relabel node) =
        iterateLayers leftLayer layers rows node := by
  intro layers
  induction layers with
  | zero => intro node; simp [iterateLayers, transportRows]
  | succ layers inductionHypothesis =>
      intro node
      simp only [iterateLayers]
      have previousEq :
          iterateLayers rightLayer layers (transportRows relabel rows) =
            transportRows relabel
              (iterateLayers leftLayer layers rows) := by
        funext rightNode
        obtain ⟨leftNode, rfl⟩ := relabel.surjective rightNode
        simpa [transportRows] using inductionHypothesis leftNode
      rw [previousEq]
      exact compatible layers
        (iterateLayers leftLayer layers rows) node

/-- Zero inactive rows after the final normalization, exactly as the encoder
does at its output boundary. -/
def zeroInactive {Node : Type*} {Value : Type*} [Zero Value]
    (active : Node → Bool) (rows : Node → Value) (node : Node) : Value :=
  if active node then rows node else 0

theorem zeroInactive_transport
    {Left : Type uLeft} {Right : Type uRight}
    {Value : Type uValue} [Zero Value]
    (relabel : Left ≃ Right) (active : Left → Bool)
    (rows : Left → Value) (node : Left) :
    zeroInactive (transportRows relabel active)
        (transportRows relabel rows) (relabel node) =
      zeroInactive active rows node := by
  simp [zeroInactive, transportRows]

/-- The deterministic output boundary of a finite encoder stack: indexed
blocks, final rowwise normalization, then inactive-row zeroing. -/
def encoderStackOutput {Node : Type*} {Value : Type*} [Zero Value]
    (active : Node → Bool) (finalNorm : Value → Value)
    (layer : Nat → (Node → Value) → Node → Value)
    (layers : Nat) (rows : Node → Value) : Node → Value :=
  zeroInactive active
    (fun node => finalNorm (iterateLayers layer layers rows node))

/-- Compatible blocks lift through an arbitrary finite encoder depth, the
shared final normalization, and exact inactive-row zeroing. -/
theorem encoderStackOutput_transport
    {Left : Type uLeft} {Right : Type uRight}
    {Value : Type uValue} [Zero Value]
    (relabel : Left ≃ Right) (active : Left → Bool)
    (finalNorm : Value → Value)
    (leftLayer : Nat → (Left → Value) → Left → Value)
    (rightLayer : Nat → (Right → Value) → Right → Value)
    (compatible : ∀ layer,
      LayerCompatible relabel (leftLayer layer) (rightLayer layer))
    (layers : Nat) (rows : Left → Value) (node : Left) :
    encoderStackOutput (transportRows relabel active) finalNorm rightLayer
        layers (transportRows relabel rows) (relabel node) =
      encoderStackOutput active finalNorm leftLayer layers rows node := by
  unfold encoderStackOutput
  have stackEq := iterateLayer_transport relabel leftLayer rightLayer
    compatible rows layers node
  simp only [zeroInactive, transportRows_apply]
  rw [stackEq]

/-! ## Exact stochastic boundary fixture -/

namespace EncoderEquivarianceFixtures

def boolSwap : Bool ≃ Bool := Equiv.swap false true

/-- A realized dropout multiplier that is not transported can break
equivariance even when the underlying row function is the identity. -/
theorem untransported_dropout_breaks_equivariance :
    let rows : Bool → ℝ := fun _ => 1
    let leftMultiplier : Bool → ℝ := fun node => if node then 0 else 2
    let rightMultiplier := leftMultiplier
    rightMultiplier (boolSwap false) *
        transportRows boolSwap rows (boolSwap false) = 0 ∧
      leftMultiplier false * rows false = 2 := by
  norm_num [boolSwap, transportRows]

/-- Transporting the same realized dropout multiplier restores the equality. -/
theorem transported_dropout_preserves_equivariance :
    let rows : Bool → ℝ := fun _ => 1
    let leftMultiplier : Bool → ℝ := fun node => if node then 0 else 2
    let rightMultiplier := transportRows boolSwap leftMultiplier
    rightMultiplier (boolSwap false) *
        transportRows boolSwap rows (boolSwap false) =
      leftMultiplier false * rows false := by
  norm_num [boolSwap, transportRows]

end EncoderEquivarianceFixtures

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
