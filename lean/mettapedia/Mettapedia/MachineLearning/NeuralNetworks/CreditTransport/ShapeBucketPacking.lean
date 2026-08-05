import Mathlib.Tactic

/-!
# Exact shape-and-operator bucket packing

Lowering a logical graph into shape-bucketed tensor stacks.
This file isolates the semantic condition under which that compiler
transformation is exact.

Every logical node has an execution signature.  The signature determines both
its feature width and the operator used for its update.  Packing enumerates the
nodes in each signature fiber, applies one shared batched operator per fiber,
and then unpacks back to logical node identities.  Packing and unpacking are
mutual inverses, and the packed shared-operator execution is exactly the
logical nodewise execution.

The operator part of the signature is essential.  A two-node fixture has equal
feature widths but different logical operators; grouping those nodes by shape
alone and applying one shared operator gives the wrong result.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ShapeBucketPacking

universe u v w

variable {Node : Type u} {Signature : Type v} {Value : Type w}
variable [Fintype Node] [DecidableEq Signature]

/-- Nodes assigned to one execution signature. -/
abbrev Fiber
    (signature : Node → Signature)
    (bucket : Signature) :=
  {node : Node // signature node = bucket}

/-- The deterministic finite enumeration used for one packed bucket. -/
noncomputable def fiberEquivFin
    (signature : Node → Signature)
    (bucket : Signature) :
    Fiber signature bucket ≃
      Fin (Fintype.card (Fiber signature bucket)) :=
  Fintype.equivFin _

/-- A logical state gives every node a vector whose width is determined by its
execution signature.  The bucket index records that width while the fiber
element retains the original node identity. -/
abbrev LogicalState
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (Value : Type w) :=
  (bucket : Signature) →
    Fiber signature bucket →
      Fin (width bucket) → Value

/-- A packed state gives every execution signature a stack of same-width node
vectors. -/
abbrev PackedState
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (Value : Type w) :=
  (bucket : Signature) →
    Fin (Fintype.card (Fiber signature bucket)) →
      Fin (width bucket) → Value

/-- Pack logical node vectors into signature-indexed stacks. -/
noncomputable def pack
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (state : LogicalState signature width Value) :
    PackedState signature width Value :=
  fun bucket packedIndex feature =>
    state bucket
      ((fiberEquivFin signature bucket).symm packedIndex)
      feature

/-- Unpack signature-indexed stacks back to logical node identities. -/
noncomputable def unpack
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (state : PackedState signature width Value) :
    LogicalState signature width Value :=
  fun bucket node feature =>
    state bucket
      ((fiberEquivFin signature bucket).toFun node)
      feature

/-- Packing and then unpacking preserves every logical value. -/
@[simp] theorem unpack_pack
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (state : LogicalState signature width Value) :
    unpack signature width (pack signature width state) = state := by
  classical
  funext bucket node feature
  simp [unpack, pack]

/-- Unpacking and then packing preserves every packed value. -/
@[simp] theorem pack_unpack
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (state : PackedState signature width Value) :
    pack signature width (unpack signature width state) = state := by
  classical
  funext bucket packedIndex feature
  simp [unpack, pack]

/-- A logical update may use one vector operator for each execution
signature. -/
def logicalMap
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (operator :
      (bucket : Signature) →
        (Fin (width bucket) → Value) →
          Fin (width bucket) → Value)
    (state : LogicalState signature width Value) :
    LogicalState signature width Value :=
  fun bucket node => operator bucket (state bucket node)

/-- Execute one shared vector operator across every row in each packed
signature bucket. -/
def packedMap
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (operator :
      (bucket : Signature) →
        (Fin (width bucket) → Value) →
          Fin (width bucket) → Value)
    (state : PackedState signature width Value) :
    PackedState signature width Value :=
  fun bucket packedIndex =>
    operator bucket (state bucket packedIndex)

/-- Shared per-signature packed execution is exactly the logical nodewise
execution after unpacking. -/
theorem unpack_packedMap_eq_logicalMap_unpack
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (operator :
      (bucket : Signature) →
        (Fin (width bucket) → Value) →
          Fin (width bucket) → Value)
    (state : PackedState signature width Value) :
    unpack signature width
        (packedMap signature width operator state) =
      logicalMap signature width operator
        (unpack signature width state) := by
  rfl

/-- The compiler-lowering crown: pack, execute once per signature bucket, and
unpack equals direct logical execution. -/
theorem unpack_packedMap_pack_eq_logicalMap
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (operator :
      (bucket : Signature) →
        (Fin (width bucket) → Value) →
          Fin (width bucket) → Value)
    (state : LogicalState signature width Value) :
    unpack signature width
        (packedMap signature width operator
          (pack signature width state)) =
      logicalMap signature width operator state := by
  rw [unpack_packedMap_eq_logicalMap_unpack]
  simp

/-- Direct logical execution may be packed without changing its result. -/
theorem pack_logicalMap_eq_packedMap_pack
    (signature : Node → Signature)
    (width : Signature → ℕ)
    (operator :
      (bucket : Signature) →
        (Fin (width bucket) → Value) →
          Fin (width bucket) → Value)
    (state : LogicalState signature width Value) :
    pack signature width (logicalMap signature width operator state) =
      packedMap signature width operator
        (pack signature width state) := by
  have unpackInjective :
      Function.Injective
        (unpack signature width :
          PackedState signature width Value →
            LogicalState signature width Value) := by
    intro left right equal
    calc
      left = pack signature width (unpack signature width left) :=
        (pack_unpack signature width left).symm
      _ = pack signature width (unpack signature width right) :=
        congrArg (pack signature width) equal
      _ = right := pack_unpack signature width right
  apply unpackInjective
  simpa using
    (unpack_packedMap_pack_eq_logicalMap
      signature width operator state).symm

/-! ## Packed adjacency keys and segment sums -/

/-- A packed node address retains its execution signature and its row inside
that signature's stack. -/
abbrev PackedNodeIndex
    (signature : Node → Signature) :=
  Σ bucket : Signature,
    Fin (Fintype.card (Fiber signature bucket))

/-- Re-key a logical node by its signature and its row within that bucket. -/
noncomputable def packNode
    (signature : Node → Signature)
    (node : Node) :
    PackedNodeIndex signature :=
  ⟨signature node,
    (fiberEquivFin signature (signature node)) ⟨node, rfl⟩⟩

/-- Recover the logical node named by a packed address. -/
noncomputable def unpackNode
    (signature : Node → Signature)
    (packed : PackedNodeIndex signature) :
    Node :=
  ((fiberEquivFin signature packed.1).symm packed.2).1

/-- Packed node addresses retain logical identity. -/
@[simp] theorem unpackNode_packNode
    (signature : Node → Signature)
    (node : Node) :
    unpackNode signature (packNode signature node) = node := by
  classical
  unfold unpackNode packNode
  exact congrArg Subtype.val
    ((fiberEquivFin signature (signature node)).symm_apply_apply
      ⟨node, rfl⟩)

theorem packNode_injective
    (signature : Node → Signature) :
    Function.Injective (packNode signature) := by
  intro left right equal
  have recovered := congrArg (unpackNode signature) equal
  simpa using recovered

variable [DecidableEq Node]
variable {Edge : Type*} [Fintype Edge]
variable {Weight : Type*} [AddCommMonoid Weight]

/-- Sum edge contributions at one logical target node. -/
def logicalSegmentSum
    (target : Edge → Node)
    (contribution : Edge → Weight)
    (node : Node) :
    Weight :=
  ∑ edge ∈ Finset.univ.filter (fun edge => target edge = node),
    contribution edge

/-- Sum edge contributions after target nodes have been re-keyed into packed
signature buckets. -/
noncomputable def packedSegmentSum
    (signature : Node → Signature)
    (target : Edge → Node)
    (contribution : Edge → Weight)
    (packedTarget : PackedNodeIndex signature) :
    Weight :=
  ∑ edge ∈ Finset.univ.filter
      (fun edge => packNode signature (target edge) = packedTarget),
    contribution edge

/-- Re-keying an adjacency by packed node addresses preserves every
target-segment sum exactly. -/
theorem packedSegmentSum_packNode
    (signature : Node → Signature)
    (target : Edge → Node)
    (contribution : Edge → Weight)
    (node : Node) :
    packedSegmentSum signature target contribution
        (packNode signature node) =
      logicalSegmentSum target contribution node := by
  classical
  unfold packedSegmentSum logicalSegmentSum
  apply Finset.sum_congr
  · ext edge
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro equal
      exact (packNode_injective signature) equal
    · intro equal
      exact congrArg (packNode signature) equal
  · intro edge member
    rfl

/-! ## Executable recovery and failure fixtures -/

def boolSignature : Bool → Bool :=
  id

def unitWidth (_ : Bool) : ℕ :=
  1

def signedOperator
    (bucket : Bool)
    (vector : Fin (unitWidth bucket) → ℤ) :
    Fin (unitWidth bucket) → ℤ :=
  if bucket then fun feature => -vector feature
  else fun feature => vector feature + 1

def signedInitial :
    LogicalState boolSignature unitWidth ℤ :=
  fun _ node _ => if node.1 then 3 else 5

/-- Distinct semantic signatures with the same shape are still packed and
executed exactly. -/
theorem signed_fixture_packed_exact :
    unpack boolSignature unitWidth
        (packedMap boolSignature unitWidth signedOperator
          (pack boolSignature unitWidth signedInitial)) =
      logicalMap boolSignature unitWidth signedOperator signedInitial :=
  unpack_packedMap_pack_eq_logicalMap
    boolSignature unitWidth signedOperator signedInitial

/-- Shape-only bucketing merges both logical nodes into one bucket. -/
def shapeOnlySignature (_ : Bool) : Unit :=
  ()

def shapeOnlyWidth (_ : Unit) : ℕ :=
  1

def sharedIdentityOperator
    (_ : Unit)
    (vector : Fin 1 → ℤ) :
    Fin 1 → ℤ :=
  vector

def shapeOnlyInitial :
    LogicalState shapeOnlySignature shapeOnlyWidth ℤ :=
  fun _ node _ => if node.1 then 3 else 5

def heterogeneousLogicalMap
    (state : LogicalState shapeOnlySignature shapeOnlyWidth ℤ) :
    LogicalState shapeOnlySignature shapeOnlyWidth ℤ :=
  fun bucket node feature =>
    if node.1 then -state bucket node feature
    else state bucket node feature + 1

def shapeOnlyFeature :
    Fin (shapeOnlyWidth ()) :=
  ⟨0, by decide⟩

def shapeOnlyTrueNode :
    Fiber shapeOnlySignature () :=
  ⟨true, rfl⟩

/-- Equal feature shapes do not license a shared operator: the shape-only
packed execution disagrees with the true heterogeneous logical update. -/
theorem shape_only_bucket_is_not_semantically_sufficient :
    unpack shapeOnlySignature shapeOnlyWidth
        (packedMap shapeOnlySignature shapeOnlyWidth sharedIdentityOperator
          (pack shapeOnlySignature shapeOnlyWidth shapeOnlyInitial))
        () shapeOnlyTrueNode shapeOnlyFeature ≠
      heterogeneousLogicalMap shapeOnlyInitial
        () shapeOnlyTrueNode shapeOnlyFeature := by
  rw [unpack_packedMap_pack_eq_logicalMap]
  norm_num [logicalMap, sharedIdentityOperator, shapeOnlyInitial,
    heterogeneousLogicalMap, shapeOnlyTrueNode]

/-- A broken adjacency key which keeps only an ordinal and discards the bucket
tag. -/
def untaggedBoolIndex (_ : Bool) : Fin 1 :=
  0

def boolEdgeTarget : Bool → Bool :=
  id

def boolEdgeContribution (edge : Bool) : ℕ :=
  if edge then 3 else 2

/-- Dropping the signature tag merges the two singleton buckets and therefore
changes the segment sum at `false` from two to five. -/
theorem untagged_bucket_index_merges_distinct_targets :
    (∑ edge ∈ Finset.univ.filter
        (fun edge : Bool =>
          untaggedBoolIndex (boolEdgeTarget edge) =
            untaggedBoolIndex false),
        boolEdgeContribution edge) = 5 ∧
      logicalSegmentSum boolEdgeTarget boolEdgeContribution false = 2 := by
  norm_num [logicalSegmentSum, boolEdgeTarget, boolEdgeContribution,
    untaggedBoolIndex, Finset.sum_filter]

#print axioms unpack_pack
#print axioms pack_unpack
#print axioms unpack_packedMap_pack_eq_logicalMap
#print axioms pack_logicalMap_eq_packedMap_pack
#print axioms unpackNode_packNode
#print axioms packNode_injective
#print axioms packedSegmentSum_packNode
#print axioms signed_fixture_packed_exact
#print axioms shape_only_bucket_is_not_semantically_sufficient
#print axioms untagged_bucket_index_merges_distinct_targets

end ShapeBucketPacking

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
