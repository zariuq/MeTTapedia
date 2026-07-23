import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FixedAddressFrontier
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Typed child initialization for fixed-address carriers

The typed-workspace and selective-belief decoders derive every child from the
same metadata vector: role, one-based parent operator, clamped argument, and
clamped depth embeddings are added.  The carriers then diverge only at their
initialization algebra.  Workspace children pass two projected branches
through coordinatewise `tanh`; belief children pass one shared context through
sigmoid mean and positive softplus-precision heads and store complementary
natural-coordinate packets.

This module states those ideal-real maps independently of tensor layout and
composes them with the fixed-address transition.  A source checker separately
pins the Python calls, clamps, heads, activations, and masks.  No binary32
activation, trained-parameter, or full-decoder equivalence is claimed here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-! ## Shared typed-hole metadata -/

/-- The four learned embedding tables and the source's depth clamp. -/
structure TypedHoleTables (Embedding : Type*) where
  role : ℕ → Embedding
  parent : ℕ → Embedding
  argument : ℕ → Embedding
  depth : ℕ → Embedding
  maxDepth : ℕ

/-- Exact source metadata map.  Argument identifiers are clamped at four;
depth identifiers are clamped at the host's declared maximum. -/
def typedHoleVector {Embedding : Type*} [AddCommMonoid Embedding]
    (tables : TypedHoleTables Embedding)
    (roleId parentId argumentId depthId : ℕ) : Embedding :=
  tables.role roleId + tables.parent parentId +
    tables.argument (min argumentId 4) +
      tables.depth (min depthId tables.maxDepth)

/-- A child records the selected operator with the source's one-based parent
identifier and its zero-based argument position. -/
def typedChildMetadata {Embedding : Type*} [AddCommMonoid Embedding]
    (tables : TypedHoleTables Embedding)
    (roleId safeAction argumentId depthId : ℕ) : Embedding :=
  typedHoleVector tables roleId (safeAction + 1) argumentId depthId

@[simp] theorem typedChildMetadata_eq
    {Embedding : Type*} [AddCommMonoid Embedding]
    (tables : TypedHoleTables Embedding)
    (roleId safeAction argumentId depthId : ℕ) :
    typedChildMetadata tables roleId safeAction argumentId depthId =
      tables.role roleId + tables.parent (safeAction + 1) +
        tables.argument (min argumentId 4) +
          tables.depth (min depthId tables.maxDepth) :=
  rfl

/-! ## Carrier-specific child values -/

/-- Workspace child value at each slot feature.  The memory summary and typed
metadata take distinct affine branches before their sum passes through
coordinatewise `tanh`. -/
noncomputable def workspaceChildValue
    {Embedding SlotFeature : Type*}
    (initialSlot holeTypeProjection : Embedding → SlotFeature → ℝ)
    (sourceSummary childMetadata : Embedding) : SlotFeature → ℝ :=
  fun feature ↦ Real.tanh
    (initialSlot sourceSummary feature +
      holeTypeProjection childMetadata feature)

/-- The ideal-real interpretation of PyTorch's default scalar softplus.  The
finite-precision implementation remains a separate replay obligation. -/
noncomputable def sourceSoftplus (value : ℝ) : ℝ :=
  Real.log (1 + Real.exp value)

theorem sourceSoftplus_pos (value : ℝ) : 0 < sourceSoftplus value := by
  apply Real.log_pos
  linarith [Real.exp_pos value]

/-- One scalar feature of the belief carrier's stored natural coordinates. -/
structure NaturalCoordinatePacket where
  positive : ℝ
  negative : ℝ

namespace NaturalCoordinatePacket

/-- Effective precision stored by one natural-coordinate packet. -/
def precision (packet : NaturalCoordinatePacket) : ℝ :=
  packet.positive + packet.negative

/-- Source-shaped packet: sigmoid mean splits one strictly positive precision
between the positive and negative coordinates. -/
noncomputable def ofLogits
    (meanLogit precisionLogit minimumPrecision : ℝ) :
    NaturalCoordinatePacket :=
  let mean := Real.sigmoid meanLogit
  let packetPrecision := sourceSoftplus precisionLogit + minimumPrecision
  { positive := mean * packetPrecision
    negative := (1 - mean) * packetPrecision }

@[simp] theorem ofLogits_precision
    (meanLogit precisionLogit minimumPrecision : ℝ) :
    (ofLogits meanLogit precisionLogit minimumPrecision).precision =
      sourceSoftplus precisionLogit + minimumPrecision := by
  simp [ofLogits, precision]
  ring

theorem ofLogits_precision_pos
    (meanLogit precisionLogit minimumPrecision : ℝ)
    (hminimum : 0 ≤ minimumPrecision) :
    0 < (ofLogits meanLogit precisionLogit minimumPrecision).precision := by
  rw [ofLogits_precision]
  exact add_pos_of_pos_of_nonneg (sourceSoftplus_pos precisionLogit) hminimum

theorem ofLogits_nonnegative
    (meanLogit precisionLogit minimumPrecision : ℝ)
    (hminimum : 0 ≤ minimumPrecision) :
    0 ≤ (ofLogits meanLogit precisionLogit minimumPrecision).positive ∧
      0 ≤ (ofLogits meanLogit precisionLogit minimumPrecision).negative := by
  have hprecision :
      0 ≤ sourceSoftplus precisionLogit + minimumPrecision :=
    (add_pos_of_pos_of_nonneg (sourceSoftplus_pos precisionLogit) hminimum).le
  constructor
  · exact mul_nonneg (Real.sigmoid_nonneg meanLogit) hprecision
  · exact mul_nonneg
      (sub_nonneg.mpr (Real.sigmoid_le_one meanLogit)) hprecision

/-- Dividing positive evidence by total evidence recovers the sigmoid mean
exactly because the source precision floor makes the denominator positive. -/
theorem ofLogits_strength
    (meanLogit precisionLogit minimumPrecision : ℝ)
    (hminimum : 0 ≤ minimumPrecision) :
    (ofLogits meanLogit precisionLogit minimumPrecision).positive /
        (ofLogits meanLogit precisionLogit minimumPrecision).precision =
      Real.sigmoid meanLogit := by
  have hdenominator :
      sourceSoftplus precisionLogit + minimumPrecision ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg
      (sourceSoftplus_pos precisionLogit) hminimum)
  rw [ofLogits_precision]
  simp only [ofLogits]
  field_simp [hdenominator]

end NaturalCoordinatePacket

/-- Belief child packets at every feature.  Both heads see the sum of the
source summary and the common typed-child metadata. -/
noncomputable def beliefChildValue
    {Embedding Feature : Type*} [Add Embedding]
    (holeMean holePrecision : Embedding → Feature → ℝ)
    (minimumPrecision : ℝ)
    (sourceSummary childMetadata : Embedding) :
    Feature → NaturalCoordinatePacket :=
  fun feature ↦ NaturalCoordinatePacket.ofLogits
    (holeMean (sourceSummary + childMetadata) feature)
    (holePrecision (sourceSummary + childMetadata) feature)
    minimumPrecision

/-! ## Composition with permanent-address allocation -/

/-- Workspace allocation is the common fixed-address transition instantiated
with the source-shaped learned child value. -/
noncomputable def applyWorkspaceChildAction
    {Embedding SlotFeature : Type*}
    (initialSlot holeTypeProjection : Embedding → SlotFeature → ℝ)
    (sourceSummary : Embedding)
    (metadata : ℕ → Embedding)
    (state : FixedAddressState (SlotFeature → ℝ))
    (position arity : ℕ) : FixedAddressState (SlotFeature → ℝ) :=
  state.applyPreviousAction position arity fun argumentIndex ↦
    workspaceChildValue initialSlot holeTypeProjection sourceSummary
      (metadata argumentIndex)

/-- Belief allocation is the same fixed-address transition instantiated with
the natural-coordinate child packet. -/
noncomputable def applyBeliefChildAction
    {Embedding Feature : Type*} [Add Embedding]
    (holeMean holePrecision : Embedding → Feature → ℝ)
    (minimumPrecision : ℝ)
    (sourceSummary : Embedding)
    (metadata : ℕ → Embedding)
    (state : FixedAddressState (Feature → NaturalCoordinatePacket))
    (position arity : ℕ) :
    FixedAddressState (Feature → NaturalCoordinatePacket) :=
  state.applyPreviousAction position arity fun argumentIndex ↦
    beliefChildValue holeMean holePrecision minimumPrecision sourceSummary
      (metadata argumentIndex)

@[simp] theorem applyWorkspaceChildAction_succ_contents
    {Embedding SlotFeature : Type*}
    (initialSlot holeTypeProjection : Embedding → SlotFeature → ℝ)
    (sourceSummary : Embedding) (metadata : ℕ → Embedding)
    (state : FixedAddressState (SlotFeature → ℝ))
    (position arity : ℕ) :
    (applyWorkspaceChildAction initialSlot holeTypeProjection sourceSummary
        metadata state (position + 1) arity).contents =
      state.initializeChildren arity fun argumentIndex ↦
        workspaceChildValue initialSlot holeTypeProjection sourceSummary
          (metadata argumentIndex) := by
  simp [applyWorkspaceChildAction]

@[simp] theorem applyBeliefChildAction_succ_contents
    {Embedding Feature : Type*} [Add Embedding]
    (holeMean holePrecision : Embedding → Feature → ℝ)
    (minimumPrecision : ℝ) (sourceSummary : Embedding)
    (metadata : ℕ → Embedding)
    (state : FixedAddressState (Feature → NaturalCoordinatePacket))
    (position arity : ℕ) :
    (applyBeliefChildAction holeMean holePrecision minimumPrecision
        sourceSummary metadata state (position + 1) arity).contents =
      state.initializeChildren arity fun argumentIndex ↦
        beliefChildValue holeMean holePrecision minimumPrecision sourceSummary
          (metadata argumentIndex) := by
  simp [applyBeliefChildAction]

/-! ## Positive and negative fixtures -/

namespace TypedChildInitializationFixtures

def integerTables : TypedHoleTables ℤ where
  role := fun identifier ↦ identifier
  parent := fun identifier ↦ 10 * identifier
  argument := fun identifier ↦ 100 * identifier
  depth := fun identifier ↦ 1000 * identifier
  maxDepth := 5

/-- Parent identifiers are one-based and both bounded embeddings clamp. -/
theorem typed_child_metadata_exact :
    typedChildMetadata integerTables 2 3 7 8 = 5442 := by
  norm_num [typedChildMetadata, typedHoleVector, integerTables]

/-- Omitting both clamps changes the actual learned metadata address. -/
theorem unclamped_metadata_is_wrong :
    typedChildMetadata integerTables 2 3 7 8 ≠
      integerTables.role 2 + integerTables.parent (3 + 1) +
        integerTables.argument 7 + integerTables.depth 8 := by
  norm_num [typedChildMetadata, typedHoleVector, integerTables]

/-- Using the zero-based action directly instead of the source's one-based
parent identifier changes the child metadata. -/
theorem zero_based_parent_metadata_is_wrong :
    typedChildMetadata integerTables 2 3 7 8 ≠
      typedHoleVector integerTables 2 3 7 8 := by
  norm_num [typedChildMetadata, typedHoleVector, integerTables]

/-- The two workspace affine branches must be combined before `tanh`.
Feeding metadata through the summary branch changes a concrete child. -/
theorem collapsed_workspace_branch_is_wrong :
    workspaceChildValue
        (fun value (_ : Unit) ↦ 2 * value)
        (fun value (_ : Unit) ↦ 3 * value)
        (1 : ℝ) (4 : ℝ) () ≠
      workspaceChildValue
        (fun value (_ : Unit) ↦ 2 * value)
        (fun _ (_ : Unit) ↦ 0)
        (1 + 4 : ℝ) (0 : ℝ) () := by
  simp only [workspaceChildValue]
  intro equality
  have := Real.tanh_injective equality
  norm_num at this

/-- At zero logits and unit floor, the source packet has equal positive and
negative coordinates and total precision `log 2 + 1`. -/
theorem belief_packet_zero_logits_exact :
    let packet := NaturalCoordinatePacket.ofLogits 0 0 1
    packet.positive = packet.negative ∧
      packet.precision = Real.log 2 + 1 := by
  dsimp [NaturalCoordinatePacket.ofLogits, NaturalCoordinatePacket.precision,
    sourceSoftplus]
  rw [Real.exp_zero, Real.sigmoid_zero]
  constructor <;> ring_nf

/-- Dropping the registered minimum precision changes every packet's total
precision by exactly that floor. -/
theorem omitted_minimum_precision_is_wrong :
    (NaturalCoordinatePacket.ofLogits 0 0 1).precision ≠
      (NaturalCoordinatePacket.ofLogits 0 0 0).precision := by
  rw [NaturalCoordinatePacket.ofLogits_precision,
    NaturalCoordinatePacket.ofLogits_precision]
  norm_num

end TypedChildInitializationFixtures

#print axioms typedChildMetadata_eq
#print axioms sourceSoftplus_pos
#print axioms NaturalCoordinatePacket.ofLogits_precision
#print axioms NaturalCoordinatePacket.ofLogits_nonnegative
#print axioms NaturalCoordinatePacket.ofLogits_strength
#print axioms applyWorkspaceChildAction_succ_contents
#print axioms applyBeliefChildAction_succ_contents
#print axioms TypedChildInitializationFixtures.typed_child_metadata_exact
#print axioms TypedChildInitializationFixtures.unclamped_metadata_is_wrong
#print axioms TypedChildInitializationFixtures.zero_based_parent_metadata_is_wrong
#print axioms TypedChildInitializationFixtures.collapsed_workspace_branch_is_wrong
#print axioms TypedChildInitializationFixtures.belief_packet_zero_logits_exact
#print axioms TypedChildInitializationFixtures.omitted_minimum_precision_is_wrong

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
