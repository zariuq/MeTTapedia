import Mettapedia.GSLT.LanguageDef.CompiledPlanFiniteSupportCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanFixedHeadIndexCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanEpochSlotCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanFlatHeadCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanGroundCacheCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanGroundDenseCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanActivationViewCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanDenseActivationViewCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanSparseEffectTrail
import Mettapedia.GSLT.LanguageDef.CompiledPlanConstructorGuidedCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanRigidHeadPrefilter
import Mettapedia.GSLT.LanguageDef.CompiledPlanRigidCoordinateCompilation
import Mettapedia.GSLT.LanguageDef.IndexedInstructionStreamCompilation
import Mettapedia.GSLT.LanguageDef.ContiguousSliceCompilation

/-!
# Composed certified optimization pipeline for compiled plans

One local typed-program recognizer drives six concrete products:

* an exactly admitted `CGP1` packet;
* an order-preserving fixed-head/arity rule index;
* packed dense variable support for every rule.
* maximal immutable ground-subterm caches;
* optional positional heads whose immediate arguments are variable slots.
* one finite query-local slot-buffer capacity shared by every rule attempt;
* rigid-coordinate plans selected independently inside each fixed-head bucket;
* optional exact bounded-slot heads for direct ground matching;
* optional substitution views admitted from range and capture analysis;
* direct bounded-slot matching over admitted substitution views;
* recursive rigid incompatibility rejection before matcher allocation;
* constructor-guided child-equation scheduling for open queries.
* generated numeric instruction decoding across arbitrary source chunks.
* immutable sequence packing into checked contiguous-slice arenas.
* sparse optional-effect trails with an exact local zero-cold recognizer.

The first two are retained in the persistent artifact.  Packed support is a
transient structural-admission carrier, so its certificate is exposed as a
derived invariant rather than retained after the packet is admitted.  This
matches the generic runtime: persistent rule buckets survive loading, while
one packed support buffer is reused and then released.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanOptimizationPipeline

universe u v

open CompiledPlanLowering
open CompiledPlanFiniteSupportCompilation
open CompiledPlanFixedHeadIndexCompilation
open CompiledPlanTermSemantics
open FiniteRuleIndexCompilation

/-- Per-rule semantic analyses consumed by the generic physical runtime.
Neither analysis is required for admission: ground caching is total, while
flat-head lowering remains explicitly optional. -/
structure RuleAnalysis where
  cachedHead : CompiledPlanGroundCacheCompilation.CachedTerm
  cachedBody : List CompiledPlanGroundCacheCompilation.CachedTerm
  flatHead : Option CompiledPlanFlatHeadCompilation.FlatHead
  groundDenseHead : Option
    CompiledPlanGroundDenseCompilation.AdmittedGroundHead
  deriving DecidableEq, Repr

def analyzeRule (rule : TypedRule) : RuleAnalysis :=
  { cachedHead :=
      CompiledPlanGroundCacheCompilation.compileTerm rule.head
    cachedBody :=
      rule.body.map CompiledPlanGroundCacheCompilation.compileTerm
    flatHead := CompiledPlanFlatHeadCompilation.compile? rule.head
    groundDenseHead :=
      CompiledPlanGroundDenseCompilation.admit?
        rule.variableCount rule.head }

/-- Derive one optional rigid-coordinate plan per exact outer-head bucket.
The bucket list and every occurrence list remain in source order. -/
def compileDispatchPlans (index : BucketIndex OuterKey TypedRule) :
    List (OuterKey ×
      Option CompiledPlanRigidCoordinateCompilation.Plan) :=
  index.map fun bucket =>
    (bucket.1,
      CompiledPlanRigidCoordinateCompilation.compile?
        bucket.1.arity bucket.2)

/-- Derive one optional substitution view for every generated body goal.
The complete source-head inventory is an input to the recognizer, so a
variable-headed or capture-demanding consumer makes the relevant view fail
closed. -/
def compileActivationViews (source : TypedProgram) :
    List (List (Option
      CompiledPlanActivationViewCompilation.ActivationViewPlan)) :=
  let consumerHeads := source.map TypedRule.head
  source.map fun producer =>
    producer.body.map fun body =>
      CompiledPlanActivationViewCompilation.compile?
        producer body consumerHeads

/-- Persistent products derived from one admitted typed program. -/
structure Artifact where
  packet : List UInt8
  ruleIndex : BucketIndex OuterKey TypedRule
  dispatchPlans : List (OuterKey ×
    Option CompiledPlanRigidCoordinateCompilation.Plan)
  ruleAnalyses : List RuleAnalysis
  activationViews : List (List (Option
    CompiledPlanActivationViewCompilation.ActivationViewPlan))
  variableSlotCapacity : Nat
  deriving DecidableEq, Repr

/-- Compile only the locally recognized fragment.  Every downstream stage is
independently partial and therefore remains fail-closed. -/
def compile? (source : TypedProgram) : Option Artifact :=
  if source.locallySupported then do
    let packet <- CompiledPlanLowering.compileBytes? source
    let ruleIndex <- FiniteRuleIndexCompilation.compile?
      ruleOuterKey? source
    some
      { packet
        ruleIndex
        dispatchPlans := compileDispatchPlans ruleIndex
        ruleAnalyses := source.map analyzeRule
        activationViews := compileActivationViews source
        variableSlotCapacity :=
          CompiledPlanEpochSlotCompilation.maximumVariableCount source }
  else
    none

/-- The composed pipeline is complete on exactly the same local fragment as
the physical packet lowering. -/
theorem compile?_complete
    (source : TypedProgram) (supported : source.locallySupported = true) :
    ∃ artifact, compile? source = some artifact := by
  obtain ⟨ruleIndex, indexCompiled⟩ :=
    compileIndex_complete_of_locallySupported source supported
  let packet := CompiledPlanWireFormat.encodeProgram
    (CompiledPlanLowering.compile source)
  let artifact : Artifact :=
    { packet := packet
      ruleIndex := ruleIndex
      dispatchPlans := compileDispatchPlans ruleIndex
      ruleAnalyses := source.map analyzeRule
      activationViews := compileActivationViews source
      variableSlotCapacity :=
        CompiledPlanEpochSlotCompilation.maximumVariableCount source }
  refine ⟨artifact, ?_⟩
  simp [artifact, packet, compile?, supported,
    CompiledPlanLowering.compileBytes?_complete source supported,
    indexCompiled]

/-- Successful composition retains the exact independently checked packet and
the exact order-preserving rule index; neither stage may silently fall back. -/
theorem compile?_success
    (source : TypedProgram) (artifact : Artifact)
    (success : compile? source = some artifact) :
    source.locallySupported = true ∧
      artifact.packet = CompiledPlanWireFormat.encodeProgram
        (CompiledPlanLowering.compile source) ∧
      FiniteRuleIndexCompilation.compile? ruleOuterKey? source =
        some artifact.ruleIndex ∧
      artifact.dispatchPlans = compileDispatchPlans artifact.ruleIndex ∧
      artifact.ruleAnalyses = source.map analyzeRule ∧
      artifact.activationViews = compileActivationViews source ∧
      artifact.variableSlotCapacity =
        CompiledPlanEpochSlotCompilation.maximumVariableCount source := by
  unfold compile? at success
  cases supported : source.locallySupported with
  | false => simp [supported] at success
  | true =>
      rw [if_pos supported] at success
      rw [CompiledPlanLowering.compileBytes?_complete source supported]
        at success
      cases indexCompiled :
          FiniteRuleIndexCompilation.compile? ruleOuterKey? source with
      | none => simp [indexCompiled] at success
      | some ruleIndex =>
          simp [indexCompiled] at success
          subst artifact
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every rule in a successfully compiled artifact also satisfies the packed
dense-support invariant consumed transiently by physical admission. -/
theorem packedSupport_of_compile?_success
    (source : TypedProgram) (artifact : Artifact)
    (success : compile? source = some artifact) :
    ∀ rule ∈ source,
      packedDenseVariables rule.variableCount.toNat
        (ruleUsedVariables rule) = true := by
  have supported := (compile?_success source artifact success).1
  have rulesSupported : source.all TypedRule.locallySupported = true := by
    simp [TypedProgram.locallySupported] at supported
    aesop
  intro rule member
  exact packedDenseVariables_of_rule_locallySupported rule
    ((List.all_eq_true.mp rulesSupported) rule member)

/-- Persistent indexed lookup in a successful artifact remains exactly the
ordered source scan for every generated key. -/
theorem lookup_eq_sourceCandidates_of_compile?_success
    (source : TypedProgram) (artifact : Artifact)
    (success : compile? source = some artifact) (query : OuterKey) :
    lookup query artifact.ruleIndex =
      sourceCandidates ruleOuterKey? source query := by
  exact lookup_compiledIndex_eq_sourceCandidates source artifact.ruleIndex
    (compile?_success source artifact success).2.2.1 query

/-! ## Exact semantics and cost of the retained rule analyses -/

/-- A generated activation view has exactly the same ordered matching
observation as fully instantiating the body and invoking the source matcher. -/
theorem activationView_match_exact
    (sourceEnvironment : Substitution)
    (source pattern : CompiledPlanAdmission.Term)
    (patternEnvironment :
      CompiledPlanGroundDenseCompilation.SourceEnvironment) :
    CompiledPlanActivationViewCompilation.matchView sourceEnvironment
        source pattern patternEnvironment =
      match instantiateTerm sourceEnvironment source with
      | none => none
      | some target =>
          CompiledPlanGroundDenseCompilation.matchSource
            pattern target patternEnvironment :=
  CompiledPlanActivationViewCompilation.matchView_eq_materialized
    sourceEnvironment source pattern patternEnvironment

/-- For a same-head consumer accepted by the generated recognizer, direct
view traversal strictly removes the complete temporary source-body
materialization. -/
theorem activationView_strict_materialization_reduction
    (producer : TypedRule) (source consumer : CompiledPlanAdmission.Term)
    (consumerHeads : List CompiledPlanAdmission.Term)
    (plan : CompiledPlanActivationViewCompilation.ActivationViewPlan)
    (accepted : CompiledPlanActivationViewCompilation.compile?
      producer source consumerHeads = some plan)
    (member : consumer ∈ consumerHeads)
    (sameHead :
      CompiledPlanActivationViewCompilation.fixedApplicationHead? source =
        CompiledPlanActivationViewCompilation.fixedApplicationHead?
          consumer) :
    CompiledPlanActivationViewCompilation.compiledCapturedMaterializations
        plan consumer <
      CompiledPlanActivationViewCompilation.sourceWholeTermMaterializations
        plan :=
  CompiledPlanActivationViewCompilation.compiledCapturedMaterializations_lt_source
    producer source consumer consumerHeads plan accepted member sameHead

/-- When both local recognizers compose, bounded matching directly over an
activation view has exactly the independently specified view observation. -/
theorem denseActivationView_match_exact
    (producer : TypedRule) (source consumer : CompiledPlanAdmission.Term)
    (consumerHeads : List CompiledPlanAdmission.Term) (width : UInt32)
    (plan :
      CompiledPlanDenseActivationViewCompilation.Plan width)
    (accepted : CompiledPlanDenseActivationViewCompilation.compile?
      producer source consumerHeads consumer width = some plan)
    (sourceEnvironment : Substitution)
    (sourceConsumerEnvironment :
      CompiledPlanGroundDenseCompilation.SourceEnvironment)
    (denseConsumerEnvironment :
      CompiledPlanGroundDenseCompilation.DenseEnvironment width)
    (related :
      CompiledPlanGroundDenseCompilation.decodeDense width
          denseConsumerEnvironment = sourceConsumerEnvironment) :
    Option.map
        (CompiledPlanGroundDenseCompilation.decodeDense width)
        (CompiledPlanDenseActivationViewCompilation.matchDenseView
          sourceEnvironment source plan.consumer denseConsumerEnvironment) =
      CompiledPlanActivationViewCompilation.matchView
        sourceEnvironment source consumer sourceConsumerEnvironment := by
  exact CompiledPlanDenseActivationViewCompilation.match_compile?_some
    producer source consumerHeads consumer width plan accepted
      sourceEnvironment sourceConsumerEnvironment denseConsumerEnvironment
      related

/-- The composed recognizer removes the complete intermediate source-body
materialization without introducing a hidden capture allocation. -/
theorem denseActivationView_strict_materialization_reduction
    (producer : TypedRule) (source consumer : CompiledPlanAdmission.Term)
    (consumerHeads : List CompiledPlanAdmission.Term) (width : UInt32)
    (plan : CompiledPlanDenseActivationViewCompilation.Plan width)
    (accepted : CompiledPlanDenseActivationViewCompilation.compile?
      producer source consumerHeads consumer width = some plan) :
    CompiledPlanDenseActivationViewCompilation.compiledCapturedMaterializations
        plan consumer <
      CompiledPlanActivationViewCompilation.sourceWholeTermMaterializations
        plan.activation := by
  exact
    CompiledPlanDenseActivationViewCompilation.compiledMaterializations_lt_source
      producer source consumerHeads consumer width plan accepted

/-- The optimizer scheduler may retain the direct view on a raw compiled tail
and force it otherwise without changing dense matching semantics. -/
theorem denseActivationView_scheduled_match_exact
    (laterGenerated : List α) (laterExternal : List β)
    (sourceEnvironment : Substitution)
    (source : CompiledPlanAdmission.Term)
    (pattern : CompiledPlanGroundDenseCompilation.DenseTerm width)
    (patternEnvironment :
      CompiledPlanGroundDenseCompilation.DenseEnvironment width) :
    CompiledPlanDenseActivationViewCompilation.matchDenseViewScheduled
        laterGenerated laterExternal sourceEnvironment source pattern
        patternEnvironment =
      match instantiateTerm sourceEnvironment source with
      | none => none
      | some target =>
          CompiledPlanGroundDenseCompilation.matchDense pattern target
            patternEnvironment := by
  exact
    CompiledPlanDenseActivationViewCompilation.matchDenseViewScheduled_eq_materialized
      laterGenerated laterExternal sourceEnvironment source pattern
        patternEnvironment

/-- A raw compiled tail licenses direct view retention with a strict reduction
from one complete source materialization to zero. -/
theorem denseActivationView_rawTail_strict_materialization_reduction :
    CompiledPlanDenseActivationViewCompilation.scheduledSourceMaterializations
        ([] : List α) ([] : List β) < 1 :=
  CompiledPlanDenseActivationViewCompilation.rawTail_strict_materialization_reduction

theorem ruleAnalyses_length_of_compile?_success
    (source : TypedProgram) (artifact : Artifact)
    (success : compile? source = some artifact) :
    artifact.ruleAnalyses.length = source.length := by
  rw [(compile?_success source artifact success).2.2.2.2.1]
  simp

/-- The persistent artifact records the exact one-buffer width derived from
the complete rule inventory. -/
theorem variableSlotCapacity_of_compile?_success
    (source : TypedProgram) (artifact : Artifact)
    (success : compile? source = some artifact) :
  artifact.variableSlotCapacity =
      CompiledPlanEpochSlotCompilation.maximumVariableCount source :=
  (compile?_success source artifact success).2.2.2.2.2.2

/-- The retained activation-view matrix is generated solely from the admitted
program and its complete consumer-head inventory. -/
theorem activationViews_of_compile?_success
    (source : TypedProgram) (artifact : Artifact)
    (success : compile? source = some artifact) :
    artifact.activationViews = compileActivationViews source :=
  (compile?_success source artifact success).2.2.2.2.2.1

/-- Activation analysis preserves the outer rule inventory and the body-goal
inventory of every rule, whether a particular view is admitted or refused. -/
theorem compileActivationViews_lengths (source : TypedProgram) :
    (compileActivationViews source).map List.length =
      source.map (fun rule => rule.body.length) := by
  simp [compileActivationViews]

/-- Every successful artifact receives exactly the coordinate plans derived
from its already-certified head/arity buckets. -/
theorem dispatchPlans_of_compile?_success
    (source : TypedProgram) (artifact : Artifact)
    (success : compile? source = some artifact) :
    artifact.dispatchPlans = compileDispatchPlans artifact.ruleIndex :=
  (compile?_success source artifact success).2.2.2.1

/-- The same admitted bucket inventory drives the reset-and-reuse scratch
program, whose snapshots retain every coordinate key in bucket order. -/
theorem dispatchScratch_exact (artifact : Artifact) :
    ReusableSlotBufferCompilation.executeReusable
        (CompiledPlanRigidCoordinateCompilation.dispatchScratchTransactions
          artifact.ruleIndex) =
      CompiledPlanRigidCoordinateCompilation.dispatchScratchSnapshots
        artifact.ruleIndex := by
  exact
    CompiledPlanRigidCoordinateCompilation.executeReusable_dispatchScratchTransactions
      artifact.ruleIndex

/-- Reusing the selector scratch allocation never allocates more buffers than
the per-bucket source realization. -/
theorem dispatchScratchAllocationCount_le (artifact : Artifact) :
    ReusableSlotBufferCompilation.reusableAllocationCount
        (CompiledPlanRigidCoordinateCompilation.dispatchScratchTransactions
          artifact.ruleIndex) ≤
      ReusableSlotBufferCompilation.freshAllocationCount
        (CompiledPlanRigidCoordinateCompilation.dispatchScratchTransactions
          artifact.ruleIndex) := by
  exact
    CompiledPlanRigidCoordinateCompilation.dispatchScratchAllocationCount_le
      artifact.ruleIndex

/-- The runtime may discard a candidate rejected by recursive rigid
compatibility: no pair of source substitutions could make that rule head and
query equal to a common ground term. -/
theorem rigidPrefilter_rejection_sound
    (ruleHead query : CompiledPlanAdmission.Term)
    (rejected :
      CompiledPlanRigidHeadPrefilter.compatibleTerm ruleHead query = false) :
    ¬∃ ruleSubstitution querySubstitution target,
      instantiateTerm ruleSubstitution ruleHead = some target ∧
        instantiateTerm querySubstitution query = some target :=
  CompiledPlanRigidHeadPrefilter.no_commonGroundInstance_of_incompatibleTerm
    ruleHead query rejected

/-- Recursive rigid prefiltering cannot increase the number of general matcher
attempts scheduled from an admitted candidate list. -/
theorem rigidPrefilter_matcherAttempts_le
    (query : CompiledPlanAdmission.Term)
    (candidateHeads : List CompiledPlanAdmission.Term) :
    CompiledPlanRigidHeadPrefilter.filteredMatcherAttempts
        query candidateHeads <=
      CompiledPlanRigidHeadPrefilter.sourceMatcherAttempts candidateHeads :=
  CompiledPlanRigidHeadPrefilter.filteredMatcherAttempts_le
    query candidateHeads

/-- When the generated recognizer exposes equal constructors, direct child
equation scheduling is exactly one ordinary Martelli--Montanari unifier step. -/
theorem constructorGuided_unify_exact
    (fuel : Nat)
    (ruleHead query : CompiledPlanAdmission.Term)
    (rest equations :
      List CompiledPlanConstructorGuidedCompilation.Equation)
    (accepted : CompiledPlanConstructorGuidedCompilation.decompose?
      ruleHead query rest = some equations) :
    Mettapedia.Logic.LP.unifyFuel (fuel + 1)
        ((CompiledPlanConstructorGuidedCompilation.encodeTerm .rule ruleHead,
          CompiledPlanConstructorGuidedCompilation.encodeTerm .query query) ::
          rest) =
      Mettapedia.Logic.LP.unifyFuel fuel equations :=
  CompiledPlanConstructorGuidedCompilation.unifyFuel_decompose?
    fuel ruleHead query rest equations accepted

/-- Every admitted direct decomposition strictly removes the temporary
rule-side constructor materialization. -/
theorem constructorGuided_strict_materialization_reduction
    (admitted :
      CompiledPlanConstructorGuidedCompilation.AdmittedDecomposition) :
    CompiledPlanConstructorGuidedCompilation.compiledConstructorMaterializations
        admitted <
      CompiledPlanConstructorGuidedCompilation.sourceConstructorMaterializations
        admitted :=
  CompiledPlanConstructorGuidedCompilation.compiledConstructorMaterializations_lt_source
    admitted

/-! The indexed-instruction compiler is a sibling product of the same staged
pipeline: its generated plan comes from local byte-language declarations, not
from the finite-Horn rule inventory. -/

def compileIndexedInstructions? :=
  IndexedInstructionStreamCompilation.admit?

/-- Successful indexed-stream admission is an exact certificate for the
independently executable source decoder. -/
theorem compileIndexedInstructions?_success
    (plan : IndexedInstructionStreamCompilation.Plan)
    (chunks : List (List UInt8))
    (admitted : IndexedInstructionStreamCompilation.AdmittedProgram)
    (success : compileIndexedInstructions? plan chunks = some admitted) :
    IndexedInstructionStreamCompilation.compile? plan chunks =
      .ok admitted.instructions := by
  unfold compileIndexedInstructions? at success
  unfold IndexedInstructionStreamCompilation.admit? at success
  split at success
  · simp at success
  · cases success
    assumption

/-- The emitted state machine may consume source chunks incrementally without
changing the flat-stream observation. -/
theorem indexedInstructions_chunking_exact
    (plan : IndexedInstructionStreamCompilation.Plan)
    (state : IndexedInstructionStreamCompilation.DecoderState)
    (chunks : List (List UInt8)) :
    IndexedInstructionStreamCompilation.runChunksFrom plan state chunks =
      IndexedInstructionStreamCompilation.runBytesFrom
        plan state chunks.flatten :=
  IndexedInstructionStreamCompilation.runChunksFrom_eq_flatten
    plan state chunks

/-- Immutable locally owned sequences may share one flat carrier without
changing any sequence observation. -/
theorem contiguousSlices_exact (sequences : List (List α)) :
    ContiguousSliceCompilation.unpack
        (ContiguousSliceCompilation.pack sequences) = sequences :=
  ContiguousSliceCompilation.unpack_pack sequences

/-- Transaction-local scratch appended after a watermark can be discarded in
constant time while every retained prefix handle keeps the same meaning. -/
theorem contiguousSlices_watermark_exact
    (storage scratch : List α)
    (slice : ContiguousSliceCompilation.Slice) :
    slice.read
        (ContiguousSliceCompilation.reset (storage ++ scratch)
          (ContiguousSliceCompilation.watermark storage)) =
      slice.read storage :=
  ContiguousSliceCompilation.Slice.read_reset_append
    storage scratch slice

/-! Optional effects are another sibling product of the staged pipeline.  The
semantic checkpoint type is independent of any particular runtime effect;
the generated machine supplies the local trace inspected by `effectFree`. -/

def compileSparseTrail
    {Logical : Type u} {Effect : Type v}
    (checkpoints : List
      (CompiledPlanSparseEffectTrail.Checkpoint Logical Effect)) :
    CompiledPlanSparseEffectTrail.SparseTrail Logical Effect :=
  CompiledPlanSparseEffectTrail.pack checkpoints

/-- Sparse trail lowering preserves the complete ordered checkpoint
observation. -/
theorem compileSparseTrail_exact
    (checkpoints : List
      (CompiledPlanSparseEffectTrail.Checkpoint Logical Effect)) :
    CompiledPlanSparseEffectTrail.unpack
        (compileSparseTrail checkpoints) = some checkpoints :=
  CompiledPlanSparseEffectTrail.unpack_pack checkpoints

/-- The generated no-effect recognizer is exactly the condition under which
the compiled physical trail has no cold payloads. -/
theorem compileSparseTrail_zeroCold_iff
    (checkpoints : List
      (CompiledPlanSparseEffectTrail.Checkpoint Logical Effect)) :
    (compileSparseTrail checkpoints).cold = [] ↔
      CompiledPlanSparseEffectTrail.effectFree checkpoints = true :=
  CompiledPlanSparseEffectTrail.pack_cold_empty_iff_effectFree checkpoints

/-- Lower the same semantic trail to the forward-array carrier used by the C
runtime.  Watermarks are generated from the preceding cold-array length. -/
def compileMarkedSparseTrail
    {Logical : Type u} {Effect : Type v}
    (checkpoints : List
      (CompiledPlanSparseEffectTrail.Checkpoint Logical Effect)) :
    CompiledPlanSparseEffectTrail.MarkedTrail Logical Effect :=
  CompiledPlanSparseEffectTrail.packMarked checkpoints

/-- The concrete forward-array lowering preserves the complete ordered
checkpoint observation. -/
theorem compileMarkedSparseTrail_exact
    (checkpoints : List
      (CompiledPlanSparseEffectTrail.Checkpoint Logical Effect)) :
    CompiledPlanSparseEffectTrail.unpackMarked
        (compileMarkedSparseTrail checkpoints) = some checkpoints :=
  CompiledPlanSparseEffectTrail.unpackMarked_packMarked checkpoints

/-- The concrete C carrier has an empty cold array under exactly the same
local no-effect certificate as the abstract sparse carrier. -/
theorem compileMarkedSparseTrail_zeroCold_iff
    (checkpoints : List
      (CompiledPlanSparseEffectTrail.Checkpoint Logical Effect)) :
    (compileMarkedSparseTrail checkpoints).cold = [] ↔
      CompiledPlanSparseEffectTrail.effectFree checkpoints = true :=
  CompiledPlanSparseEffectTrail.packMarked_cold_empty_iff_effectFree
    checkpoints

/-- Any emitted coordinate plan retains exactly the source occurrences of its
outer bucket. -/
theorem mem_compileDispatchPlans_some
    (index : BucketIndex OuterKey TypedRule)
    (key : OuterKey)
    (plan : CompiledPlanRigidCoordinateCompilation.Plan)
    (member : (key, some plan) ∈ compileDispatchPlans index) :
    ∃ rules,
      (key, rules) ∈ index ∧
        plan.entries.map
          CompiledPlanRigidCoordinateCompilation.Entry.rule = rules := by
  induction index with
  | nil => simp [compileDispatchPlans] at member
  | cons bucket index inductionHypothesis =>
      obtain ⟨storedKey, rules⟩ := bucket
      simp only [compileDispatchPlans, List.map_cons, List.mem_cons] at member
      rcases member with same | later
      · have keyEquality := congrArg Prod.fst same
        have planEquality := congrArg Prod.snd same
        simp only at keyEquality planEquality
        subst key
        exact ⟨rules, by simp,
          CompiledPlanRigidCoordinateCompilation.compile?_rules
            storedKey.arity rules plan planEquality.symm⟩
      · obtain ⟨laterRules, laterMember, exactRules⟩ :=
          inductionHypothesis later
        exact ⟨laterRules, by simp [laterMember], exactRules⟩

/-- Every rule-local variable occurrence fits the artifact's single finite
query-local slot buffer. -/
theorem compileRuleSlots?_complete_of_compile?_success
    (source : TypedProgram) (artifact : Artifact)
    (success : compile? source = some artifact)
    (rule : TypedRule) (member : rule ∈ source) :
    ∃ slots : List (Fin artifact.variableSlotCapacity),
      CompiledPlanEpochSlotCompilation.compileRuleSlots?
        artifact.variableSlotCapacity rule = some slots := by
  rw [variableSlotCapacity_of_compile?_success source artifact success]
  exact CompiledPlanEpochSlotCompilation.compileRuleSlots?_complete_of_program
    source rule (compile?_success source artifact success).1 member

/-- The cached head retained for every rule has exactly the ordinary
typed-plan instantiation semantics. -/
theorem analyzeRule_cachedHead_exact
    (rule : TypedRule) (substitution : Substitution) :
    CompiledPlanGroundCacheCompilation.executeTerm substitution
        (analyzeRule rule).cachedHead =
      instantiateTerm substitution rule.head := by
  exact CompiledPlanGroundCacheCompilation.executeTerm_compileTerm
    rule.head substitution

/-- The cached body preserves every goal, its order, and its multiplicity. -/
theorem analyzeRule_cachedBody_exact
    (rule : TypedRule) (substitution : Substitution) :
    (analyzeRule rule).cachedBody.map
        (CompiledPlanGroundCacheCompilation.executeTerm substitution) =
      rule.body.map (instantiateTerm substitution) := by
  simp only [analyzeRule, List.map_map]
  apply List.map_congr_left
  intro term member
  exact CompiledPlanGroundCacheCompilation.executeTerm_compileTerm
    term substitution

/-- Optional positional lowering is used only when its recognizer produced
the exact source-head certificate. -/
theorem analyzeRule_flatHead_exact
    (rule : TypedRule) (substitution : Substitution)
    (flat : CompiledPlanFlatHeadCompilation.FlatHead)
    (accepted : (analyzeRule rule).flatHead = some flat) :
    CompiledPlanFlatHeadCompilation.execute substitution flat =
      instantiateTerm substitution rule.head := by
  exact CompiledPlanFlatHeadCompilation.execute_eq_instantiateTerm_of_compile?
    substitution rule.head flat accepted

/-- Local dense support makes the direct ground matcher available for every
rule accepted by the common source recognizer. -/
theorem analyzeRule_groundDenseHead_complete
    (rule : TypedRule) (supported : rule.locallySupported = true) :
    ∃ admitted,
      (analyzeRule rule).groundDenseHead = some admitted := by
  have combinedBound :=
    CompiledPlanEpochSlotCompilation.ruleUsedVariables_all_lt_of_locallySupported
      rule supported
  have headBound :
      (termUsedVariables rule.head).all
          (fun slot => slot < rule.variableCount.toNat) = true := by
    unfold ruleUsedVariables at combinedBound
    rw [List.all_append, Bool.and_eq_true] at combinedBound
    exact combinedBound.1
  obtain ⟨admitted, admittedEq⟩ :=
    CompiledPlanGroundDenseCompilation.admit?_complete_of_all_lt
      rule.variableCount rule.head headBound
  exact ⟨admitted, by simpa [analyzeRule] using admittedEq⟩

/-- Whenever the local analyzer emitted a bounded head, its direct ground
matcher has exactly the independent source-matcher observation. -/
theorem analyzeRule_groundDenseHead_exact
    (rule : TypedRule)
    (admitted : CompiledPlanGroundDenseCompilation.AdmittedGroundHead)
    (accepted : (analyzeRule rule).groundDenseHead = some admitted)
    (target : GroundTerm) :
    Option.map
        (CompiledPlanGroundDenseCompilation.decodeDense admitted.width)
        (CompiledPlanGroundDenseCompilation.matchDense admitted.compiled target
          (CompiledPlanGroundDenseCompilation.emptyDenseEnvironment
            admitted.width)) =
      CompiledPlanGroundDenseCompilation.matchSource rule.head target
        CompiledPlanGroundDenseCompilation.emptySourceEnvironment := by
  exact CompiledPlanGroundDenseCompilation.match_admit?_some
    rule.variableCount rule.head admitted (by
      simpa [analyzeRule] using accepted) target

/-- Direct dense matching strictly removes the intermediate source-head
materialization admitted by this analyzer. -/
theorem analyzeRule_groundDenseHead_strict_materialization_reduction
    (admitted : CompiledPlanGroundDenseCompilation.AdmittedGroundHead) :
    CompiledPlanGroundDenseCompilation.compiledHeadMaterializations admitted <
      CompiledPlanGroundDenseCompilation.sourceHeadMaterializations admitted :=
  CompiledPlanGroundDenseCompilation.compiledHeadMaterializations_lt_source
    admitted

/-- Caching never increases the number of nodes dynamically materialized for
a rule head. -/
theorem analyzeRule_cachedHead_cost_le (rule : TypedRule) :
    CompiledPlanGroundCacheCompilation.dynamicNodeCount
        (analyzeRule rule).cachedHead ≤
      CompiledPlanGroundCacheCompilation.sourceNodeCount rule.head := by
  exact CompiledPlanGroundCacheCompilation.dynamicNodeCount_compile_le
    rule.head

/-! ## Positive and negative composition canaries -/

private def unaryRule (name head : UInt8) : TypedRule :=
  { name := [name]
    head := .application [head] (.cons (.variable 0) .nil)
    body := []
    variableCount := 1 }

private def independentProgram : TypedProgram :=
  [unaryRule 1 10, unaryRule 2 20, unaryRule 3 10]

/-- A multi-bucket program passes the whole composed compiler. -/
example : (compile? independentProgram).isSome = true := by
  have supported : independentProgram.locallySupported = true := by
    decide
  obtain ⟨artifact, compiled⟩ := compile?_complete independentProgram supported
  rw [compiled]
  rfl

/-- Empty programs are rejected by the shared local recognizer. -/
example : (compile? []).isSome = false := by
  decide

/-- A headless rule cannot gain an index through composition. -/
example :
    (compile?
      [{ name := [4]
         head := .symbol [30]
         body := []
         variableCount := 0 }]).isSome = false := by
  decide

/-- A variable hole remains rejected before packed admission. -/
example :
    (compile?
      [{ name := [5]
         head := .application [40] (.cons (.variable 1) .nil)
         body := []
         variableCount := 2 }]).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanOptimizationPipeline
