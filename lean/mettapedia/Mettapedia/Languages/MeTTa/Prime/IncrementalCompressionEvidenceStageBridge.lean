import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceIndexedOSLFBridge
import Mettapedia.Languages.MeTTa.Prime.IncrementalCompressionBoundedRanking

/-!
# Evidence-stage currentness for external incremental-compression guidance

Growing algorithmic-feature evidence has a forward, lax indexed semantics,
while an external learned model is valid only at the exact stage named by its
receipt.  These facts are compatible rather than contradictory: semantic
transport may remain available after growth even though old learned guidance
must fail open to source execution.

This module binds a guidance request to an experiment identity and a finite
observed-source inventory.  Strict growth changes that key.  The main theorem
simultaneously constructs the forward implication-GSLT translation and proves
that a model trained at the earlier key cannot guide preparation at the later
key.
-/

namespace Mettapedia.Languages.MeTTa.Prime
namespace IncrementalCompressionEvidenceStageBridge

open KolmogorovComplexity
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidence
open Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.AlgorithmicFeatureEvidenceGrowth
open IncrementalCompressionOptimizationSelection
open IncrementalCompressionExternalGuidanceReceipt
open IncrementalCompressionExternalArtifactChecker
open IncrementalCompressionRankingArtifact
open IncrementalCompressionBoundedRanking
open NativeTypedOptimizationAdmission
open Mettapedia.OSLF.Framework.IndexedModalFunctor

universe uExperiment uSourceIndex uFeatureIndex uCandidateId uFormula
  uDigest uScore uSource

/-! ## Executable evidence-stage identities -/

/-- An external-model revision key names both the experiment and its exact
finite inventory of observed source indices. -/
structure EvidenceStageRevision
    (ExperimentId : Type uExperiment) (SourceIndex : Type uSourceIndex) where
  experiment : ExperimentId
  observed : Finset SourceIndex
deriving DecidableEq

/-- Bind one complete candidate request to an exact evidence stage. -/
def requestAtEvidenceStage
    {ExperimentId : Type uExperiment} {SourceIndex : Type uSourceIndex}
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    (experiment : ExperimentId) (observed : Finset SourceIndex)
    (family : CandidateFamily CandidateId Formula) :
    GuidanceRequestReceipt CandidateId Formula
      (EvidenceStageRevision ExperimentId SourceIndex) where
  revision := ⟨experiment, observed⟩
  family := family

@[simp]
theorem requestAtEvidenceStage_revision
    {ExperimentId : Type uExperiment} {SourceIndex : Type uSourceIndex}
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    (experiment : ExperimentId) (observed : Finset SourceIndex)
    (family : CandidateFamily CandidateId Formula) :
    (requestAtEvidenceStage experiment observed family).revision =
      (⟨experiment, observed⟩ : EvidenceStageRevision ExperimentId SourceIndex) :=
  rfl

theorem evidenceStageRevision_ne_of_observed_ne
    {ExperimentId : Type uExperiment} {SourceIndex : Type uSourceIndex}
    (experiment : ExperimentId) {earlier later : Finset SourceIndex}
    (strictGrowth : earlier ≠ later) :
    (⟨experiment, earlier⟩ : EvidenceStageRevision ExperimentId SourceIndex) ≠
      ⟨experiment, later⟩ := by
  intro revisionEq
  exact strictGrowth (congrArg EvidenceStageRevision.observed revisionEq)

/-! ## Semantic growth with stage-local learner invalidation -/

/-- Strict source growth preserves the forward implication semantics while
invalidating a learner trained at the earlier stage.  Rejection is fail-open:
Prime executes the source plan rather than treating stale guidance as a
semantic failure. -/
theorem semantic_growth_and_stale_guidance_fallback
    {SourceIndex : Type uSourceIndex} {FeatureIndex : Type uFeatureIndex}
    {ExperimentId : Type uExperiment}
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Digest : Type uDigest} {Score : Type uScore}
    {Source : Type uSource} {U : ConditionalAlgorithm}
    [Fintype SourceIndex] [Fintype FeatureIndex]
    [DecidableEq ExperimentId] [DecidableEq SourceIndex] [DecidableEq Digest]
    [LT Score]
    {trace : TraceProjection Source} {source : Source}
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (experiment : ExperimentId)
    {earlier later : Finset SourceIndex}
    (growth : earlier ⊆ later) (strictGrowth : earlier ≠ later)
    (family : CandidateFamily CandidateId Formula)
    (model : ModelReceipt
      (EvidenceStageRevision ExperimentId SourceIndex) Digest)
    (trainedAtEarlier : model.trainingRevision = ⟨experiment, earlier⟩)
    (calibration : CalibrationReceipt Digest Score)
    (ranking : ReorderingReceipt
      (requestAtEvidenceStage experiment later family).family)
    (guidance : CompressionGuidance U trace source)
    (spec : OptimizationSpec Source)
    (authority : Option (ExactAuthority spec source)) :
    Nonempty (OperationalTranslation
      (E.implicationGSLTAt (↑later : Set SourceIndex))
      (E.implicationGSLTAt (↑earlier : Set SourceIndex))) ∧
      validateAndPrepare spec
        (requestAtEvidenceStage experiment later family)
        model calibration ranking guidance authority = .source := by
  constructor
  · refine ⟨E.implicationGrowthTranslation ?_⟩
    intro index observedEarlier
    exact growth observedEarlier
  · apply validateAndPrepare_of_revision_mismatch
    intro revisionEq
    have stageEq :
        (⟨experiment, earlier⟩ : EvidenceStageRevision ExperimentId SourceIndex) =
          ⟨experiment, later⟩ :=
      trainedAtEarlier.symm.trans revisionEq
    exact strictGrowth (congrArg EvidenceStageRevision.observed stageEq)

/-- The executable raw-artifact route obeys the same indexed boundary.  Strict
evidence growth transports all surviving implication steps forward, while an
artifact trained at the earlier stage is rejected before Prime preparation. -/
theorem semantic_growth_and_stale_raw_guidance_fallback
    {SourceIndex : Type uSourceIndex} {FeatureIndex : Type uFeatureIndex}
    {ExperimentId : Type uExperiment}
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Digest : Type uDigest} {Score : Type uScore}
    {Source : Type uSource} {U : ConditionalAlgorithm}
    [Fintype SourceIndex] [Fintype FeatureIndex]
    [DecidableEq ExperimentId] [DecidableEq SourceIndex]
    [DecidableEq CandidateId] [DecidableEq Digest]
    [LT Score] [DecidableRel (· < · : Score → Score → Prop)]
    {trace : TraceProjection Source} {source : Source}
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (experiment : ExperimentId)
    {earlier later : Finset SourceIndex}
    (growth : earlier ⊆ later) (strictGrowth : earlier ≠ later)
    (family : CandidateFamily CandidateId Formula)
    (model : ModelReceipt
      (EvidenceStageRevision ExperimentId SourceIndex) Digest)
    (trainedAtEarlier : model.trainingRevision = ⟨experiment, earlier⟩)
    (raw : RawExternalGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source)
    (spec : OptimizationSpec Source)
    (authority : Option (ExactAuthority spec source)) :
    Nonempty (OperationalTranslation
      (E.implicationGSLTAt (↑later : Set SourceIndex))
      (E.implicationGSLTAt (↑earlier : Set SourceIndex))) ∧
      ingestAndPrepare spec
        (requestAtEvidenceStage experiment later family)
        model raw guidance authority = .source := by
  constructor
  · refine ⟨E.implicationGrowthTranslation ?_⟩
    intro index observedEarlier
    exact growth observedEarlier
  · have mismatch : model.trainingRevision ≠
        (requestAtEvidenceStage experiment later family).revision := by
      intro revisionEq
      have stageEq :
          (⟨experiment, earlier⟩ :
              EvidenceStageRevision ExperimentId SourceIndex) =
            ⟨experiment, later⟩ :=
        trainedAtEarlier.symm.trans revisionEq
      exact strictGrowth (congrArg EvidenceStageRevision.observed stageEq)
    unfold ingestAndPrepare
    rw [ingestExternalGuidance_of_revision_mismatch
      (requestAtEvidenceStage experiment later family) model raw guidance
      mismatch]

/-- The indexed/lax OSLF map and the fixed-width external-artifact boundary
compose without conflating their responsibilities.  Evidence growth induces a
contravariant lax modal pullback.  Independently, bounded production may reject
an artifact, and any successfully produced artifact is still rejected when its
model receipt names the earlier evidence stage.  Both rejection paths preserve
source execution. -/
theorem semantic_growth_has_lax_modal_pullback_and_stale_bounded_fallback
    {SourceIndex : Type uSourceIndex} {FeatureIndex : Type uFeatureIndex}
    {ExperimentId : Type uExperiment}
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Digest : Type uDigest} {Score : Type uScore}
    {Source : Type uSource} {U : ConditionalAlgorithm}
    [Fintype SourceIndex] [Fintype FeatureIndex]
    [DecidableEq ExperimentId] [DecidableEq SourceIndex]
    [DecidableEq CandidateId] [DecidableEq Digest]
    [LT Score] [DecidableRel (· < · : Score → Score → Prop)]
    {trace : TraceProjection Source} {source : Source}
    (E : FiniteFeatureExperiment SourceIndex FeatureIndex)
    (experiment : ExperimentId)
    {earlier later : Finset SourceIndex}
    (growth : earlier ⊆ later) (strictGrowth : earlier ≠ later)
    (family : CandidateFamily CandidateId Formula)
    (model : ModelReceipt
      (EvidenceStageRevision ExperimentId SourceIndex) Digest)
    (trainedAtEarlier : model.trainingRevision = ⟨experiment, earlier⟩)
    (limit : Nat)
    (raw : RawMeasuredGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source)
    (spec : OptimizationSpec Source)
    (authority : Option (ExactAuthority spec source)) :
    Nonempty (ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject
        (E.implicationGSLTAt (↑earlier : Set SourceIndex)))
      (oslfForwardModalObject
        (E.implicationGSLTAt (↑later : Set SourceIndex)))) ∧
      produceIngestAndPrepareWithinBound limit spec
        (requestAtEvidenceStage experiment later family)
        model raw guidance authority = .source := by
  have growthSet : (↑earlier : Set SourceIndex) ⊆ ↑later := by
    intro index observedEarlier
    exact growth observedEarlier
  let translation := E.implicationGrowthTranslation growthSet
  constructor
  · exact ⟨Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.pullbackLax
      translation⟩
  · have mismatch : model.trainingRevision ≠
        (requestAtEvidenceStage experiment later family).revision := by
      intro revisionEq
      have stageEq :
          (⟨experiment, earlier⟩ :
              EvidenceStageRevision ExperimentId SourceIndex) =
            ⟨experiment, later⟩ :=
        trainedAtEarlier.symm.trans revisionEq
      exact strictGrowth (congrArg EvidenceStageRevision.observed stageEq)
    unfold produceIngestAndPrepareWithinBound
    cases production : produceRawArtifactWithinBound limit raw with
    | none => rfl
    | some produced =>
        simp only
        unfold ingestAndPrepare
        rw [ingestExternalGuidance_of_revision_mismatch
          (requestAtEvidenceStage experiment later family) model produced
          guidance mismatch]

/-! ## Finite controls -/

namespace Canary

def earlySources : Finset Bool := {false}

def laterSources : Finset Bool := {false, true}

theorem earlySources_subset_laterSources : earlySources ⊆ laterSources := by
  decide

theorem earlySources_ne_laterSources : earlySources ≠ laterSources := by
  decide

@[simp]
theorem coe_earlySources : (↑earlySources : Set Bool) = earlyObserved := by
  ext source
  cases source <;> simp [earlySources, earlyObserved]

@[simp]
theorem coe_laterSources : (↑laterSources : Set Bool) = laterObserved := by
  ext source
  cases source <;> simp [laterSources, laterObserved]

def earlyRequest :
    GuidanceRequestReceipt String Nat (EvidenceStageRevision Nat Bool) :=
  requestAtEvidenceStage 17 earlySources
    IncrementalCompressionExternalGuidanceReceipt.Canary.family

def laterRequest :
    GuidanceRequestReceipt String Nat (EvidenceStageRevision Nat Bool) :=
  requestAtEvidenceStage 17 laterSources
    IncrementalCompressionExternalGuidanceReceipt.Canary.family

def ranking : ReorderingReceipt earlyRequest.family where
  order := IncrementalCompressionExternalGuidanceReceipt.Canary.ranking.order
  complete :=
    IncrementalCompressionExternalGuidanceReceipt.Canary.ranking.complete

def model : ModelReceipt (EvidenceStageRevision Nat Bool) Nat where
  modelDigest :=
    IncrementalCompressionExternalGuidanceReceipt.Canary.model.modelDigest
  datasetDigest :=
    IncrementalCompressionExternalGuidanceReceipt.Canary.model.datasetDigest
  trainingReceiptDigest :=
    IncrementalCompressionExternalGuidanceReceipt.Canary.model.trainingReceiptDigest
  trainingRevision := ⟨17, earlySources⟩

/-- Positive control: exact evidence-stage identity admits the same complete,
calibrated reordering receipt. -/
theorem same_stage_guidance_is_admitted :
    (validateExternalGuidance earlyRequest model
      IncrementalCompressionExternalGuidanceReceipt.Canary.calibration
      ranking IncrementalCompressionExternalGuidanceReceipt.Canary.guidance).isSome =
        true := by
  decide

/-- Positive executable control: the raw artifact is admitted at the exact
evidence stage named by the model. -/
theorem same_stage_raw_artifact_is_admitted :
    (ingestExternalGuidance earlyRequest model
      IncrementalCompressionExternalArtifactChecker.Canary.rawArtifact
      IncrementalCompressionExternalGuidanceReceipt.Canary.guidance).isSome =
        true := by
  decide

/-- The exact bounded ranking producer reaches ingestion at the current
evidence stage. -/
theorem same_stage_bounded_artifact_is_ingested :
    (match produceRawArtifactWithinBound uint64MaxNat
        IncrementalCompressionRankingArtifact.Canary.measuredArtifact with
      | none => false
      | some produced =>
          (ingestExternalGuidance earlyRequest model produced
            IncrementalCompressionExternalGuidanceReceipt.Canary.guidance).isSome) =
        true := by
  decide

/-- Strict evidence growth retains a forward semantic map while the unchanged
external model is rejected and Prime falls back to source execution. -/
theorem strict_growth_transports_semantics_and_rejects_stale_guidance :
    Nonempty (OperationalTranslation
      (growthCanaryExperiment.implicationGSLTAt
        (↑laterSources : Set Bool))
      (growthCanaryExperiment.implicationGSLTAt
        (↑earlySources : Set Bool))) ∧
      validateAndPrepare NativeTypedOptimizationNIKBridge.DispatchCanary.spec
        laterRequest model
        IncrementalCompressionExternalGuidanceReceipt.Canary.calibration
        { order := ranking.order
          complete := ranking.complete }
        (IncrementalCompressionOptimizationSelection.Canary.finiteGuidance
          NativeTypedOptimizationNIKBridge.DispatchCanary.candidate.source)
        none = .source := by
  exact semantic_growth_and_stale_guidance_fallback
    growthCanaryExperiment 17 earlySources_subset_laterSources
      earlySources_ne_laterSources
      IncrementalCompressionExternalGuidanceReceipt.Canary.family model rfl
      IncrementalCompressionExternalGuidanceReceipt.Canary.calibration
      { order := ranking.order
        complete := ranking.complete }
      (IncrementalCompressionOptimizationSelection.Canary.finiteGuidance
        NativeTypedOptimizationNIKBridge.DispatchCanary.candidate.source)
      NativeTypedOptimizationNIKBridge.DispatchCanary.spec none

/-- The raw persisted form has the same strict-growth behavior: semantic steps
transport forward, while stale learned guidance fails open. -/
theorem strict_growth_transports_semantics_and_rejects_stale_raw_artifact :
    Nonempty (OperationalTranslation
      (growthCanaryExperiment.implicationGSLTAt
        (↑laterSources : Set Bool))
      (growthCanaryExperiment.implicationGSLTAt
        (↑earlySources : Set Bool))) ∧
      ingestAndPrepare NativeTypedOptimizationNIKBridge.DispatchCanary.spec
        laterRequest model
        IncrementalCompressionExternalArtifactChecker.Canary.rawArtifact
        (IncrementalCompressionOptimizationSelection.Canary.finiteGuidance
          NativeTypedOptimizationNIKBridge.DispatchCanary.candidate.source)
        none = .source := by
  exact semantic_growth_and_stale_raw_guidance_fallback
    growthCanaryExperiment 17 earlySources_subset_laterSources
      earlySources_ne_laterSources
      IncrementalCompressionExternalGuidanceReceipt.Canary.family model rfl
      IncrementalCompressionExternalArtifactChecker.Canary.rawArtifact
      (IncrementalCompressionOptimizationSelection.Canary.finiteGuidance
        NativeTypedOptimizationNIKBridge.DispatchCanary.candidate.source)
      NativeTypedOptimizationNIKBridge.DispatchCanary.spec none

/-- The combined indexed result: strict evidence growth has its lawful lax
modal pullback, while a bounded artifact tied to the old stage cannot guide
the new stage even when exact runtime authority is available. -/
theorem strict_growth_has_lax_modal_map_and_rejects_stale_bounded_artifact :
    Nonempty (ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject
        (growthCanaryExperiment.implicationGSLTAt
          (↑earlySources : Set Bool)))
      (oslfForwardModalObject
        (growthCanaryExperiment.implicationGSLTAt
          (↑laterSources : Set Bool)))) ∧
      produceIngestAndPrepareWithinBound uint64MaxNat
        NativeTypedOptimizationNIKBridge.DispatchCanary.spec
        laterRequest model
        IncrementalCompressionRankingArtifact.Canary.measuredArtifact
        (IncrementalCompressionOptimizationSelection.Canary.finiteGuidance
          NativeTypedOptimizationNIKBridge.DispatchCanary.candidate.source)
        (some NativeTypedOptimizationNIKBridge.DispatchCanary.authority.authority) =
          .source := by
  exact semantic_growth_has_lax_modal_pullback_and_stale_bounded_fallback
    growthCanaryExperiment 17 earlySources_subset_laterSources
      earlySources_ne_laterSources
      IncrementalCompressionExternalGuidanceReceipt.Canary.family model rfl
      uint64MaxNat
      IncrementalCompressionRankingArtifact.Canary.measuredArtifact
      (IncrementalCompressionOptimizationSelection.Canary.finiteGuidance
        NativeTypedOptimizationNIKBridge.DispatchCanary.candidate.source)
      NativeTypedOptimizationNIKBridge.DispatchCanary.spec
      (some NativeTypedOptimizationNIKBridge.DispatchCanary.authority.authority)

/-- Representation overflow is an independent fail-open boundary even at the
current evidence stage and in the presence of exact runtime authority. -/
theorem current_stage_uint64_overflow_falls_back :
    produceIngestAndPrepareWithinBound uint64MaxNat
      NativeTypedOptimizationNIKBridge.DispatchCanary.spec
      earlyRequest model
      IncrementalCompressionBoundedRanking.Canary.hugeMeasuredArtifact
      (IncrementalCompressionOptimizationSelection.Canary.finiteGuidance
        NativeTypedOptimizationNIKBridge.DispatchCanary.candidate.source)
      (some NativeTypedOptimizationNIKBridge.DispatchCanary.authority.authority) =
        .source := by
  apply produceIngestAndPrepareWithinBound_of_production_rejected
  exact IncrementalCompressionBoundedRanking.Canary.huge_exact_tie_rejects_uint64

end Canary

section AxiomAudit

#print axioms evidenceStageRevision_ne_of_observed_ne
#print axioms semantic_growth_and_stale_guidance_fallback
#print axioms semantic_growth_and_stale_raw_guidance_fallback
#print axioms semantic_growth_has_lax_modal_pullback_and_stale_bounded_fallback
#print axioms Canary.same_stage_guidance_is_admitted
#print axioms Canary.same_stage_raw_artifact_is_admitted
#print axioms Canary.same_stage_bounded_artifact_is_ingested
#print axioms Canary.strict_growth_transports_semantics_and_rejects_stale_guidance
#print axioms Canary.strict_growth_transports_semantics_and_rejects_stale_raw_artifact
#print axioms Canary.strict_growth_has_lax_modal_map_and_rejects_stale_bounded_artifact
#print axioms Canary.current_stage_uint64_overflow_falls_back

end AxiomAudit

end IncrementalCompressionEvidenceStageBridge
end Mettapedia.Languages.MeTTa.Prime
