import Mettapedia.Languages.MeTTa.Prime.IncrementalCompressionExternalGuidanceReceipt

/-!
# Executable checking of external incremental-compression artifacts

The proof-level external-guidance boundary stores candidate completeness as a
permutation and calibration quality as four strict proper-score inequalities.
Persisted artifacts do not arrive with those Lean proofs.  This module checks
the raw candidate order and raw scores and constructs the proof-bearing
receipts only when every check succeeds.

The checker is deliberately narrow.  It does not infer semantic optimization
authority, alter the candidate family, or weaken revision validation.  A raw
artifact that is incomplete, duplicated, poorly calibrated, or stale yields no
guidance, and Prime retains ordinary source execution.
-/

namespace Mettapedia.Languages.MeTTa.Prime
namespace IncrementalCompressionExternalArtifactChecker

open KolmogorovComplexity
open IncrementalCompressionOptimizationSelection
open IncrementalCompressionExternalGuidanceReceipt
open NativeTypedOptimizationAdmission

universe uCandidateId uFormula uRevision uDigest uScore uSource

/-! ## Raw calibration evidence -/

/-- The eight persisted score values used by the existing four-part proper
score gate.  Unlike `ProperScoreGate`, this structure contains no proofs. -/
structure RawProperScores (Score : Type uScore) where
  exactModelLogLoss : Score
  exactBaselineLogLoss : Score
  exactModelBrier : Score
  exactBaselineBrier : Score
  repeatedModelMeanLogLoss : Score
  repeatedBaselineMeanLogLoss : Score
  repeatedModelMeanBrier : Score
  repeatedBaselineMeanBrier : Score

namespace RawProperScores

/-- The proposition decided by the executable proper-score checker. -/
def Passes {Score : Type uScore} [LT Score]
    (scores : RawProperScores Score) : Prop :=
  scores.exactModelLogLoss < scores.exactBaselineLogLoss ∧
  scores.exactModelBrier < scores.exactBaselineBrier ∧
  scores.repeatedModelMeanLogLoss < scores.repeatedBaselineMeanLogLoss ∧
  scores.repeatedModelMeanBrier < scores.repeatedBaselineMeanBrier

/-- Check all four strict proper-score improvements and retain their proofs. -/
def check {Score : Type uScore} [LT Score]
    [DecidableRel (· < · : Score → Score → Prop)]
    (scores : RawProperScores Score) : Option (ProperScoreGate Score) :=
  if exact_logLoss_improves :
      scores.exactModelLogLoss < scores.exactBaselineLogLoss then
    if exact_brier_improves :
        scores.exactModelBrier < scores.exactBaselineBrier then
      if repeated_logLoss_improves :
          scores.repeatedModelMeanLogLoss <
            scores.repeatedBaselineMeanLogLoss then
        if repeated_brier_improves :
            scores.repeatedModelMeanBrier <
              scores.repeatedBaselineMeanBrier then
          some
            { exactModelLogLoss := scores.exactModelLogLoss
              exactBaselineLogLoss := scores.exactBaselineLogLoss
              exactModelBrier := scores.exactModelBrier
              exactBaselineBrier := scores.exactBaselineBrier
              repeatedModelMeanLogLoss := scores.repeatedModelMeanLogLoss
              repeatedBaselineMeanLogLoss :=
                scores.repeatedBaselineMeanLogLoss
              repeatedModelMeanBrier := scores.repeatedModelMeanBrier
              repeatedBaselineMeanBrier :=
                scores.repeatedBaselineMeanBrier
              exact_logLoss_improves := exact_logLoss_improves
              exact_brier_improves := exact_brier_improves
              repeated_logLoss_improves := repeated_logLoss_improves
              repeated_brier_improves := repeated_brier_improves }
        else none
      else none
    else none
  else none

/-- The executable check succeeds exactly when all four inequalities hold. -/
theorem check_isSome_iff_passes
    {Score : Type uScore} [LT Score]
    [DecidableRel (· < · : Score → Score → Prop)]
    (scores : RawProperScores Score) :
    scores.check.isSome = true ↔ scores.Passes := by
  unfold check Passes
  by_cases h₁ : scores.exactModelLogLoss < scores.exactBaselineLogLoss
  · by_cases h₂ : scores.exactModelBrier < scores.exactBaselineBrier
    · by_cases h₃ : scores.repeatedModelMeanLogLoss <
        scores.repeatedBaselineMeanLogLoss
      · by_cases h₄ : scores.repeatedModelMeanBrier <
          scores.repeatedBaselineMeanBrier
        · simp [h₁, h₂, h₃, h₄]
        · simp [h₁, h₂, h₃, h₄]
      · simp [h₁, h₂, h₃]
    · simp [h₁, h₂]
  · simp [h₁]

end RawProperScores

/-- Raw persisted calibration coordinates and score values. -/
structure RawCalibrationArtifact (Digest : Type uDigest) (Score : Type uScore) where
  modelDigest : Digest
  datasetDigest : Digest
  trainingReceiptDigest : Digest
  properScores : RawProperScores Score

namespace RawCalibrationArtifact

/-- Turn raw calibration data into a proof-bearing calibration receipt. -/
def check {Digest : Type uDigest} {Score : Type uScore} [LT Score]
    [DecidableRel (· < · : Score → Score → Prop)]
    (raw : RawCalibrationArtifact Digest Score) :
    Option (CalibrationReceipt Digest Score) :=
  match raw.properScores.check with
  | none => none
  | some properScores =>
      some
        { modelDigest := raw.modelDigest
          datasetDigest := raw.datasetDigest
          trainingReceiptDigest := raw.trainingReceiptDigest
          properScores := properScores }

/-- Calibration admission is equivalent to the raw proper-score predicate. -/
theorem check_isSome_iff_passes
    {Digest : Type uDigest} {Score : Type uScore} [LT Score]
    [DecidableRel (· < · : Score → Score → Prop)]
    (raw : RawCalibrationArtifact Digest Score) :
    raw.check.isSome = true ↔ raw.properScores.Passes := by
  rw [← RawProperScores.check_isSome_iff_passes]
  unfold RawCalibrationArtifact.check
  cases raw.properScores.check <;> simp

end RawCalibrationArtifact

/-! ## Complete raw external artifacts -/

/-- The externally persisted portion of one ranking artifact.  Candidate
formulas remain in the trusted request; the artifact carries only stable IDs
and calibration data. -/
structure RawExternalGuidanceArtifact
    (CandidateId : Type uCandidateId) (Digest : Type uDigest)
    (Score : Type uScore) where
  order : List CandidateId
  calibration : RawCalibrationArtifact Digest Score

/-- The result of checking a raw artifact against one exact request. -/
structure CheckedExternalArtifact
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} (Digest : Type uDigest) (Score : Type uScore)
    [LT Score]
    (request : GuidanceRequestReceipt CandidateId Formula Revision) where
  ranking : ReorderingReceipt request.family
  calibration : CalibrationReceipt Digest Score

/-- Check candidate-family completeness and calibration quality.  The
permutation decision rejects both missing and duplicated candidate IDs. -/
def checkExternalArtifact
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    [DecidableEq CandidateId]
    [DecidableRel (· < · : Score → Score → Prop)]
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (raw : RawExternalGuidanceArtifact CandidateId Digest Score) :
    Option (CheckedExternalArtifact Digest Score request) :=
  if complete : raw.order.Perm request.family.ids then
    match raw.calibration.check with
    | none => none
    | some calibration =>
        some
          { ranking := { order := raw.order, complete := complete }
            calibration := calibration }
  else none

namespace CheckedExternalArtifact

/-- A checked artifact contains every requested candidate exactly once. -/
theorem mem_ranking_iff_source
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {request : GuidanceRequestReceipt CandidateId Formula Revision}
    (checked : CheckedExternalArtifact Digest Score request)
    (candidate : CandidateId) :
    candidate ∈ checked.ranking.order ↔ candidate ∈ request.family.ids :=
  checked.ranking.mem_iff_source candidate

/-- Checked candidate order has the same cardinality as the source family. -/
theorem ranking_length_eq_source
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {request : GuidanceRequestReceipt CandidateId Formula Revision}
    (checked : CheckedExternalArtifact Digest Score request) :
    checked.ranking.order.length = request.family.ids.length :=
  checked.ranking.length_eq_source

end CheckedExternalArtifact

/-! ## Identity validation and fail-open Prime preparation -/

/-- An admitted raw artifact packages the dynamically constructed calibration
receipt with the existing exact-identity validation result. -/
structure IngestedExternalGuidance
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    (Score : Type uScore) [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest) where
  calibration : CalibrationReceipt Digest Score
  validated : ValidatedExternalGuidance
    (U := U) (trace := trace) (source := source) request model calibration

/-- Check raw evidence and then validate its exact revision and digest square. -/
def ingestExternalGuidance
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq CandidateId] [DecidableEq Revision] [DecidableEq Digest]
    [DecidableRel (· < · : Score → Score → Prop)]
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (raw : RawExternalGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source) :
    Option (IngestedExternalGuidance
      (U := U) (trace := trace) (source := source) Score request model) :=
  match checkExternalArtifact request raw with
  | none => none
  | some checked =>
      match validateExternalGuidance request model checked.calibration
          checked.ranking guidance with
      | none => none
      | some validated =>
          some { calibration := checked.calibration, validated := validated }

/-- Run Prime preparation only after successful raw ingestion.  Rejection at
either checking layer returns the source plan. -/
def ingestAndPrepare
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq CandidateId] [DecidableEq Revision] [DecidableEq Digest]
    [DecidableRel (· < · : Score → Score → Prop)]
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (raw : RawExternalGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source)
    (authority : Option (ExactAuthority spec source)) :
    ExecutionPlan spec source :=
  match ingestExternalGuidance request model raw guidance with
  | none => .source
  | some ingested =>
      prepareWithGuidance spec trace source
        (some ingested.validated.guidance) authority

/-- Raw admission cannot change the source observation, regardless of whether
checking, identity validation, recognition, or authority succeeds. -/
theorem observe_ingestAndPrepare
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq CandidateId] [DecidableEq Revision] [DecidableEq Digest]
    [DecidableRel (· < · : Score → Score → Prop)]
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (raw : RawExternalGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source)
    (authority : Option (ExactAuthority spec source)) :
    (ingestAndPrepare spec request model raw guidance authority).observe =
      spec.observeSource source := by
  unfold ingestAndPrepare
  cases ingestExternalGuidance request model raw guidance with
  | none => rfl
  | some ingested =>
      exact observe_prepareWithGuidance spec trace source
        (some ingested.validated.guidance) authority

/-- A raw family/calibration rejection cannot reach native preparation. -/
theorem ingestAndPrepare_of_artifact_rejected
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq CandidateId] [DecidableEq Revision] [DecidableEq Digest]
    [DecidableRel (· < · : Score → Score → Prop)]
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (raw : RawExternalGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source)
    (authority : Option (ExactAuthority spec source))
    (rejected : checkExternalArtifact request raw = none) :
    ingestAndPrepare spec request model raw guidance authority = .source := by
  simp [ingestAndPrepare, ingestExternalGuidance, rejected]

/-- Raw calibration and ranking evidence never manufactures native authority.
Even an admitted artifact retains source execution when authority is absent. -/
theorem ingestAndPrepare_without_authority
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq CandidateId] [DecidableEq Revision] [DecidableEq Digest]
    [DecidableRel (· < · : Score → Score → Prop)]
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (raw : RawExternalGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source) :
    ingestAndPrepare spec request model raw guidance none = .source := by
  unfold ingestAndPrepare
  cases ingestExternalGuidance request model raw guidance <;> rfl

/-- A model trained at another stage remains unusable even when the raw family
and calibration values themselves pass. -/
theorem ingestExternalGuidance_of_revision_mismatch
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq CandidateId] [DecidableEq Revision] [DecidableEq Digest]
    [DecidableRel (· < · : Score → Score → Prop)]
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (raw : RawExternalGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source)
    (mismatch : model.trainingRevision ≠ request.revision) :
    ingestExternalGuidance request model raw guidance = none := by
  unfold ingestExternalGuidance
  cases hchecked : checkExternalArtifact request raw with
  | none => rfl
  | some checked =>
      simp [validateExternalGuidance, mismatch]

/-! ## Executable controls -/

namespace Canary

open IncrementalCompressionExternalGuidanceReceipt.Canary

def rawProperScores : RawProperScores Nat where
  exactModelLogLoss := 2
  exactBaselineLogLoss := 3
  exactModelBrier := 4
  exactBaselineBrier := 5
  repeatedModelMeanLogLoss := 6
  repeatedBaselineMeanLogLoss := 7
  repeatedModelMeanBrier := 8
  repeatedBaselineMeanBrier := 9

def rawCalibration : RawCalibrationArtifact Nat Nat where
  modelDigest := 101
  datasetDigest := 202
  trainingReceiptDigest := 303
  properScores := rawProperScores

def rawArtifact : RawExternalGuidanceArtifact String Nat Nat where
  order := ["right", "left"]
  calibration := rawCalibration

/-- Positive control: raw values construct the complete proof-bearing receipt
and pass the exact identity square. -/
theorem aligned_raw_artifact_is_ingested :
    (ingestExternalGuidance request model rawArtifact guidance).isSome = true := by
  decide

def missingCandidateArtifact : RawExternalGuidanceArtifact String Nat Nat where
  order := ["right"]
  calibration := rawCalibration

/-- Negative control: a proper subfamily is rejected. -/
theorem missing_candidate_is_rejected :
    checkExternalArtifact request missingCandidateArtifact = none := by
  decide

def duplicateCandidateArtifact : RawExternalGuidanceArtifact String Nat Nat where
  order := ["right", "right"]
  calibration := rawCalibration

/-- Negative control: duplicating one candidate cannot mask a dropped one. -/
theorem duplicate_candidate_is_rejected :
    checkExternalArtifact request duplicateCandidateArtifact = none := by
  decide

def failedScoreArtifact : RawExternalGuidanceArtifact String Nat Nat where
  order := ["right", "left"]
  calibration :=
    { rawCalibration with
      properScores :=
        { rawProperScores with
          exactModelLogLoss := 4
          exactBaselineLogLoss := 3 } }

/-- Negative control: one failed proper-score comparison rejects calibration. -/
theorem failed_proper_score_is_rejected :
    checkExternalArtifact request failedScoreArtifact = none := by
  decide

/-- Negative control: a well-formed raw artifact is stale after revision
growth and therefore produces no admitted guidance. -/
theorem changed_revision_rejects_raw_artifact :
    ingestExternalGuidance { request with revision := 8 }
      model rawArtifact guidance = none := by
  decide

end Canary

section AxiomAudit

#print axioms RawProperScores.check_isSome_iff_passes
#print axioms RawCalibrationArtifact.check_isSome_iff_passes
#print axioms CheckedExternalArtifact.mem_ranking_iff_source
#print axioms CheckedExternalArtifact.ranking_length_eq_source
#print axioms observe_ingestAndPrepare
#print axioms ingestAndPrepare_of_artifact_rejected
#print axioms ingestAndPrepare_without_authority
#print axioms ingestExternalGuidance_of_revision_mismatch
#print axioms Canary.aligned_raw_artifact_is_ingested
#print axioms Canary.missing_candidate_is_rejected
#print axioms Canary.duplicate_candidate_is_rejected
#print axioms Canary.failed_proper_score_is_rejected
#print axioms Canary.changed_revision_rejects_raw_artifact

end AxiomAudit

end IncrementalCompressionExternalArtifactChecker
end Mettapedia.Languages.MeTTa.Prime
