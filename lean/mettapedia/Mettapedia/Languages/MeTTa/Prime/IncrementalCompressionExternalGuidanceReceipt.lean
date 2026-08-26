import Mettapedia.Languages.MeTTa.Prime.IncrementalCompressionOptimizationSelection

/-!
# Revision-bound external incremental-compression guidance

An external learner may rank one complete candidate family, but the ranking is
usable only at the exact package, dataset, model, and training receipt for
which it was calibrated.  This module gives that boundary an executable Lean
form and connects it to Prime's existing fail-open compression-guided
preparation.

Candidate completeness is proof-relevant: a ranking stores a list permutation,
not a Boolean assertion that it is complete.  Calibration likewise contains
strict held-out proper-score inequalities rather than an unvalidated status
flag.  Runtime validation checks only the receipt identities.  Semantic
authority and source fallback remain the responsibility of the existing Prime
optimization admission layer.
-/

namespace Mettapedia.Languages.MeTTa.Prime
namespace IncrementalCompressionExternalGuidanceReceipt

open KolmogorovComplexity
open IncrementalCompressionOptimizationSelection
open NativeTypedOptimizationAdmission

universe uCandidateId uFormula uRevision uDigest uScore uSource

/-! ## Complete candidate families and reorder-only guidance -/

/-- A complete source-ordered candidate family with unique stable identities. -/
structure CandidateFamily (CandidateId : Type uCandidateId)
    (Formula : Type uFormula) where
  candidates : List (CandidateId × Formula)
  uniqueIds : (candidates.map Prod.fst).Nodup

namespace CandidateFamily

def ids {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    (family : CandidateFamily CandidateId Formula) : List CandidateId :=
  family.candidates.map Prod.fst

end CandidateFamily

/-- A ranker may return only a permutation of the complete source identities. -/
structure ReorderingReceipt
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    (family : CandidateFamily CandidateId Formula) where
  order : List CandidateId
  complete : order.Perm family.ids

namespace ReorderingReceipt

theorem mem_iff_source
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {family : CandidateFamily CandidateId Formula}
    (receipt : ReorderingReceipt family) (candidate : CandidateId) :
    candidate ∈ receipt.order ↔ candidate ∈ family.ids :=
  receipt.complete.mem_iff

theorem length_eq_source
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {family : CandidateFamily CandidateId Formula}
    (receipt : ReorderingReceipt family) :
    receipt.order.length = family.ids.length :=
  receipt.complete.length_eq

theorem order_nodup
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {family : CandidateFamily CandidateId Formula}
    (receipt : ReorderingReceipt family) : receipt.order.Nodup := by
  exact receipt.complete.nodup_iff.mpr family.uniqueIds

end ReorderingReceipt

/-! ## Model and calibration receipts -/

/-- The identities embedded in one persisted model artifact. -/
structure ModelReceipt (Revision : Type uRevision) (Digest : Type uDigest) where
  modelDigest : Digest
  datasetDigest : Digest
  trainingReceiptDigest : Digest
  trainingRevision : Revision

/-- Exact-model and repeated-split held-out proper-score evidence. -/
structure ProperScoreGate (Score : Type uScore) [LT Score] where
  exactModelLogLoss : Score
  exactBaselineLogLoss : Score
  exactModelBrier : Score
  exactBaselineBrier : Score
  repeatedModelMeanLogLoss : Score
  repeatedBaselineMeanLogLoss : Score
  repeatedModelMeanBrier : Score
  repeatedBaselineMeanBrier : Score
  exact_logLoss_improves : exactModelLogLoss < exactBaselineLogLoss
  exact_brier_improves : exactModelBrier < exactBaselineBrier
  repeated_logLoss_improves :
    repeatedModelMeanLogLoss < repeatedBaselineMeanLogLoss
  repeated_brier_improves :
    repeatedModelMeanBrier < repeatedBaselineMeanBrier

/-- Calibration evidence names the exact model, dataset, and training receipt
whose proper-score gate was evaluated. -/
structure CalibrationReceipt (Digest : Type uDigest) (Score : Type uScore)
    [LT Score] where
  modelDigest : Digest
  datasetDigest : Digest
  trainingReceiptDigest : Digest
  properScores : ProperScoreGate Score

/-- One complete candidate request at one exact package revision. -/
structure GuidanceRequestReceipt
    (CandidateId : Type uCandidateId) (Formula : Type uFormula)
    (Revision : Type uRevision) where
  revision : Revision
  family : CandidateFamily CandidateId Formula

/-! ## Executable receipt validation -/

/-- Evidence returned only after every external receipt coordinate agrees.
It contains guidance, ranking, and identity agreement, but no semantic
optimization authority. -/
structure ValidatedExternalGuidance
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (calibration : CalibrationReceipt Digest Score) where
  ranking : ReorderingReceipt request.family
  guidance : CompressionGuidance U trace source
  revision_eq : model.trainingRevision = request.revision
  model_eq : calibration.modelDigest = model.modelDigest
  dataset_eq : calibration.datasetDigest = model.datasetDigest
  trainingReceipt_eq :
    calibration.trainingReceiptDigest = model.trainingReceiptDigest

/-- Validate the exact package/model/calibration square.  Candidate-family
completeness and proper-score inequalities are already retained as proofs in
their respective receipts. -/
def validateExternalGuidance
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq Revision] [DecidableEq Digest]
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (calibration : CalibrationReceipt Digest Score)
    (ranking : ReorderingReceipt request.family)
    (guidance : CompressionGuidance U trace source) :
    Option (ValidatedExternalGuidance
      (U := U) (trace := trace) (source := source)
      request model calibration) :=
  if revision_eq : model.trainingRevision = request.revision then
    if model_eq : calibration.modelDigest = model.modelDigest then
      if dataset_eq : calibration.datasetDigest = model.datasetDigest then
        if trainingReceipt_eq :
            calibration.trainingReceiptDigest = model.trainingReceiptDigest then
          some
            { ranking := ranking
              guidance := guidance
              revision_eq := revision_eq
              model_eq := model_eq
              dataset_eq := dataset_eq
              trainingReceipt_eq := trainingReceipt_eq }
        else none
      else none
    else none
  else none

/-- Prime consumes only the compression witness inside a validated external
receipt.  Native authority and the recognizer still control preparation. -/
def prepareWithExternalGuidance
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    {request : GuidanceRequestReceipt CandidateId Formula Revision}
    {model : ModelReceipt Revision Digest}
    {calibration : CalibrationReceipt Digest Score}
    (spec : OptimizationSpec Source)
    (validated : Option (ValidatedExternalGuidance
      (U := U) (trace := trace) (source := source) request model calibration))
    (authority : Option (ExactAuthority spec source)) :
    ExecutionPlan spec source :=
  prepareWithGuidance spec trace source
    (validated.map fun receipt => receipt.guidance) authority

/-- The composed external route validates receipts and then delegates to the
existing fail-open Prime preparation boundary. -/
def validateAndPrepare
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq Revision] [DecidableEq Digest]
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (calibration : CalibrationReceipt Digest Score)
    (ranking : ReorderingReceipt request.family)
    (guidance : CompressionGuidance U trace source)
    (authority : Option (ExactAuthority spec source)) :
    ExecutionPlan spec source :=
  prepareWithExternalGuidance spec
    (validateExternalGuidance request model calibration ranking guidance)
    authority

/-- Every validated or rejected external route retains the ordinary source
observation. -/
theorem observe_prepareWithExternalGuidance
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    {request : GuidanceRequestReceipt CandidateId Formula Revision}
    {model : ModelReceipt Revision Digest}
    {calibration : CalibrationReceipt Digest Score}
    (spec : OptimizationSpec Source)
    (validated : Option (ValidatedExternalGuidance
      (U := U) (trace := trace) (source := source) request model calibration))
    (authority : Option (ExactAuthority spec source)) :
    (prepareWithExternalGuidance spec validated authority).observe =
      spec.observeSource source :=
  observe_prepareWithGuidance spec trace source _ authority

/-- A model trained at another package revision cannot reach native
preparation; validation returns no guidance and execution stays on source. -/
theorem validateAndPrepare_of_revision_mismatch
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq Revision] [DecidableEq Digest]
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (calibration : CalibrationReceipt Digest Score)
    (ranking : ReorderingReceipt request.family)
    (guidance : CompressionGuidance U trace source)
    (authority : Option (ExactAuthority spec source))
    (mismatch : model.trainingRevision ≠ request.revision) :
    validateAndPrepare spec request model calibration ranking guidance authority =
      .source := by
  simp [validateAndPrepare, validateExternalGuidance, mismatch,
    prepareWithExternalGuidance]

/-- Even at the right package revision, a calibration receipt naming another
model forces source fallback. -/
theorem validateAndPrepare_of_model_mismatch
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq Revision] [DecidableEq Digest]
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (calibration : CalibrationReceipt Digest Score)
    (ranking : ReorderingReceipt request.family)
    (guidance : CompressionGuidance U trace source)
    (authority : Option (ExactAuthority spec source))
    (revision_eq : model.trainingRevision = request.revision)
    (mismatch : calibration.modelDigest ≠ model.modelDigest) :
    validateAndPrepare spec request model calibration ranking guidance authority =
      .source := by
  simp [validateAndPrepare, validateExternalGuidance, revision_eq, mismatch,
    prepareWithExternalGuidance]

/-! ## Finite controls -/

namespace Canary

def family : CandidateFamily String Nat where
  candidates := [("left", 11), ("right", 22)]
  uniqueIds := by decide

def request : GuidanceRequestReceipt String Nat Nat where
  revision := 7
  family := family

def ranking : ReorderingReceipt request.family where
  order := ["right", "left"]
  complete := by decide

def model : ModelReceipt Nat Nat where
  modelDigest := 101
  datasetDigest := 202
  trainingReceiptDigest := 303
  trainingRevision := 7

def properScores : ProperScoreGate Nat where
  exactModelLogLoss := 2
  exactBaselineLogLoss := 3
  exactModelBrier := 4
  exactBaselineBrier := 5
  repeatedModelMeanLogLoss := 6
  repeatedBaselineMeanLogLoss := 7
  repeatedModelMeanBrier := 8
  repeatedBaselineMeanBrier := 9
  exact_logLoss_improves := by decide
  exact_brier_improves := by decide
  repeated_logLoss_improves := by decide
  repeated_brier_improves := by decide

def calibration : CalibrationReceipt Nat Nat where
  modelDigest := 101
  datasetDigest := 202
  trainingReceiptDigest := 303
  properScores := properScores

def guidance : CompressionGuidance
    finiteCompressionAlgorithm
    (IncrementalCompressionOptimizationSelection.Canary.fourBitTrace
      (Source := Unit)) () :=
  IncrementalCompressionOptimizationSelection.Canary.finiteGuidance ()

/-- Positive control: a complete permutation with aligned model and
calibration receipts is admitted. -/
theorem aligned_external_guidance_is_admitted :
    (validateExternalGuidance request model calibration ranking guidance).isSome =
      true := by
  decide

/-- Negative control: forward package growth makes the old model stale. -/
theorem changed_revision_rejects_external_guidance :
    validateExternalGuidance { request with revision := 8 }
        model calibration
        { order := ranking.order
          complete := ranking.complete }
        guidance = none := by
  decide

/-- Reorder-only guidance retains both candidates, including the one moved to
the end of the ranking. -/
theorem reordered_family_drops_no_candidate :
    "left" ∈ ranking.order ↔ "left" ∈ request.family.ids :=
  ranking.mem_iff_source "left"

end Canary

section AxiomAudit

#print axioms ReorderingReceipt.mem_iff_source
#print axioms ReorderingReceipt.length_eq_source
#print axioms ReorderingReceipt.order_nodup
#print axioms observe_prepareWithExternalGuidance
#print axioms validateAndPrepare_of_revision_mismatch
#print axioms validateAndPrepare_of_model_mismatch
#print axioms Canary.aligned_external_guidance_is_admitted
#print axioms Canary.changed_revision_rejects_external_guidance
#print axioms Canary.reordered_family_drops_no_candidate

end AxiomAudit

end IncrementalCompressionExternalGuidanceReceipt
end Mettapedia.Languages.MeTTa.Prime
