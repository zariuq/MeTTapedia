import Mettapedia.Languages.MeTTa.Prime.IncrementalCompressionRankingArtifact

/-!
# Bounded exact ranking for incremental-compression artifacts

The reference compression-rate ordering uses natural-number cross products.
That specification is exact, but a fixed-width implementation must establish
that both products fit before evaluating the comparator.  This module gives
the admission layer for such implementations.

`checkedMulAt` checks multiplication with division before forming the product.
The list preflight applies that check to both cross products for every possible
comparison.  An admitted list is then ranked by the existing exact stable
sorter; the result is definitionally the unbounded reference result.  Failed
preflight produces no ranking artifact, and the composed Prime preparation
returns the source plan.
-/

namespace Mettapedia.Languages.MeTTa.Prime
namespace IncrementalCompressionBoundedRanking

open IncrementalCompressionOptimizationSelection
open IncrementalCompressionExternalGuidanceReceipt
open IncrementalCompressionExternalArtifactChecker
open IncrementalCompressionRankingArtifact
open NativeTypedOptimizationAdmission

universe uCandidateId uFormula uRevision uDigest uScore uSource

/-! ## Division-guarded multiplication -/

/-- Largest natural number representable by `UInt64`. -/
def uint64MaxNat : Nat := UInt64.size - 1

/-- Multiply only after division has established that the product is at most
`limit`.  The zero branch avoids division by zero. -/
def checkedMulAt (limit left right : Nat) : Option Nat :=
  if left = 0 then
    some 0
  else if right ≤ limit / left then
    some (left * right)
  else none

/-- Division-guarded multiplication succeeds exactly when the mathematical
product fits the bound. -/
theorem checkedMulAt_isSome_iff (limit left right : Nat) :
    (checkedMulAt limit left right).isSome = true ↔
      left * right ≤ limit := by
  by_cases leftZero : left = 0
  · subst left
    simp [checkedMulAt]
  · have leftPos : 0 < left := Nat.pos_of_ne_zero leftZero
    simp [checkedMulAt, leftZero, Nat.le_div_iff_mul_le leftPos, Nat.mul_comm]

/-- A successful bounded multiplication returns the exact natural-number
product, never a saturated or wrapped approximation. -/
theorem checkedMulAt_eq_some_iff
    (limit left right product : Nat) :
    checkedMulAt limit left right = some product ↔
      product = left * right ∧ left * right ≤ limit := by
  by_cases leftZero : left = 0
  · subst left
    simp [checkedMulAt, eq_comm]
  · have leftPos : 0 < left := Nat.pos_of_ne_zero leftZero
    by_cases fits : right ≤ limit / left
    · have productFits : left * right ≤ limit := by
        simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le leftPos).mp fits
      simp [checkedMulAt, leftZero, fits, productFits, eq_comm]
    · have doesNotFit : ¬ left * right ≤ limit := by
        intro productFits
        apply fits
        exact (Nat.le_div_iff_mul_le leftPos).mpr (by
          simpa [Nat.mul_comm] using productFits)
      simp [checkedMulAt, leftZero, fits, doesNotFit]

/-! ## Pairwise and whole-list preflight -/

/-- Both products required to compare `left` and `right` fit `limit`. -/
def PairFitsAt
    {CandidateId : Type uCandidateId} (limit : Nat)
    (left right : CompressionMeasurement CandidateId) : Prop :=
  right.savedBits * left.ordinaryLength ≤ limit ∧
    left.savedBits * right.ordinaryLength ≤ limit

/-- Executable pair preflight.  Each multiplication is guarded independently. -/
def pairFitsAt?
    {CandidateId : Type uCandidateId} (limit : Nat)
    (left right : CompressionMeasurement CandidateId) : Bool :=
  (checkedMulAt limit right.savedBits left.ordinaryLength).isSome &&
    (checkedMulAt limit left.savedBits right.ordinaryLength).isSome

/-- The executable pair preflight recognizes precisely `PairFitsAt`. -/
theorem pairFitsAt?_eq_true_iff
    {CandidateId : Type uCandidateId} (limit : Nat)
    (left right : CompressionMeasurement CandidateId) :
    pairFitsAt? limit left right = true ↔ PairFitsAt limit left right := by
  simp only [pairFitsAt?, Bool.and_eq_true,
    checkedMulAt_isSome_iff, PairFitsAt]

/-- Every comparison that stable sorting might request fits `limit`. -/
def ComparisonSafeAt
    {CandidateId : Type uCandidateId} (limit : Nat)
    (measurements : List (CompressionMeasurement CandidateId)) : Prop :=
  ∀ left ∈ measurements, ∀ right ∈ measurements,
    PairFitsAt limit left right

/-- Executable whole-list preflight. -/
def comparisonSafeAt?
    {CandidateId : Type uCandidateId} (limit : Nat)
    (measurements : List (CompressionMeasurement CandidateId)) : Bool :=
  measurements.all fun left =>
    measurements.all fun right => pairFitsAt? limit left right

/-- Whole-list preflight succeeds exactly when every possible exact comparison
fits the selected representation bound. -/
theorem comparisonSafeAt?_eq_true_iff
    {CandidateId : Type uCandidateId} (limit : Nat)
    (measurements : List (CompressionMeasurement CandidateId)) :
    comparisonSafeAt? limit measurements = true ↔
      ComparisonSafeAt limit measurements := by
  simp only [comparisonSafeAt?, List.all_eq_true,
    pairFitsAt?_eq_true_iff, ComparisonSafeAt]

/-! ## Bounded ranking and production -/

/-- Run the exact stable ranking only after every potential comparison passes
bounded-product preflight. -/
def rankWithinBound
    {CandidateId : Type uCandidateId} (limit : Nat)
    (measurements : List (CompressionMeasurement CandidateId)) :
    Option (List (CompressionMeasurement CandidateId)) :=
  if comparisonSafeAt? limit measurements then
    some (rankMeasurements measurements)
  else none

/-- Safe bounded ranking is exactly the unbounded natural-number reference
ranking. -/
theorem rankWithinBound_eq_some_iff
    {CandidateId : Type uCandidateId} (limit : Nat)
    (measurements ranked : List (CompressionMeasurement CandidateId)) :
    rankWithinBound limit measurements = some ranked ↔
      ComparisonSafeAt limit measurements ∧
        ranked = rankMeasurements measurements := by
  by_cases safe : comparisonSafeAt? limit measurements = true
  · have safeSpec :=
      (comparisonSafeAt?_eq_true_iff limit measurements).mp safe
    simp [rankWithinBound, safe, safeSpec, eq_comm]
  · have unsafeSpec : ¬ ComparisonSafeAt limit measurements := by
      intro safeSpec
      exact safe ((comparisonSafeAt?_eq_true_iff limit measurements).mpr safeSpec)
    simp [rankWithinBound, safe, unsafeSpec]

/-- Every admitted bounded ranking retains the full checked family. -/
theorem rankWithinBound_perm
    {CandidateId : Type uCandidateId} {limit : Nat}
    {measurements ranked : List (CompressionMeasurement CandidateId)}
    (accepted : rankWithinBound limit measurements = some ranked) :
    ranked.Perm measurements := by
  have exactReference :=
    (rankWithinBound_eq_some_iff limit measurements ranked).mp accepted
  rw [exactReference.2]
  exact rankMeasurements_perm measurements

/-- Check denominators, preflight bounded cross products, and emit the same
raw artifact as the unbounded producer when admission succeeds. -/
def produceRawArtifactWithinBound
    {CandidateId : Type uCandidateId} {Digest : Type uDigest}
    {Score : Type uScore}
    (limit : Nat)
    (raw : RawMeasuredGuidanceArtifact CandidateId Digest Score) :
    Option (RawExternalGuidanceArtifact CandidateId Digest Score) :=
  match checkMeasurements raw.measurements with
  | none => none
  | some checked =>
      match rankWithinBound limit checked with
      | none => none
      | some ranked =>
          some
            { order := ranked.map (·.candidate)
              calibration := raw.calibration }

/-- Success of bounded production implies byte-for-byte structural equality
with the unbounded exact producer. -/
theorem produceRawArtifactWithinBound_success_implies_reference
    {CandidateId : Type uCandidateId} {Digest : Type uDigest}
    {Score : Type uScore} {limit : Nat}
    {raw : RawMeasuredGuidanceArtifact CandidateId Digest Score}
    {produced : RawExternalGuidanceArtifact CandidateId Digest Score}
    (accepted : produceRawArtifactWithinBound limit raw = some produced) :
    produceRawArtifact raw = some produced := by
  unfold produceRawArtifactWithinBound at accepted
  cases checkedResult : checkMeasurements raw.measurements with
  | none => simp [checkedResult] at accepted
  | some checked =>
      cases rankedResult : rankWithinBound limit checked with
      | none => simp [checkedResult, rankedResult] at accepted
      | some ranked =>
          have exactReference :=
            (rankWithinBound_eq_some_iff limit checked ranked).mp rankedResult
          simp [checkedResult, rankedResult] at accepted
          subst produced
          simp [produceRawArtifact, checkedResult, rankedCandidateIds,
            exactReference.2]

/-- Bounded production cannot add, delete, or duplicate a measured candidate. -/
theorem produceRawArtifactWithinBound_order_perm_measurement_ids
    {CandidateId : Type uCandidateId} {Digest : Type uDigest}
    {Score : Type uScore} {limit : Nat}
    {raw : RawMeasuredGuidanceArtifact CandidateId Digest Score}
    {produced : RawExternalGuidanceArtifact CandidateId Digest Score}
    (accepted : produceRawArtifactWithinBound limit raw = some produced) :
    produced.order.Perm (raw.measurements.map (·.candidate)) :=
  produceRawArtifact_order_perm_measurement_ids
    (produceRawArtifactWithinBound_success_implies_reference accepted)

/-- Bounded production retains the caller's calibration payload exactly. -/
theorem produceRawArtifactWithinBound_calibration
    {CandidateId : Type uCandidateId} {Digest : Type uDigest}
    {Score : Type uScore} {limit : Nat}
    {raw : RawMeasuredGuidanceArtifact CandidateId Digest Score}
    {produced : RawExternalGuidanceArtifact CandidateId Digest Score}
    (accepted : produceRawArtifactWithinBound limit raw = some produced) :
    produced.calibration = raw.calibration :=
  produceRawArtifact_calibration
    (produceRawArtifactWithinBound_success_implies_reference accepted)

/-! ## Fail-open composition with Prime preparation -/

/-- Produce a bounded exact artifact and run the existing external checker and
Prime preparation.  Any denominator or overflow rejection returns the source
plan before learned guidance can affect execution. -/
def produceIngestAndPrepareWithinBound
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : KolmogorovComplexity.ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq CandidateId] [DecidableEq Revision] [DecidableEq Digest]
    [DecidableRel (· < · : Score → Score → Prop)]
    (limit : Nat)
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (raw : RawMeasuredGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source)
    (authority : Option (ExactAuthority spec source)) :
    ExecutionPlan spec source :=
  match produceRawArtifactWithinBound limit raw with
  | none => .source
  | some produced =>
      ingestAndPrepare spec request model produced guidance authority

/-- Bounded artifact construction preserves the source observation whether it
succeeds or falls back. -/
theorem observe_produceIngestAndPrepareWithinBound
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : KolmogorovComplexity.ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq CandidateId] [DecidableEq Revision] [DecidableEq Digest]
    [DecidableRel (· < · : Score → Score → Prop)]
    (limit : Nat)
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (raw : RawMeasuredGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source)
    (authority : Option (ExactAuthority spec source)) :
    (produceIngestAndPrepareWithinBound limit spec request model raw guidance
      authority).observe = spec.observeSource source := by
  unfold produceIngestAndPrepareWithinBound
  cases produceRawArtifactWithinBound limit raw with
  | none => rfl
  | some produced =>
      exact observe_ingestAndPrepare spec request model produced guidance authority

/-- Overflow or malformed-measurement rejection is an explicit source-plan
fallback, not a different ordering. -/
theorem produceIngestAndPrepareWithinBound_of_production_rejected
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    {Source : Type uSource} {U : KolmogorovComplexity.ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    [DecidableEq CandidateId] [DecidableEq Revision] [DecidableEq Digest]
    [DecidableRel (· < · : Score → Score → Prop)]
    (limit : Nat)
    (spec : OptimizationSpec Source)
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (model : ModelReceipt Revision Digest)
    (raw : RawMeasuredGuidanceArtifact CandidateId Digest Score)
    (guidance : CompressionGuidance U trace source)
    (authority : Option (ExactAuthority spec source))
    (rejected : produceRawArtifactWithinBound limit raw = none) :
    produceIngestAndPrepareWithinBound limit spec request model raw guidance
      authority = .source := by
  simp [produceIngestAndPrepareWithinBound, rejected]

/-! ## Finite boundary controls -/

namespace Canary

open IncrementalCompressionExternalArtifactChecker.Canary
open IncrementalCompressionRankingArtifact.Canary

/-- The largest comparison in `measuredArtifact` is `70 * 100 = 7000`. -/
theorem measured_artifact_fits_exact_boundary :
    (produceRawArtifactWithinBound 7000 measuredArtifact).map (·.order) =
      some ["right", "left"] := by
  decide

/-- Lowering that bound by one rejects the artifact rather than wrapping or
changing its candidate order. -/
theorem measured_artifact_rejects_below_boundary :
    produceRawArtifactWithinBound 6999 measuredArtifact = none := by
  decide

/-- The ordinary canary is safely representable by a 64-bit implementation. -/
theorem measured_artifact_fits_uint64 :
    (produceRawArtifactWithinBound uint64MaxNat measuredArtifact).map (·.order) =
      some ["right", "left"] := by
  decide

def hugeLeftMeasurement : RawCompressionMeasurement String where
  candidate := "huge-left"
  ordinaryLength := 2 ^ 40
  featureLength := 0
  residualLength := 0

def hugeRightMeasurement : RawCompressionMeasurement String where
  candidate := "huge-right"
  ordinaryLength := 2 ^ 40
  featureLength := 0
  residualLength := 0

def hugeMeasuredArtifact : RawMeasuredGuidanceArtifact String Nat Nat where
  measurements := [hugeLeftMeasurement, hugeRightMeasurement]
  calibration := rawCalibration

/-- A mathematically valid exact tie whose `2^80` products exceed `UInt64`
is rejected by the bounded producer. -/
theorem huge_exact_tie_rejects_uint64 :
    produceRawArtifactWithinBound uint64MaxNat hugeMeasuredArtifact = none := by
  decide

/-- The unbounded reference remains defined for the same huge exact tie and
preserves source order.  This separates representation rejection from the
mathematical ranking relation. -/
theorem huge_exact_tie_has_unbounded_reference :
    (produceRawArtifact hugeMeasuredArtifact).map (·.order) =
      some ["huge-left", "huge-right"] := by
  decide

end Canary

section AxiomAudit

#print axioms checkedMulAt_isSome_iff
#print axioms checkedMulAt_eq_some_iff
#print axioms pairFitsAt?_eq_true_iff
#print axioms comparisonSafeAt?_eq_true_iff
#print axioms rankWithinBound_eq_some_iff
#print axioms rankWithinBound_perm
#print axioms produceRawArtifactWithinBound_success_implies_reference
#print axioms produceRawArtifactWithinBound_order_perm_measurement_ids
#print axioms produceRawArtifactWithinBound_calibration
#print axioms observe_produceIngestAndPrepareWithinBound
#print axioms produceIngestAndPrepareWithinBound_of_production_rejected
#print axioms Canary.measured_artifact_fits_exact_boundary
#print axioms Canary.measured_artifact_rejects_below_boundary
#print axioms Canary.measured_artifact_fits_uint64
#print axioms Canary.huge_exact_tie_rejects_uint64
#print axioms Canary.huge_exact_tie_has_unbounded_reference

end AxiomAudit

end IncrementalCompressionBoundedRanking
end Mettapedia.Languages.MeTTa.Prime
