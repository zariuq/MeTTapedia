import Mathlib.Data.List.Sort
import Mettapedia.Languages.MeTTa.Prime.IncrementalCompressionExternalArtifactChecker

/-!
# Exact description-length ranking artifacts

This module constructs the raw complete ordering consumed by Prime's external
incremental-compression artifact checker.  Each candidate measurement records
the ordinary trace length and the feature/residual two-part length.  Ranking
uses the exact saved-bit fraction

`(ordinaryLength - (featureLength + residualLength)) / ordinaryLength`.

The executable comparator uses natural-number cross multiplication, so it has
no floating-point division, rounding mode, or tolerance.  Stable insertion
sorting preserves source order when exact rates tie.  Sorting is proved to be
a permutation before the existing external checker validates it against the
complete request family.
-/

namespace Mettapedia.Languages.MeTTa.Prime
namespace IncrementalCompressionRankingArtifact

open IncrementalCompressionOptimizationSelection
open IncrementalCompressionExternalGuidanceReceipt
open IncrementalCompressionExternalArtifactChecker

universe uCandidateId uFormula uRevision uDigest uScore uSource

/-! ## Raw and positive-denominator measurements -/

/-- Persisted description-length measurements for one stable candidate ID. -/
structure RawCompressionMeasurement (CandidateId : Type uCandidateId) where
  candidate : CandidateId
  ordinaryLength : Nat
  featureLength : Nat
  residualLength : Nat
deriving DecidableEq

namespace RawCompressionMeasurement

/-- The measured two-part description length. -/
def twoPartLength {CandidateId : Type uCandidateId}
    (measurement : RawCompressionMeasurement CandidateId) : Nat :=
  measurement.featureLength + measurement.residualLength

/-- Saved bits, truncated at zero for a noncompressive candidate. -/
def savedBits {CandidateId : Type uCandidateId}
    (measurement : RawCompressionMeasurement CandidateId) : Nat :=
  measurement.ordinaryLength - measurement.twoPartLength

/-- Extract an exact raw measurement from an existing strict executable
compression witness. -/
def ofGuidance
    {CandidateId : Type uCandidateId} {Source : Type uSource}
    {U : KolmogorovComplexity.ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    (candidate : CandidateId) (guidance : CompressionGuidance U trace source) :
    RawCompressionMeasurement CandidateId where
  candidate := candidate
  ordinaryLength := guidance.ordinaryCost
  featureLength := guidance.step.featureProgram.length
  residualLength := guidance.step.residual.length

@[simp]
theorem ofGuidance_ordinaryLength
    {CandidateId : Type uCandidateId} {Source : Type uSource}
    {U : KolmogorovComplexity.ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    (candidate : CandidateId) (guidance : CompressionGuidance U trace source) :
    (ofGuidance candidate guidance).ordinaryLength = guidance.ordinaryCost :=
  rfl

@[simp]
theorem ofGuidance_twoPartLength
    {CandidateId : Type uCandidateId} {Source : Type uSource}
    {U : KolmogorovComplexity.ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    (candidate : CandidateId) (guidance : CompressionGuidance U trace source) :
    (ofGuidance candidate guidance).twoPartLength = guidance.compiledCost :=
  rfl

/-- Strict compression supplies the positive denominator needed by the exact
rate comparison. -/
theorem ofGuidance_ordinary_pos
    {CandidateId : Type uCandidateId} {Source : Type uSource}
    {U : KolmogorovComplexity.ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    (candidate : CandidateId) (guidance : CompressionGuidance U trace source) :
    0 < (ofGuidance candidate guidance).ordinaryLength := by
  rw [ofGuidance_ordinaryLength]
  exact lt_of_le_of_lt (Nat.zero_le guidance.compiledCost)
    guidance.compiledCost_lt_ordinaryCost

/-- A strict compression witness has a strictly positive saved-bit count. -/
theorem ofGuidance_savedBits_pos
    {CandidateId : Type uCandidateId} {Source : Type uSource}
    {U : KolmogorovComplexity.ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    (candidate : CandidateId) (guidance : CompressionGuidance U trace source) :
    0 < (ofGuidance candidate guidance).savedBits := by
  rw [savedBits, ofGuidance_twoPartLength, ofGuidance_ordinaryLength]
  have compression := guidance.compiledCost_lt_ordinaryCost
  omega

end RawCompressionMeasurement

/-- A measurement whose ordinary trace has a positive length.  Positivity is
the only extra premise required to interpret the saved-bit ratio exactly. -/
structure CompressionMeasurement (CandidateId : Type uCandidateId) extends
    RawCompressionMeasurement CandidateId where
  ordinary_pos : 0 < ordinaryLength

namespace CompressionMeasurement

/-- Erase the positivity proof to recover the persisted measurement. -/
def raw {CandidateId : Type uCandidateId}
    (measurement : CompressionMeasurement CandidateId) :
    RawCompressionMeasurement CandidateId :=
  measurement.toRawCompressionMeasurement

/-- The measured two-part description length. -/
def twoPartLength {CandidateId : Type uCandidateId}
    (measurement : CompressionMeasurement CandidateId) : Nat :=
  measurement.featureLength + measurement.residualLength

/-- Saved bits, truncated at zero for a noncompressive candidate. -/
def savedBits {CandidateId : Type uCandidateId}
    (measurement : CompressionMeasurement CandidateId) : Nat :=
  measurement.ordinaryLength - measurement.twoPartLength

/-- Exact rational compression rate used only as a mathematical
specification.  The executable comparator below does not divide. -/
def rate {CandidateId : Type uCandidateId}
    (measurement : CompressionMeasurement CandidateId) : ℚ :=
  (measurement.savedBits : ℚ) / (measurement.ordinaryLength : ℚ)

/-- `left` ranks no later than `right` exactly when its saved-bit fraction is
at least as large.  Cross multiplication makes the decision integral. -/
def AtLeastAsGood {CandidateId : Type uCandidateId}
    (left right : CompressionMeasurement CandidateId) : Prop :=
  right.savedBits * left.ordinaryLength ≤
    left.savedBits * right.ordinaryLength

instance {CandidateId : Type uCandidateId} :
    DecidableRel (@AtLeastAsGood CandidateId) :=
  fun left right =>
    inferInstanceAs (Decidable
      (right.savedBits * left.ordinaryLength ≤
        left.savedBits * right.ordinaryLength))

/-- The cross-product comparator is exactly descending rational-rate order. -/
theorem atLeastAsGood_iff_rate_ge
    {CandidateId : Type uCandidateId}
    (left right : CompressionMeasurement CandidateId) :
    AtLeastAsGood left right ↔ right.rate ≤ left.rate := by
  unfold AtLeastAsGood rate
  rw [div_le_div_iff₀]
  · norm_cast
  · exact_mod_cast right.ordinary_pos
  · exact_mod_cast left.ordinary_pos

instance {CandidateId : Type uCandidateId} :
    Std.Total (@AtLeastAsGood CandidateId) where
  total left right := by
    rcases le_total right.rate left.rate with h | h
    · exact Or.inl ((atLeastAsGood_iff_rate_ge left right).mpr h)
    · exact Or.inr ((atLeastAsGood_iff_rate_ge right left).mpr h)

instance {CandidateId : Type uCandidateId} :
    IsTrans (CompressionMeasurement CandidateId) (@AtLeastAsGood CandidateId) where
  trans left middle right hleft hmiddle := by
    apply (atLeastAsGood_iff_rate_ge left right).mpr
    exact le_trans
      ((atLeastAsGood_iff_rate_ge middle right).mp hmiddle)
      ((atLeastAsGood_iff_rate_ge left middle).mp hleft)

end CompressionMeasurement

namespace RawCompressionMeasurement

/-- Check the positive denominator required by the exact rate semantics. -/
def check {CandidateId : Type uCandidateId}
    (raw : RawCompressionMeasurement CandidateId) :
    Option (CompressionMeasurement CandidateId) :=
  if ordinary_pos : 0 < raw.ordinaryLength then
    some
      { candidate := raw.candidate
        ordinaryLength := raw.ordinaryLength
        featureLength := raw.featureLength
        residualLength := raw.residualLength
        ordinary_pos := ordinary_pos }
  else none

/-- Measurement checking succeeds exactly for a positive ordinary length. -/
theorem check_isSome_iff_ordinary_pos
    {CandidateId : Type uCandidateId}
    (raw : RawCompressionMeasurement CandidateId) :
    raw.check.isSome = true ↔ 0 < raw.ordinaryLength := by
  unfold check
  by_cases ordinary_pos : 0 < raw.ordinaryLength <;> simp [ordinary_pos]

/-- Measurements extracted from strict guidance always pass denominator
checking. -/
theorem check_ofGuidance_isSome
    {CandidateId : Type uCandidateId} {Source : Type uSource}
    {U : KolmogorovComplexity.ConditionalAlgorithm}
    {trace : TraceProjection Source} {source : Source}
    (candidate : CandidateId) (guidance : CompressionGuidance U trace source) :
    (ofGuidance candidate guidance).check.isSome = true :=
  (check_isSome_iff_ordinary_pos _).mpr
    (ofGuidance_ordinary_pos candidate guidance)

end RawCompressionMeasurement

/-! ## Checked measurement lists -/

/-- Check every measurement while preserving its source position. -/
def checkMeasurements {CandidateId : Type uCandidateId} :
    List (RawCompressionMeasurement CandidateId) →
      Option (List (CompressionMeasurement CandidateId))
  | [] => some []
  | head :: tail =>
      match head.check, checkMeasurements tail with
      | some checkedHead, some checkedTail =>
          some (checkedHead :: checkedTail)
      | _, _ => none

/-- Successful list checking preserves the candidate-ID sequence exactly. -/
theorem checkMeasurements_map_candidate
    {CandidateId : Type uCandidateId}
    {raw : List (RawCompressionMeasurement CandidateId)}
    {checked : List (CompressionMeasurement CandidateId)}
    (accepted : checkMeasurements raw = some checked) :
    checked.map (·.candidate) = raw.map (·.candidate) := by
  induction raw generalizing checked with
  | nil =>
      simp [checkMeasurements] at accepted
      subst checked
      rfl
  | cons head tail ih =>
      simp only [checkMeasurements] at accepted
      cases hhead : head.check with
      | none => simp [hhead] at accepted
      | some checkedHead =>
          cases htail : checkMeasurements tail with
          | none => simp [hhead, htail] at accepted
          | some checkedTail =>
              simp [hhead, htail] at accepted
              subst checked
              have headId : checkedHead.candidate = head.candidate := by
                unfold RawCompressionMeasurement.check at hhead
                split at hhead
                · have measurementEq := Option.some.inj hhead
                  exact (congrArg
                    (fun measurement : CompressionMeasurement CandidateId =>
                      measurement.candidate) measurementEq).symm
                · simp at hhead
              simp [headId, ih htail]

/-! ## Exact stable ranking -/

/-- Stable descending-rate ranking. -/
def rankMeasurements {CandidateId : Type uCandidateId}
    (measurements : List (CompressionMeasurement CandidateId)) :
    List (CompressionMeasurement CandidateId) :=
  measurements.insertionSort CompressionMeasurement.AtLeastAsGood

/-- Stable ranking is a permutation of every checked measurement. -/
theorem rankMeasurements_perm
    {CandidateId : Type uCandidateId}
    (measurements : List (CompressionMeasurement CandidateId)) :
    (rankMeasurements measurements).Perm measurements :=
  List.perm_insertionSort CompressionMeasurement.AtLeastAsGood measurements

/-- The ranked measurements are pairwise nonincreasing in exact rate. -/
theorem rankMeasurements_pairwise
    {CandidateId : Type uCandidateId}
    (measurements : List (CompressionMeasurement CandidateId)) :
    (rankMeasurements measurements).Pairwise
      CompressionMeasurement.AtLeastAsGood :=
  List.pairwise_insertionSort
    CompressionMeasurement.AtLeastAsGood measurements

/-- Candidate IDs emitted by stable exact-rate ranking. -/
def rankedCandidateIds {CandidateId : Type uCandidateId}
    (measurements : List (CompressionMeasurement CandidateId)) :
    List CandidateId :=
  (rankMeasurements measurements).map (·.candidate)

/-- Ranking neither adds nor deletes candidate IDs. -/
theorem rankedCandidateIds_perm
    {CandidateId : Type uCandidateId}
    (measurements : List (CompressionMeasurement CandidateId)) :
    (rankedCandidateIds measurements).Perm
      (measurements.map (·.candidate)) :=
  by
    simpa [rankedCandidateIds] using
      (rankMeasurements_perm measurements).map
        (fun measurement => measurement.candidate)

/-- Exact-rate ties preserve the source order for a two-candidate list. -/
theorem rankMeasurements_pair_of_equal_rate
    {CandidateId : Type uCandidateId}
    (left right : CompressionMeasurement CandidateId)
    (tie : left.rate = right.rate) :
    rankMeasurements [left, right] = [left, right] := by
  have ordered : CompressionMeasurement.AtLeastAsGood left right :=
    (CompressionMeasurement.atLeastAsGood_iff_rate_ge left right).mpr
      tie.symm.le
  simp [rankMeasurements, List.insertionSort, ordered]

/-! ## Producer artifacts -/

/-- Raw measurements plus the already defined raw held-out calibration data. -/
structure RawMeasuredGuidanceArtifact
    (CandidateId : Type uCandidateId) (Digest : Type uDigest)
    (Score : Type uScore) where
  measurements : List (RawCompressionMeasurement CandidateId)
  calibration : RawCalibrationArtifact Digest Score

/-- Construct the raw external ordering after checking every denominator. -/
def produceRawArtifact
    {CandidateId : Type uCandidateId} {Digest : Type uDigest}
    {Score : Type uScore}
    (raw : RawMeasuredGuidanceArtifact CandidateId Digest Score) :
    Option (RawExternalGuidanceArtifact CandidateId Digest Score) :=
  match checkMeasurements raw.measurements with
  | none => none
  | some checked =>
      some
        { order := rankedCandidateIds checked
          calibration := raw.calibration }

/-- Whenever production succeeds, the generated order is a permutation of
the raw measurement-ID sequence. -/
theorem produceRawArtifact_order_perm_measurement_ids
    {CandidateId : Type uCandidateId} {Digest : Type uDigest}
    {Score : Type uScore}
    {raw : RawMeasuredGuidanceArtifact CandidateId Digest Score}
    {produced : RawExternalGuidanceArtifact CandidateId Digest Score}
    (accepted : produceRawArtifact raw = some produced) :
    produced.order.Perm (raw.measurements.map (·.candidate)) := by
  unfold produceRawArtifact at accepted
  cases hchecked : checkMeasurements raw.measurements with
  | none => simp [hchecked] at accepted
  | some checked =>
      simp [hchecked] at accepted
      subst produced
      have permutation := rankedCandidateIds_perm checked
      rw [checkMeasurements_map_candidate hchecked] at permutation
      exact permutation

/-- Production retains the exact calibration payload supplied by the caller. -/
theorem produceRawArtifact_calibration
    {CandidateId : Type uCandidateId} {Digest : Type uDigest}
    {Score : Type uScore}
    {raw : RawMeasuredGuidanceArtifact CandidateId Digest Score}
    {produced : RawExternalGuidanceArtifact CandidateId Digest Score}
    (accepted : produceRawArtifact raw = some produced) :
    produced.calibration = raw.calibration := by
  unfold produceRawArtifact at accepted
  cases hchecked : checkMeasurements raw.measurements with
  | none => simp [hchecked] at accepted
  | some checked =>
      simp [hchecked] at accepted
      subst produced
      rfl

/-- Produce and then apply the existing complete-family and calibration
checker. -/
def produceAndCheck
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    [DecidableEq CandidateId]
    [DecidableRel (· < · : Score → Score → Prop)]
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (raw : RawMeasuredGuidanceArtifact CandidateId Digest Score) :
    Option (CheckedExternalArtifact Digest Score request) :=
  match produceRawArtifact raw with
  | none => none
  | some produced => checkExternalArtifact request produced

/-- Complete measured support plus passing held-out scores is sufficient for
the produced artifact to pass the existing external checker. -/
theorem produceAndCheck_isSome_of_complete_and_calibrated
    {CandidateId : Type uCandidateId} {Formula : Type uFormula}
    {Revision : Type uRevision} {Digest : Type uDigest}
    {Score : Type uScore} [LT Score]
    [DecidableEq CandidateId]
    [DecidableRel (· < · : Score → Score → Prop)]
    (request : GuidanceRequestReceipt CandidateId Formula Revision)
    (raw : RawMeasuredGuidanceArtifact CandidateId Digest Score)
    (produced : RawExternalGuidanceArtifact CandidateId Digest Score)
    (production : produceRawArtifact raw = some produced)
    (complete : (raw.measurements.map (·.candidate)).Perm request.family.ids)
    (calibrated : raw.calibration.properScores.Passes) :
    (produceAndCheck request raw).isSome = true := by
  have producedComplete : produced.order.Perm request.family.ids :=
    (produceRawArtifact_order_perm_measurement_ids production).trans complete
  have calibrationEq := produceRawArtifact_calibration production
  have producedCalibrated : produced.calibration.properScores.Passes := by
    rw [calibrationEq]
    exact calibrated
  have calibrationAccepted : produced.calibration.check.isSome = true :=
    (RawCalibrationArtifact.check_isSome_iff_passes
      produced.calibration).mpr producedCalibrated
  cases hcalibration : produced.calibration.check with
  | none =>
      simp [hcalibration] at calibrationAccepted
  | some receipt =>
      simp [produceAndCheck, production, checkExternalArtifact,
        producedComplete, hcalibration]

/-! ## Finite executable controls -/

namespace Canary

open IncrementalCompressionExternalGuidanceReceipt.Canary
open IncrementalCompressionExternalArtifactChecker.Canary

def leftMeasurement : RawCompressionMeasurement String where
  candidate := "left"
  ordinaryLength := 100
  featureLength := 20
  residualLength := 30

def rightMeasurement : RawCompressionMeasurement String where
  candidate := "right"
  ordinaryLength := 100
  featureLength := 10
  residualLength := 20

def measuredArtifact : RawMeasuredGuidanceArtifact String Nat Nat where
  measurements := [leftMeasurement, rightMeasurement]
  calibration := rawCalibration

/-- Positive control: 70% saved ranks before 50% saved and reproduces the raw
artifact accepted by the external checker. -/
theorem producer_emits_expected_complete_order :
    (produceRawArtifact measuredArtifact).map (·.order) =
      some rawArtifact.order := by
  decide

/-- The producer output passes complete-family and calibration checking. -/
theorem produced_artifact_is_checked :
    (produceAndCheck request measuredArtifact).isSome = true := by
  decide

/-- The producer output also passes the exact model-identity ingestion gate. -/
theorem produced_artifact_is_ingested :
    (match produceRawArtifact measuredArtifact with
      | none => false
      | some produced =>
          (ingestExternalGuidance request model produced guidance).isSome) =
        true := by
  decide

/-- Positive source control: a genuine strict compression witness directly
produces a checkable, positive-gain measurement. -/
theorem strict_guidance_produces_checked_measurement :
    ((RawCompressionMeasurement.ofGuidance "left" guidance).check).isSome =
      true :=
  RawCompressionMeasurement.check_ofGuidance_isSome "left" guidance

theorem strict_guidance_measurement_saves_bits :
    0 < (RawCompressionMeasurement.ofGuidance "left" guidance).savedBits :=
  RawCompressionMeasurement.ofGuidance_savedBits_pos "left" guidance

def incompleteMeasuredArtifact : RawMeasuredGuidanceArtifact String Nat Nat where
  measurements := [rightMeasurement]
  calibration := rawCalibration

/-- Negative control: a well-formed measurement for only one candidate is
produced, then rejected because it does not cover the complete request. -/
theorem incomplete_measurements_are_rejected :
    produceAndCheck request incompleteMeasuredArtifact = none := by
  decide

def zeroLengthMeasurement : RawCompressionMeasurement String where
  candidate := "left"
  ordinaryLength := 0
  featureLength := 0
  residualLength := 0

def zeroLengthArtifact : RawMeasuredGuidanceArtifact String Nat Nat where
  measurements := [zeroLengthMeasurement, rightMeasurement]
  calibration := rawCalibration

/-- Negative control: a zero denominator is rejected rather than assigned an
implementation-dependent exceptional rate. -/
theorem zero_ordinary_length_is_rejected :
    produceRawArtifact zeroLengthArtifact = none := by
  decide

def tieLeft : RawCompressionMeasurement String where
  candidate := "left"
  ordinaryLength := 10
  featureLength := 2
  residualLength := 3

def tieRight : RawCompressionMeasurement String where
  candidate := "right"
  ordinaryLength := 20
  featureLength := 4
  residualLength := 6

def tiedArtifact : RawMeasuredGuidanceArtifact String Nat Nat where
  measurements := [tieLeft, tieRight]
  calibration := rawCalibration

/-- Tie control: equal exact rates retain the request's source order. -/
theorem equal_rates_preserve_source_order :
    (produceRawArtifact tiedArtifact).map (·.order) =
      some ["left", "right"] := by
  decide

end Canary

section AxiomAudit

#print axioms CompressionMeasurement.atLeastAsGood_iff_rate_ge
#print axioms RawCompressionMeasurement.ofGuidance_ordinary_pos
#print axioms RawCompressionMeasurement.ofGuidance_savedBits_pos
#print axioms RawCompressionMeasurement.check_isSome_iff_ordinary_pos
#print axioms RawCompressionMeasurement.check_ofGuidance_isSome
#print axioms checkMeasurements_map_candidate
#print axioms rankMeasurements_perm
#print axioms rankMeasurements_pairwise
#print axioms rankedCandidateIds_perm
#print axioms rankMeasurements_pair_of_equal_rate
#print axioms produceRawArtifact_order_perm_measurement_ids
#print axioms produceRawArtifact_calibration
#print axioms produceAndCheck_isSome_of_complete_and_calibrated
#print axioms Canary.producer_emits_expected_complete_order
#print axioms Canary.produced_artifact_is_checked
#print axioms Canary.produced_artifact_is_ingested
#print axioms Canary.strict_guidance_produces_checked_measurement
#print axioms Canary.strict_guidance_measurement_saves_bits
#print axioms Canary.incomplete_measurements_are_rejected
#print axioms Canary.zero_ordinary_length_is_rejected
#print axioms Canary.equal_rates_preserve_source_order

end AxiomAudit

end IncrementalCompressionRankingArtifact
end Mettapedia.Languages.MeTTa.Prime
