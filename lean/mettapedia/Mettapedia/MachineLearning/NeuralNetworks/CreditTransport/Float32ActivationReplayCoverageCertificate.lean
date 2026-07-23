import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Float32ActivationReplayBatchCertificate

/-!
# Complete coverage by binary32 activation replay batches

Large traced tensors are checked in bounded slices.  This module prevents a
collection of individually valid slices from being mistaken for complete
coverage: the source identity must agree, the first slice must begin at zero,
every following slice must begin at the preceding exclusive endpoint, and the
final endpoint must equal the declared source entry count.

Digest strings are compared, not interpreted.  Establishing that they name a
particular trace remains a source-provenance obligation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Float32ActivationReplayCoverageCertificate

open Float32ActivationReplayCertificate
open Float32ActivationReplayBatchCertificate

noncomputable section

/-- Identity shared by every slice of one traced activation tensor. -/
structure ActivationReplaySource where
  sourceProbeSha256 : String
  inputTensorSha256 : String
  outputTensorSha256 : String
  siteIndex : Nat
  sourceEntryCount : Nat
  deriving DecidableEq, Repr

/-- One checked batch together with its exclusive source interval metadata. -/
structure Float32ActivationReplaySlice where
  source : ActivationReplaySource
  sliceStart : Nat
  batch : Float32ActivationReplayBatch
  deriving Repr

/-- Exact recursive coverage from `cursor` to the source tensor's endpoint. -/
def CoversFrom (source : ActivationReplaySource) :
    Nat → List Float32ActivationReplaySlice → Prop
  | cursor, [] => cursor = source.sourceEntryCount
  | cursor, slice :: slices =>
      slice.source = source ∧
      slice.sliceStart = cursor ∧
      slice.batch.Valid ∧
      CoversFrom source (cursor + slice.batch.expectedCount) slices

/-- Executable mirror of `CoversFrom`. -/
def coversFromCheck (source : ActivationReplaySource) :
    Nat → List Float32ActivationReplaySlice → Bool
  | cursor, [] => decide (cursor = source.sourceEntryCount)
  | cursor, slice :: slices =>
      decide (slice.source = source ∧ slice.sliceStart = cursor) &&
      slice.batch.check &&
      coversFromCheck source (cursor + slice.batch.expectedCount) slices

theorem coversFromCheck_eq_true_iff (source : ActivationReplaySource)
    (cursor : Nat) (slices : List Float32ActivationReplaySlice) :
    coversFromCheck source cursor slices = true ↔
      CoversFrom source cursor slices := by
  induction slices generalizing cursor with
  | nil => simp [coversFromCheck, CoversFrom]
  | cons slice slices ih =>
      simp [coversFromCheck, CoversFrom, ih,
        Float32ActivationReplayBatch.check_eq_true_iff, and_assoc]

/-- A source header and the ordered slices claimed to cover it. -/
structure Float32ActivationReplayCoverage where
  source : ActivationReplaySource
  slices : List Float32ActivationReplaySlice
  deriving Repr

/-- Propositional meaning of complete nonempty-source coverage. -/
def Float32ActivationReplayCoverage.Valid
    (coverage : Float32ActivationReplayCoverage) : Prop :=
  0 < coverage.source.sourceEntryCount ∧
  CoversFrom coverage.source 0 coverage.slices

/-- Check exact nonempty contiguous coverage and every underlying replay. -/
def Float32ActivationReplayCoverage.check
    (coverage : Float32ActivationReplayCoverage) : Bool :=
  decide (0 < coverage.source.sourceEntryCount) &&
  coversFromCheck coverage.source 0 coverage.slices

theorem Float32ActivationReplayCoverage.check_eq_true_iff
    (coverage : Float32ActivationReplayCoverage) :
    coverage.check = true ↔ coverage.Valid := by
  simp [Float32ActivationReplayCoverage.check,
    Float32ActivationReplayCoverage.Valid, coversFromCheck_eq_true_iff]

/-- Flattened records in the unique source order certified by a manifest. -/
def Float32ActivationReplayCoverage.entries
    (coverage : Float32ActivationReplayCoverage) : List Float32ActivationReplay :=
  coverage.slices.flatMap fun slice => slice.batch.entries

/-- Total exact-real discrepancy across all covered entries. -/
def Float32ActivationReplayCoverage.totalAbsoluteError
    (coverage : Float32ActivationReplayCoverage) : ℝ :=
  (coverage.slices.map fun slice => slice.batch.totalAbsoluteError).sum

/-- Sum of all checked rational error budgets across all covered entries. -/
def Float32ActivationReplayCoverage.totalCertifiedError
    (coverage : Float32ActivationReplayCoverage) : ℝ :=
  (coverage.slices.map fun slice => slice.batch.totalCertifiedError).sum

theorem CoversFrom.entries_length_add_cursor
    {source : ActivationReplaySource} {cursor : Nat}
    {slices : List Float32ActivationReplaySlice}
    (hcover : CoversFrom source cursor slices) :
    (slices.flatMap fun slice => slice.batch.entries).length + cursor =
      source.sourceEntryCount := by
  induction slices generalizing cursor with
  | nil => simpa [CoversFrom] using hcover
  | cons slice slices ih =>
      rcases hcover with ⟨_, _, hbatch, hrest⟩
      have htail := ih hrest
      simp only [List.flatMap_cons, List.length_append]
      rw [hbatch.2.1]
      omega

/-- Accepted coverage contains exactly the declared number of records. -/
theorem Float32ActivationReplayCoverage.entries_length_eq
    (coverage : Float32ActivationReplayCoverage)
    (hcheck : coverage.check = true) :
    coverage.entries.length = coverage.source.sourceEntryCount := by
  have hcover := (coverage.check_eq_true_iff.mp hcheck).2
  have hlength := CoversFrom.entries_length_add_cursor hcover
  simpa [Float32ActivationReplayCoverage.entries] using hlength

theorem CoversFrom.batch_valid_of_mem
    {source : ActivationReplaySource} {cursor : Nat}
    {slices : List Float32ActivationReplaySlice}
    (hcover : CoversFrom source cursor slices)
    {slice : Float32ActivationReplaySlice} (hmem : slice ∈ slices) :
    slice.batch.Valid := by
  induction slices generalizing cursor with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases hcover with ⟨_, _, hhead, htail⟩
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hhead
      · exact ih htail hmem

/-- Every flattened record in an accepted coverage manifest inherits the
single-pair exact-real soundness theorem. -/
theorem Float32ActivationReplayCoverage.sound_of_mem
    (coverage : Float32ActivationReplayCoverage)
    (hcheck : coverage.check = true)
    {certificate : Float32ActivationReplay}
    (hmem : certificate ∈ coverage.entries) :
    |certificate.output.toReal -
        certificate.enclosure.operation.realMap certificate.input.toReal| ≤
      (certificate.enclosure.localError : ℝ) := by
  rw [Float32ActivationReplayCoverage.entries, List.mem_flatMap] at hmem
  obtain ⟨slice, hslice, hcertificate⟩ := hmem
  have hcover := (coverage.check_eq_true_iff.mp hcheck).2
  have hvalid := hcover.batch_valid_of_mem hslice
  exact slice.batch.sound_of_mem
    (slice.batch.check_eq_true_iff.mpr hvalid) hcertificate

theorem CoversFrom.total_error_le
    {source : ActivationReplaySource} {cursor : Nat}
    {slices : List Float32ActivationReplaySlice}
    (hcover : CoversFrom source cursor slices) :
    (slices.map fun slice => slice.batch.totalAbsoluteError).sum ≤
      (slices.map fun slice => slice.batch.totalCertifiedError).sum := by
  induction slices generalizing cursor with
  | nil => simp
  | cons slice slices ih =>
      rcases hcover with ⟨_, _, hbatch, hrest⟩
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add
        (slice.batch.totalAbsoluteError_le
          (slice.batch.check_eq_true_iff.mpr hbatch))
        (ih hrest)

/-- Complete coverage transports every batch error budget into one global
conservative error budget. -/
theorem Float32ActivationReplayCoverage.totalAbsoluteError_le
    (coverage : Float32ActivationReplayCoverage)
    (hcheck : coverage.check = true) :
    coverage.totalAbsoluteError ≤ coverage.totalCertifiedError := by
  exact CoversFrom.total_error_le (coverage.check_eq_true_iff.mp hcheck).2

/-! ## Complete coverage and corrupt-manifest fixtures -/

def fixtureSource : ActivationReplaySource where
  sourceProbeSha256 := "probe-a"
  inputTensorSha256 := "input-a"
  outputTensorSha256 := "output-a"
  siteIndex := 0
  sourceEntryCount := 2

def firstSingletonBatch : Float32ActivationReplayBatch where
  expectedCount := 1
  entries := [sigmoidHalfReplay]

def secondSingletonBatch : Float32ActivationReplayBatch where
  expectedCount := 1
  entries := [sigmoidTwoReplay]

def firstSlice : Float32ActivationReplaySlice where
  source := fixtureSource
  sliceStart := 0
  batch := firstSingletonBatch

def secondSlice : Float32ActivationReplaySlice where
  source := fixtureSource
  sliceStart := 1
  batch := secondSingletonBatch

def completeCoverage : Float32ActivationReplayCoverage where
  source := fixtureSource
  slices := [firstSlice, secondSlice]

theorem completeCoverage_is_accepted : completeCoverage.check = true := by
  simp [completeCoverage, Float32ActivationReplayCoverage.check,
    coversFromCheck, firstSlice, secondSlice, fixtureSource,
    firstSingletonBatch, secondSingletonBatch,
    Float32ActivationReplayBatch.check, sigmoidHalfReplay_is_accepted,
    sigmoidTwoReplay_is_accepted]

theorem completeCoverage_has_two_entries : completeCoverage.entries.length = 2 := by
  simpa [completeCoverage, fixtureSource] using
    completeCoverage.entries_length_eq completeCoverage_is_accepted

theorem completeCoverage_total_error_is_bounded :
    completeCoverage.totalAbsoluteError ≤ completeCoverage.totalCertifiedError :=
  completeCoverage.totalAbsoluteError_le completeCoverage_is_accepted

/-- A missing index between slices is rejected. -/
def gapCoverage : Float32ActivationReplayCoverage where
  source := fixtureSource
  slices := [firstSlice, { secondSlice with sliceStart := 2 }]

theorem gapCoverage_is_rejected : gapCoverage.check = false := by
  simp [gapCoverage, Float32ActivationReplayCoverage.check, coversFromCheck,
    firstSlice, secondSlice, fixtureSource, firstSingletonBatch,
    Float32ActivationReplayBatch.check, sigmoidHalfReplay_is_accepted]

/-- Reusing an already covered index is rejected. -/
def overlapCoverage : Float32ActivationReplayCoverage where
  source := fixtureSource
  slices := [firstSlice, { secondSlice with sliceStart := 0 }]

theorem overlapCoverage_is_rejected : overlapCoverage.check = false := by
  simp [overlapCoverage, Float32ActivationReplayCoverage.check, coversFromCheck,
    firstSlice, secondSlice, fixtureSource, firstSingletonBatch,
    Float32ActivationReplayBatch.check, sigmoidHalfReplay_is_accepted]

/-- Ending before the declared source endpoint is rejected. -/
def truncatedCoverage : Float32ActivationReplayCoverage where
  source := fixtureSource
  slices := [firstSlice]

theorem truncatedCoverage_is_rejected : truncatedCoverage.check = false := by
  simp [truncatedCoverage, Float32ActivationReplayCoverage.check,
    coversFromCheck, firstSlice, fixtureSource, firstSingletonBatch,
    Float32ActivationReplayBatch.check, sigmoidHalfReplay_is_accepted]

/-- Individually valid slices from another site cannot be mixed in. -/
def wrongSiteCoverage : Float32ActivationReplayCoverage where
  source := fixtureSource
  slices := [firstSlice, { secondSlice with
    source := { fixtureSource with siteIndex := 1 } }]

theorem wrongSiteCoverage_is_rejected : wrongSiteCoverage.check = false := by
  simp [wrongSiteCoverage, Float32ActivationReplayCoverage.check,
    coversFromCheck, firstSlice, secondSlice, fixtureSource,
    firstSingletonBatch, Float32ActivationReplayBatch.check,
    sigmoidHalfReplay_is_accepted]

/-- An empty list cannot cover a positive-size source. -/
def emptyCoverage : Float32ActivationReplayCoverage where
  source := fixtureSource
  slices := []

theorem emptyCoverage_is_rejected : emptyCoverage.check = false := by
  rfl

#print axioms coversFromCheck_eq_true_iff
#print axioms Float32ActivationReplayCoverage.entries_length_eq
#print axioms Float32ActivationReplayCoverage.sound_of_mem
#print axioms Float32ActivationReplayCoverage.totalAbsoluteError_le
#print axioms completeCoverage_total_error_is_bounded
#print axioms gapCoverage_is_rejected
#print axioms overlapCoverage_is_rejected
#print axioms truncatedCoverage_is_rejected
#print axioms wrongSiteCoverage_is_rejected
#print axioms emptyCoverage_is_rejected

end

end Float32ActivationReplayCoverageCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
