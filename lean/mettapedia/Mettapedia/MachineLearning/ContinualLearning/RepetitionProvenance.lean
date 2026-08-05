import Mathlib

/-!
# Provenance of environmental repetition and learner-controlled replay

Hemati et al., *Continual Learning in the Presence of Repetition*
(arXiv:2405.04101), distinguish repetition supplied by the environment from
replay selected by the learning strategy.  Their challenge report is
empirical; it does not state the information-theoretic results below.

This file formalizes a reusable provenance boundary motivated by that
distinction:

* tagged streams split exactly into environmental and replay occurrences;
* erasing the origin tag makes the two causes observationally
  indistinguishable when they carry the same payload;
* consequently no observation-only reconstruction can recover every origin
  stream;
* retaining the tag makes both the origin sequence and its counts exact.

The result concerns causal bookkeeping, not model accuracy.  It does not
claim that environmental repetition or replay is preferable, nor that
observed payloads are statistically independent.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace RepetitionProvenance

/-- Whether a repeated occurrence came from the external stream or from a
replay decision made by the learning strategy. -/
inductive OccurrenceOrigin where
  | environment
  | replay
  deriving DecidableEq, Repr

/-- An observed payload together with the provenance needed for causal
accounting. -/
structure TaggedOccurrence (Payload : Type*) where
  payload : Payload
  origin : OccurrenceOrigin
  deriving DecidableEq, Repr

/-- Remove provenance, retaining only what an untagged learner observes. -/
def eraseOrigin {Payload : Type*}
    (occurrence : TaggedOccurrence Payload) : Payload :=
  occurrence.payload

/-- Untagged observation stream. -/
def eraseStream {Payload : Type*}
    (stream : List (TaggedOccurrence Payload)) : List Payload :=
  stream.map eraseOrigin

/-- Exact origin trace retained by a provenance-aware ledger. -/
def originStream {Payload : Type*}
    (stream : List (TaggedOccurrence Payload)) : List OccurrenceOrigin :=
  stream.map TaggedOccurrence.origin

/-- Number of occurrences having one declared origin. -/
def originCount {Payload : Type*}
    (origin : OccurrenceOrigin)
    (stream : List (TaggedOccurrence Payload)) : ℕ :=
  (stream.filter fun occurrence => occurrence.origin = origin).length

/-- Every tagged occurrence belongs to exactly one of the two provenance
classes. -/
theorem originCount_environment_add_replay
    {Payload : Type*}
    (stream : List (TaggedOccurrence Payload)) :
    originCount .environment stream + originCount .replay stream =
      stream.length := by
  induction stream with
  | nil =>
      simp [originCount]
  | cons occurrence tail ih =>
      rcases occurrence with ⟨payload, origin⟩
      cases origin with
      | environment =>
          simp_all [originCount]
          omega
      | replay =>
          simp_all [originCount]
          omega

/-- A provenance-aware ledger recovers the origin of each tagged occurrence
without inspecting its payload. -/
theorem tagged_origin_recovery_exact
    {Payload : Type*}
    (stream : List (TaggedOccurrence Payload)) :
    stream.map (fun occurrence => occurrence.origin) = originStream stream := by
  rfl

/-- Correctness of an origin classifier on one tagged occurrence.  The
classifier itself sees only the untagged payload. -/
def ObservationOnlyCorrect
    {Payload : Type*}
    (classifier : Payload → OccurrenceOrigin)
    (occurrence : TaggedOccurrence Payload) : Prop :=
  classifier (eraseOrigin occurrence) = occurrence.origin

/-- No observation-only classifier can be correct for both possible causes
of the same payload. -/
theorem observationOnly_not_correct_for_both_origins
    {Payload : Type*}
    (classifier : Payload → OccurrenceOrigin)
    (payload : Payload) :
    ¬ (ObservationOnlyCorrect classifier
          ⟨payload, .environment⟩ ∧
        ObservationOnlyCorrect classifier
          ⟨payload, .replay⟩) := by
  cases h : classifier payload <;>
    simp [ObservationOnlyCorrect, eraseOrigin, h]

/-- Stream-level impossibility: after origin erasure, no reconstruction
function can recover the exact origin trace for every tagged stream. -/
theorem no_universal_origin_reconstruction
    {Payload : Type*}
    (payload : Payload) :
    ¬ ∃ reconstruct : List Payload → List OccurrenceOrigin,
        ∀ stream : List (TaggedOccurrence Payload),
          reconstruct (eraseStream stream) = originStream stream := by
  rintro ⟨reconstruct, reconstructs⟩
  have environmentCase :=
    reconstructs [⟨payload, .environment⟩]
  have replayCase :=
    reconstructs [⟨payload, .replay⟩]
  have impossible :
      [OccurrenceOrigin.environment] = [OccurrenceOrigin.replay] := by
    simpa [eraseStream, eraseOrigin, originStream] using
      environmentCase.symm.trans replayCase
  simp at impossible

/-! ## Executable positive and negative fixtures -/

def environmentalUnit : TaggedOccurrence Unit :=
  ⟨(), .environment⟩

def replayedUnit : TaggedOccurrence Unit :=
  ⟨(), .replay⟩

/-- Positive fixture: a tagged two-event ledger retains one event from each
source and decomposes its total exactly. -/
theorem tagged_two_event_ledger :
    originStream [environmentalUnit, replayedUnit] =
        [.environment, .replay] ∧
      originCount .environment [environmentalUnit, replayedUnit] = 1 ∧
      originCount .replay [environmentalUnit, replayedUnit] = 1 ∧
      originCount .environment [environmentalUnit, replayedUnit] +
          originCount .replay [environmentalUnit, replayedUnit] =
        [environmentalUnit, replayedUnit].length := by
  decide

/-- Negative fixture: the one-event environmental and replay streams have
identical untagged observations and equal total length, but different
environmental counts. -/
theorem erased_singletons_hide_provenance :
    eraseStream [environmentalUnit] = eraseStream [replayedUnit] ∧
      [environmentalUnit].length = [replayedUnit].length ∧
      originCount .environment [environmentalUnit] ≠
        originCount .environment [replayedUnit] := by
  decide

/-- Crown: exact tagged accounting and the impossibility of reconstructing
all origins after erasure hold simultaneously. -/
theorem repetition_provenance_boundary_crown :
    (∀ stream : List (TaggedOccurrence Unit),
        originCount .environment stream + originCount .replay stream =
          stream.length) ∧
      ¬ ∃ reconstruct : List Unit → List OccurrenceOrigin,
        ∀ stream : List (TaggedOccurrence Unit),
          reconstruct (eraseStream stream) = originStream stream := by
  constructor
  · exact originCount_environment_add_replay
  · exact no_universal_origin_reconstruction ()

#print axioms originCount_environment_add_replay
#print axioms observationOnly_not_correct_for_both_origins
#print axioms no_universal_origin_reconstruction
#print axioms repetition_provenance_boundary_crown

end RepetitionProvenance

end Mettapedia.MachineLearning.ContinualLearning
