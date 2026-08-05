import Mettapedia.GSLT.LanguageDef.Gauthier.Adjudications33
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceBridge
import Mettapedia.PLN.Evidence.SourceReliability

/-!
# OEIS proof adjudications as dependence-aware WM-PLN evidence

An extensional Lean proof is factive evidence for the formal claim.  It does
not become an independent vote for the preceding text-to-specification
translation: the proof explicitly records that translation as an ancestor.
Independent review can contribute a separate source only when its lineage is
declared disjoint.  Source reliability remains an input to the graded layer;
the existence of a proof does not manufacture a calibration rate.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.OEISAdjudicationEvidence

open Mettapedia.GSLT.LanguageDef.GauthierAdjudications33
open Mettapedia.GSLT.LanguageDef.GauthierOEISSequenceSemantics
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.SourceReliability

/-- Provenance stages whose dependence must remain visible during revision. -/
inductive Lineage where
  | campaignProgram (programSha256 : String)
  | oeisEntry (revision oeisId entrySha256 : String)
  | formalization (revision oeisId entrySha256 : String)
  | leanProof (programSha256 oeisId : String)
  | independentReview (reviewId : Nat)
  deriving DecidableEq, BEq, Repr

abbrev Packet := SourcePacket String String Lineage

def claimOf (adjudication : CertifiedAdjudication) : String × String :=
  (adjudication.candidate.programSha256,
    adjudication.formalization.source.oeisId)

def entryLineage (adjudication : CertifiedAdjudication) : Lineage :=
  .oeisEntry adjudication.formalization.source.snapshotRevision
    adjudication.formalization.source.oeisId
    adjudication.formalization.source.entrySha256

def formalizationLineage (adjudication : CertifiedAdjudication) : Lineage :=
  .formalization adjudication.formalization.source.snapshotRevision
    adjudication.formalization.source.oeisId
    adjudication.formalization.source.entrySha256

/-- The formalization packet depends on the exact pinned OEIS entry. -/
def translationPacket (adjudication : CertifiedAdjudication) : Packet where
  program := adjudication.candidate.programSha256
  target := adjudication.formalization.source.oeisId
  source := formalizationLineage adjudication
  ancestors := {entryLineage adjudication}

/-- The proof packet depends transitively on the campaign program, OEIS entry,
and text-to-specification formalization. -/
def proofPacket (adjudication : CertifiedAdjudication) : Packet where
  program := adjudication.candidate.programSha256
  target := adjudication.formalization.source.oeisId
  source := .leanProof adjudication.candidate.programSha256
    adjudication.formalization.source.oeisId
  ancestors :=
    { .campaignProgram adjudication.candidate.programSha256
    , entryLineage adjudication
    , formalizationLineage adjudication }

/-- A separately identified review is represented as a fresh source.  The
caller, not this datatype, is responsible for assigning review identifiers
only to genuinely independent reviews. -/
def independentReviewPacket (adjudication : CertifiedAdjudication)
    (reviewId : Nat) : Packet where
  program := adjudication.candidate.programSha256
  target := adjudication.formalization.source.oeisId
  source := .independentReview reviewId
  ancestors := ∅

/-- A proof-carrying registry entry exposes its exact factive conclusion. -/
theorem certifiedAdjudication_is_factive (adjudication : CertifiedAdjudication) :
    CandidateRealizes adjudication.formalization.spec adjudication.candidate :=
  adjudication.correctness

theorem proofPacket_claim (adjudication : CertifiedAdjudication) :
    (proofPacket adjudication).claim = claimOf adjudication := by
  rfl

theorem proofPacket_contributes_one_positive_count
    (adjudication : CertifiedAdjudication) :
    aggregatePacketEvidence [proofPacket adjudication] (claimOf adjudication) =
      ⟨1, 0⟩ := by
  unfold aggregatePacketEvidence
  simp only [List.map]
  rw [
    Mettapedia.PLN.Evidence.EvidentialLedger.aggregate_cons,
    Mettapedia.PLN.Evidence.EvidentialLedger.aggregate_nil]
  simp [packetSourceItem, packetSupport, claimOf, proofPacket]

/-- Repeating one proof is not an independent confirmation. -/
theorem duplicateProof_not_sourceDisjoint (adjudication : CertifiedAdjudication) :
    ¬ (proofPacket adjudication).SourceDisjoint (proofPacket adjudication) := by
  intro h
  exact h.1 rfl

/-- The proof and its source translation are deliberately dependent: the
translation source occurs in the proof packet's ancestor set. -/
theorem translation_proof_not_sourceDisjoint
    (adjudication : CertifiedAdjudication) :
    ¬ (translationPacket adjudication).SourceDisjoint (proofPacket adjudication) := by
  intro h
  exact h.2.1 (by simp [translationPacket, proofPacket, formalizationLineage])

theorem translation_proof_have_no_additiveRevisionLicense
    (adjudication : CertifiedAdjudication) :
    ¬ AdditiveRevisionLicense (translationPacket adjudication)
      (proofPacket adjudication) := by
  intro license
  exact translation_proof_not_sourceDisjoint adjudication license.sourceDisjoint

/-- A separately sourced review is disjoint from the proof packet under the
declared lineage model and therefore receives an additive-revision license. -/
theorem independentReview_sourceDisjoint
    (adjudication : CertifiedAdjudication) (reviewId : Nat) :
    (proofPacket adjudication).SourceDisjoint
      (independentReviewPacket adjudication reviewId) := by
  simp [proofPacket, independentReviewPacket, entryLineage,
    formalizationLineage, SourcePacket.SourceDisjoint]

theorem independentReview_licenses_additiveRevision
    (adjudication : CertifiedAdjudication) (reviewId : Nat) :
    AdditiveRevisionLicense (proofPacket adjudication)
      (independentReviewPacket adjudication reviewId) :=
  sourceDisjoint_licenses_additiveRevision _ _
    (independentReview_sourceDisjoint adjudication reviewId)

/-- Graded confidence in the text-to-specification translation remains a
calibrated-input question.  This operation merely applies the supplied source
profile; it does not infer one from the existence or length of a proof. -/
def translationEvidence (profile : ReliabilityProfile) : BinEvNat :=
  reliabilityAdjust profile ⟨1, 0⟩

theorem perfectTranslationProfile_preserves_confirmation :
    translationEvidence perfectProfile = ⟨1, 0⟩ := by
  exact perfect_preserves ⟨1, 0⟩

def certifiedProofPackets : List Packet :=
  certifiedAdjudications.map proofPacket

theorem certifiedProofPacket_count : certifiedProofPackets.length = 33 := by
  simpa [certifiedProofPackets] using certifiedAdjudication_count

#print axioms certifiedAdjudication_is_factive
#print axioms proofPacket_contributes_one_positive_count
#print axioms duplicateProof_not_sourceDisjoint
#print axioms translation_proof_have_no_additiveRevisionLicense
#print axioms independentReview_licenses_additiveRevision
#print axioms perfectTranslationProfile_preserves_confirmation
#print axioms certifiedProofPacket_count

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.OEISAdjudicationEvidence
