import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.DesirableGambles

namespace Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex

open Mettapedia.PLN.WorldModel

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNInformationGeometry
open Mettapedia.PLN.TruthValues.PLNAmplitudePhase
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.Algebra.TwoDimClassification
open scoped ENNReal

universe u v


/-! ## Information-geometric coordinates -/

/-- Binary mean/concentration coordinates are lossless for positive total
evidence. -/
theorem binary_mean_concentration_is_lossless
    (e : BinaryCounts) (hTotal : e.total ≠ 0) :
    (BetaMeanConcentration.fromCounts e).decodeCounts =
      (e.nPlus, e.nMinus) :=
  BetaMeanConcentration.decode_fromCounts e hTotal

/-- Categorical mean-vector/concentration coordinates are lossless for positive
total evidence, pointwise in each category. -/
theorem categorical_mean_concentration_is_lossless
    {k : ℕ} (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k)
    (hTotal : e.total ≠ 0) (i : Fin k) :
    (DirichletMeanConcentration.fromCounts e).decodeCounts i =
      (e.counts i : ℝ) :=
  DirichletMeanConcentration.decode_fromCounts e hTotal i

/-- Mean/concentration alone does not choose the binary confidence link. -/
theorem beta_coordinate_does_not_force_confidence_link :
    let z : BetaMeanConcentration := ⟨1 / 2, 1⟩
    plnConfidenceLink 1 (by norm_num) z ≠
      reserveHalfLink 1 (by norm_num) z :=
  same_beta_coordinate_two_valid_confidence_links_differ

/-- Mean-vector/concentration alone does not choose the categorical confidence
link. -/
theorem dirichlet_coordinate_does_not_force_confidence_link :
    let z : DirichletMeanConcentration 3 := ⟨fun _ => 1 / 3, 1⟩
    dirichletPLNConfidenceLink 1 (by norm_num) z ≠
      dirichletReserveHalfLink 1 (by norm_num) z :=
  same_dirichlet_coordinate_two_valid_confidence_links_differ

/-! ## Typed revision -/

/-- Typed binary revision built from evidence counts decodes to componentwise
evidence addition. -/
theorem typed_binary_revision_is_evidence_addition
    (χ : EvidenceWeightCoordinate) (e₁ e₂ : BinaryCounts)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (hSum : e₁.total + e₂.total ≠ 0) :
    (TypedSTV.revise (TypedSTV.fromCounts χ e₁)
      (TypedSTV.fromCounts χ e₂)).decodeCounts =
        ((e₁.add e₂).nPlus, (e₁.add e₂).nMinus) :=
  typedSTV_revision_fromCounts_decodes_added_counts χ e₁ e₂ h₁ h₂ hSum

/-- Typed categorical revision built from evidence counts decodes to
componentwise categorical evidence addition. -/
theorem typed_categorical_revision_is_evidence_addition
    {k : ℕ} (χ : EvidenceWeightCoordinate)
    (e₁ e₂ : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (hSum : (e₁.total : ℝ) + (e₂.total : ℝ) ≠ 0) (i : Fin k) :
    (TypedCategoricalTruth.revise
      (TypedCategoricalTruth.fromCounts χ e₁)
      (TypedCategoricalTruth.fromCounts χ e₂)).decodeCounts i =
        ((e₁ + e₂).counts i : ℝ) :=
  typedCategorical_revision_fromCounts_decodes_added_counts
    χ e₁ e₂ h₁ h₂ hSum i

/-! ## Subjective-Logic coordinate dictionary -/

/-- Subjective-Logic projected probability with base rate and prior weight is
the asymmetric Beta posterior mean in the EvidenceBeta/Revision core. -/
theorem subjective_logic_projection_is_beta_posterior_mean
    (nPos nNeg baseRate priorWeight : ℝ) :
    (Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.weightedOpinion
        nPos nNeg baseRate priorWeight).projected =
      Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.asymmetricBetaPosteriorMean
        nPos nNeg baseRate priorWeight :=
  Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.weightedOpinion_projected_eq_asymmetricBetaPosteriorMean
    nPos nNeg baseRate priorWeight

/-- Raw Subjective-Logic evidence fusion is evidence addition before projection,
not fusion of already-prior-loaded displayed probabilities. -/
theorem subjective_logic_raw_fusion_is_shared_prior_beta_projection
    (n₁Pos n₁Neg n₂Pos n₂Neg : ℕ) :
    (Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.laplaceOpinion
      (n₁Pos + n₂Pos) (n₁Neg + n₂Neg)).projected =
      (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.withUniformPrior
        (n₁Pos + n₂Pos) (n₁Neg + n₂Neg)).posteriorMean :=
  Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.laplaceOpinion_projected_rawEvidenceAdd_eq_EvidenceBetaParams_posteriorMean
    n₁Pos n₁Neg n₂Pos n₂Neg

/-- The MeTTa-facing raw-count Revision rule is exactly count addition before
readout, matching the Subjective-Logic / EvidenceBeta sufficient-statistic
dictionary. -/
theorem subjective_logic_raw_count_revision_is_evidence_addition
    (e₁ e₂ : BinaryCounts)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0) :
    let tv₁ := Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNCountSTV e₁ h₁
    let tv₂ := Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNCountSTV e₂ h₂
    (Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNRevision tv₁ tv₂).strength =
        (e₁.add e₂).strength ∧
      (Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNRevision tv₁ tv₂).confidence =
        Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNOddsCoordinate.encode
          ((e₁.add e₂).total) :=
  Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.semanticPLNRevision_rawCountSTV_eq_added_count_view
    e₁ e₂ h₁ h₂

/-- Guardrail: revising two prior-loaded projected readouts is not the same
operation as one shared-prior update over combined raw evidence. -/
theorem subjective_logic_prior_loaded_revision_not_shared_prior :
    (Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNRevision
        Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.priorLoadedProjectionSTV_6_0
        Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.priorLoadedProjectionSTV_0_2).strength ≠
      (Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.laplaceOpinion 6 2).projected :=
  Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.semanticPLNRevision_priorLoadedProjection_ne_sharedPrior

/-- Proof-carrying Subjective-Logic / EvidenceBeta profile.  It packages the
coordinate dictionary, the raw-evidence fusion law, and the prior-loaded
projection guardrail that keeps displayed probabilities from being revised as
if they were raw sufficient statistics. -/
structure SubjectiveLogicEvidenceBetaProfile where
  projectionIsBetaPosteriorMean :
    ∀ nPos nNeg baseRate priorWeight : ℝ,
      (Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.weightedOpinion
          nPos nNeg baseRate priorWeight).projected =
        Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.asymmetricBetaPosteriorMean
          nPos nNeg baseRate priorWeight
  rawFusionIsSharedPriorBetaProjection :
    ∀ n₁Pos n₁Neg n₂Pos n₂Neg : ℕ,
      (Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.laplaceOpinion
        (n₁Pos + n₂Pos) (n₁Neg + n₂Neg)).projected =
        (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.withUniformPrior
          (n₁Pos + n₂Pos) (n₁Neg + n₂Neg)).posteriorMean
  rawCountRevisionIsEvidenceAddition :
    ∀ (e₁ e₂ : BinaryCounts)
      (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0),
      let tv₁ := Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNCountSTV e₁ h₁
      let tv₂ := Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNCountSTV e₂ h₂
      (Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNRevision tv₁ tv₂).strength =
          (e₁.add e₂).strength ∧
        (Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNRevision tv₁ tv₂).confidence =
          Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNOddsCoordinate.encode
            ((e₁.add e₂).total)
  priorLoadedRevisionNotSharedPrior :
    (Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNRevision
        Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.priorLoadedProjectionSTV_6_0
        Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.priorLoadedProjectionSTV_0_2).strength ≠
      (Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.laplaceOpinion 6 2).projected
  priorLoadedRevisionStrength :
    (Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore.semanticPLNRevision
        Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.priorLoadedProjectionSTV_6_0
        Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.priorLoadedProjectionSTV_0_2).strength =
      (23 / 32 : ℝ)
  sharedPriorCombinedProjection :
    (Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.laplaceOpinion 6 2).projected =
      (7 / 10 : ℝ)

/-- Public profile for the Subjective-Logic / EvidenceBeta dictionary used by
the Revision jewel and its MeTTa witnesses. -/
noncomputable def subjectiveLogicEvidenceBetaProfile : SubjectiveLogicEvidenceBetaProfile where
  projectionIsBetaPosteriorMean :=
    subjective_logic_projection_is_beta_posterior_mean
  rawFusionIsSharedPriorBetaProjection :=
    subjective_logic_raw_fusion_is_shared_prior_beta_projection
  rawCountRevisionIsEvidenceAddition :=
    subjective_logic_raw_count_revision_is_evidence_addition
  priorLoadedRevisionNotSharedPrior :=
    subjective_logic_prior_loaded_revision_not_shared_prior
  priorLoadedRevisionStrength :=
    Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.semanticPLNRevision_priorLoadedProjection_strength_eq
  sharedPriorCombinedProjection :=
    Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge.sharedPriorCombinedProjection_6_2_eq

/-! ## Chapter-12 ASSOC/PAT provenance index -/

/-- Public index name for the live Chapter-12 ASSOC/PAT source-provenance
consumer: the two demo packets are exact source packets, and guarded list
Revision rejects their shared provenance rather than double-counting it. -/
theorem assoc_pat_exact_packets_are_exact_and_guarded_revision_rejects_overlap :
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.ExactStampPacket
        Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence ∧
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.ExactStampPacket
        Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence ∧
        Mettapedia.KR.ConceptGeometry.AbstractInheritance.StampedBinaryEvidence.guardedListRevise
          [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
            Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence] = none :=
  Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.assoc_pat_exactPacket_consumer_canary

/-- Public index name for the overlap-corrected ASSOC/PAT packet merge: exact
rule-family packets merge to the packet over their source-stamp union. -/
theorem assoc_pat_exact_packet_joint_merge_is_source_union :
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.packetJointMerge
        [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
          Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence] =
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.stampSetPacket
        (Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.packetListUnion
          [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
            Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence]) :=
  Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.assoc_pat_packetJointMerge_eq_source_union

/-- Public index name for duplicate-source absorption in the concrete ASSOC/PAT
consumer surface. -/
theorem assoc_pat_exact_packet_duplicate_absorbs :
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.packetJointMerge
        [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
          Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
          Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence] =
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.packetJointMerge
        [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
          Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence] :=
  Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.assoc_pat_packetJointMerge_duplicate_absorb

/-- Public index name for the concrete Chapter-12 noncollapse guardrail: PAT
strictly extends ASSOC on the `bird/bird` toy concept because the consequent
extent channel is nonempty. -/
theorem assoc_pat_base_score_bird_bird_lt_pat_base_score_bird_bird :
    Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.assocBaseScore
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird <
      Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.patBaseScore
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird :=
  Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.assocBaseScore_birdBird_lt_patBaseScore_birdBird

/-- Public index name for the evidence-level Chapter-12 noncollapse guardrail:
the ASSOC and PAT query channels remain distinct at the rule-facing evidence
surface, not only in their raw score definitions. -/
theorem assoc_pat_evidence_bird_bird_ne_pat_evidence_bird_bird :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.DemoState)
        (Atom := Mettapedia.KR.ConceptOntology.Examples.Concept)
        (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.DemoPairQuery)
        1
        Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.pairEnc
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird ≠
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalPATEvidence
        (State := Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.DemoState)
        (Atom := Mettapedia.KR.ConceptOntology.Examples.Concept)
        (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.DemoPairQuery)
        1
        Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.pairEnc
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird :=
  Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.assocEvidence_birdBird_ne_patEvidence_birdBird

/-- Public index name for the negative guardrail showing that a mixed combiner
which ignores its extensional coordinate can equate mixed evidence while
extensional evidence differs. -/
theorem assoc_pat_ignore_extensional_combiner_collapses_extensional_channel :
    ∃ x y assoc pat : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence,
      (fun _ assoc pat => assoc + pat) x assoc pat =
          (fun _ assoc pat => assoc + pat) y assoc pat ∧
        x ≠ y :=
  Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.ignoreExtensionalCombiner_mixedEvidence_eq_without_extensionalEvidence_eq

/-- Public index name for the matching cancellativity guardrail: the
ASSOC/PAT-only mixed combiner is not left-cancellable in the extensional
coordinate. -/
theorem assoc_pat_ignore_extensional_combiner_not_left_cancellable :
    ¬ (∀ {x y assoc pat : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence},
      (fun _ assoc pat => assoc + pat) x assoc pat =
          (fun _ assoc pat => assoc + pat) y assoc pat →
        x = y) :=
  Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.ignoreExtensionalCombiner_not_leftCancellable

/-- Public index name for the negative guardrail showing that ASSOC/PAT
monotonicity alone does not force mixed-channel monotonicity when the
extensional coordinate drops. -/
theorem assoc_pat_mixed_monotonicity_requires_extensional_monotonicity :
    ∃ ext₁ ext₂ assoc₁ assoc₂ pat₁ pat₂ :
        Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence,
      assoc₁ ≤ assoc₂ ∧
        pat₁ ≤ pat₂ ∧
        ¬ ext₁ ≤ ext₂ ∧
        ¬ (ext₁ + assoc₁ + pat₁ ≤ ext₂ + assoc₂ + pat₂) :=
  Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLAssocPatBridge.mixedEvidence_mono_requires_extensional_mono_counterexample

/-- Proof-carrying profile for the current Chapter-12 ASSOC/PAT consumer
surface. It packages exact-provenance positive cases, the finite-table and
formed-concept source packages, the formed-concept semantic-layer ASSOC/PAT
equality and monotonicity theorems, the formed-concept mixed boundary and
monotonicity theorems, the pattern-coded semantic-layer consumer, PAT-vs-ASSOC
noncollapse, and mixed-channel side-condition guardrails. -/
structure AssocPatChapter12ConsumerProfile where
  exactPacketsAndOverlapGuard :
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.ExactStampPacket
        Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence ∧
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.ExactStampPacket
        Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence ∧
        Mettapedia.KR.ConceptGeometry.AbstractInheritance.StampedBinaryEvidence.guardedListRevise
          [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
            Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence] = none
  exactPacketJointMergeIsSourceUnion :
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.packetJointMerge
        [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
          Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence] =
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.stampSetPacket
        (Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.packetListUnion
          [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
            Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence])
  duplicateExactPacketAbsorbs :
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.packetJointMerge
        [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
          Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
          Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence] =
      Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.packetJointMerge
        [Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.penguinBirdStampedEvidence,
          Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.birdBirdStampedEvidence]
  formedConceptChapter12Source :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.FormedConceptChapter12SourceProfile
  formedConceptSemanticLayerAssocPatEquality :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.FormedConceptSemanticLayerAssocPatEqualityProfile.{0, 0, 0}
  formedConceptSemanticLayerAssocPatMonotonicity :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.FormedConceptSemanticLayerAssocPatMonotonicityProfile.{0, 0, 0}
  formedConceptMixedSemanticLayerBoundary :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.FormedConceptMixedSemanticLayerBoundaryProfile.{0, 0, 0}
  formedConceptMixedSemanticLayerMonotonicity :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.FormedConceptMixedSemanticLayerMonotonicityProfile.{0, 0, 0}
  finiteTableChapter12Source :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.FiniteTableChapter12SourceProfile
  patternCodedChapter12Source :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.PatternCodedChapter12SourceProfile
  patternCodedSemanticLayerConsumer :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.PatternCodedSemanticLayerConsumerProfile.{0, 0, 0}
  richPatternCodedChapter12Source :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.RichPatternCodedChapter12SourceProfile
  richPatternCodedSemanticLayerConsumer :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.RichPatternCodedSemanticLayerConsumerProfile.{0, 0, 0}
  baseScorePATStrictlyExtendsASSOC :
    Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.assocBaseScore
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird <
      Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.patBaseScore
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
  evidenceChannelsDoNotCollapse :
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.DemoState)
        (Atom := Mettapedia.KR.ConceptOntology.Examples.Concept)
        (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.DemoPairQuery)
        1
        Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.pairEnc
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird ≠
      Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalPATEvidence
        (State := Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.DemoState)
        (Atom := Mettapedia.KR.ConceptOntology.Examples.Concept)
        (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.DemoPairQuery)
        1
        Mettapedia.PLN.ConceptGeometry.AssocPat.AbstractInheritanceIntensionalDemo.pairEnc
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
        Mettapedia.KR.ConceptOntology.Examples.Concept.bird
  ignoreExtensionalCombinerCollapsesExtensionalChannel :
    ∃ x y assoc pat : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence,
      (fun _ assoc pat => assoc + pat) x assoc pat =
          (fun _ assoc pat => assoc + pat) y assoc pat ∧
        x ≠ y
  ignoreExtensionalCombinerNotLeftCancellable :
    ¬ (∀ {x y assoc pat : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence},
      (fun _ assoc pat => assoc + pat) x assoc pat =
          (fun _ assoc pat => assoc + pat) y assoc pat →
        x = y)
  mixedMonotonicityRequiresExtensionalMonotonicity :
    ∃ ext₁ ext₂ assoc₁ assoc₂ pat₁ pat₂ :
        Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence,
      assoc₁ ≤ assoc₂ ∧
        pat₁ ≤ pat₂ ∧
        ¬ ext₁ ≤ ext₂ ∧
        ¬ (ext₁ + assoc₁ + pat₁ ≤ ext₂ + assoc₂ + pat₂)

/-- Public profile for the current Chapter-12 ASSOC/PAT exact-provenance and
noncollapse consumer surface. -/
def assocPatChapter12ConsumerProfile : AssocPatChapter12ConsumerProfile where
  exactPacketsAndOverlapGuard :=
    assoc_pat_exact_packets_are_exact_and_guarded_revision_rejects_overlap
  exactPacketJointMergeIsSourceUnion :=
    assoc_pat_exact_packet_joint_merge_is_source_union
  duplicateExactPacketAbsorbs :=
    assoc_pat_exact_packet_duplicate_absorbs
  formedConceptChapter12Source :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.formedConceptChapter12SourceProfile
  formedConceptSemanticLayerAssocPatEquality :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.formedConceptSemanticLayerAssocPatEqualityProfile.{0, 0, 0}
  formedConceptSemanticLayerAssocPatMonotonicity :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.formedConceptSemanticLayerAssocPatMonotonicityProfile.{0, 0, 0}
  formedConceptMixedSemanticLayerBoundary :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.formedConceptMixedSemanticLayerBoundaryProfile.{0, 0, 0}
  formedConceptMixedSemanticLayerMonotonicity :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.formedConceptMixedSemanticLayerMonotonicityProfile.{0, 0, 0}
  finiteTableChapter12Source :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.finiteTableChapter12SourceProfile
  patternCodedChapter12Source :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.patternCodedChapter12SourceProfile
  patternCodedSemanticLayerConsumer :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.patternCodedSemanticLayerConsumerProfile.{0, 0, 0}
  richPatternCodedChapter12Source :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.richPatternCodedChapter12SourceProfile
  richPatternCodedSemanticLayerConsumer :=
    Mettapedia.PLN.ConceptGeometry.AssocPat.PLNHigherOrderHOLEmpiricalAssocPatBridge.richPatternCodedSemanticLayerConsumerProfile.{0, 0, 0}
  baseScorePATStrictlyExtendsASSOC :=
    assoc_pat_base_score_bird_bird_lt_pat_base_score_bird_bird
  evidenceChannelsDoNotCollapse :=
    assoc_pat_evidence_bird_bird_ne_pat_evidence_bird_bird
  ignoreExtensionalCombinerCollapsesExtensionalChannel :=
    assoc_pat_ignore_extensional_combiner_collapses_extensional_channel
  ignoreExtensionalCombinerNotLeftCancellable :=
    assoc_pat_ignore_extensional_combiner_not_left_cancellable
  mixedMonotonicityRequiresExtensionalMonotonicity :=
    assoc_pat_mixed_monotonicity_requires_extensional_monotonicity


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
