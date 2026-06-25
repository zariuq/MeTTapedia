import Mettapedia.KR.ConceptGeometry.IntensionalInheritanceAll
import Mettapedia.KR.ConceptOntology.Examples

/-!
# Intensional Inheritance Entry-Point Canary

This file exercises the focused `IntensionalInheritanceAll` import surface by
pulling the tiny empirical 2x2 inheritance object through the new factor-graph /
VE / BP bridge theorems.
-/

namespace Mettapedia.KR.ConceptGeometry.Examples.IntensionalInheritanceAllCanary

open Mettapedia.KR.ConceptGeometry.IntensionalInheritance
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.KR.ConceptOntology.Examples

instance : Nonempty (MembershipCounts.EmpiricalObject MembershipCounts.positiveExample) :=
  ⟨Sum.inr (Sum.inr (Sum.inr ⟨0, by decide⟩))⟩

local instance : Nonempty Creature := ⟨Creature.tweety⟩

local instance : Fintype Creature where
  elems := {Creature.tweety, Creature.pingu, Creature.plane}
  complete := by
    intro x
    cases x <;> simp

inductive ToyMembershipObservation where
  | seen (x : Creature) (c : Concept)
  deriving DecidableEq, Repr

def positiveExampleTable : FiniteWitnessFeatureTable where
  neither := MembershipCounts.positiveExample.neither
  witnessOnly := MembershipCounts.positiveExample.witnessOnly
  featureOnly := MembershipCounts.positiveExample.featureOnly
  both := MembershipCounts.positiveExample.both
  total_pos := MembershipCounts.positiveExample.total_pos

theorem positiveExample_prior_eq_ve_ratio :
    MembershipCounts.priorProbWitness MembershipCounts.positiveExample =
      (MembershipCounts.veWeight MembershipCounts.positiveExample
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        MembershipCounts.veWeight MembershipCounts.positiveExample [] := by
  simpa using
    MembershipCounts.priorProbWitness_eq_veWeight_ratio
      MembershipCounts.positiveExample

theorem positiveExample_semantic_prior_eq_ve_ratio :
    Interpretation.finitePriorProb
        (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
        MembershipConcept.witness =
      (MembershipCounts.veWeight MembershipCounts.positiveExample
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        MembershipCounts.veWeight MembershipCounts.positiveExample [] := by
  simpa using
    MembershipCounts.finitePriorProb_semanticInterpretation_witness_eq_veWeight_ratio
      MembershipCounts.positiveExample

theorem positiveExample_ext_eq_bp_ratio :
    MembershipCounts.extensionalInheritance MembershipCounts.positiveExample =
      if MembershipCounts.featureMessage MembershipCounts.positiveExample true = 0 then
        0
      else
        (MembershipCounts.jointFactorBelief MembershipCounts.positiveExample
          (MembershipCounts.ttJointAssign MembershipCounts.positiveExample) : ℝ) /
          MembershipCounts.featureMessage MembershipCounts.positiveExample true := by
  simpa using
    MembershipCounts.extensionalInheritance_eq_bp_ratio
      MembershipCounts.positiveExample

theorem positiveExample_semantic_ext_eq_bp_ratio :
    Interpretation.finiteExtensionalProb
        (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
        MembershipConcept.feature
        MembershipConcept.witness =
      if MembershipCounts.featureMessage MembershipCounts.positiveExample true = 0 then
        0
      else
        (MembershipCounts.jointFactorBelief MembershipCounts.positiveExample
          (MembershipCounts.ttJointAssign MembershipCounts.positiveExample) : ℝ) /
          MembershipCounts.featureMessage MembershipCounts.positiveExample true := by
  simpa using
    MembershipCounts.finiteExtensionalProb_semanticInterpretation_feature_witness_eq_bp_ratio
      MembershipCounts.positiveExample

theorem positiveExample_score_eq_ve_query_score :
    MembershipCounts.pointwiseIntensionalScoreBits MembershipCounts.positiveExample =
      logRatioInformationGainFromEvidence
        (if MembershipCounts.veWeight MembershipCounts.positiveExample
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (MembershipCounts.veWeight MembershipCounts.positiveExample
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            MembershipCounts.veWeight MembershipCounts.positiveExample
              [⟨MembershipConcept.feature, true⟩])
        ((MembershipCounts.veWeight MembershipCounts.positiveExample
            [⟨MembershipConcept.witness, true⟩] : ℝ) /
          MembershipCounts.veWeight MembershipCounts.positiveExample []) := by
  simpa using
    MembershipCounts.pointwiseIntensionalScoreBits_eq_ve_query_score
      MembershipCounts.positiveExample

theorem positiveExample_semantic_score_eq_ve_query_score :
    Interpretation.finitePointwiseLogRatioBits
        (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
        MembershipConcept.feature
        MembershipConcept.witness =
      logRatioInformationGainFromEvidence
        (if MembershipCounts.veWeight MembershipCounts.positiveExample
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (MembershipCounts.veWeight MembershipCounts.positiveExample
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            MembershipCounts.veWeight MembershipCounts.positiveExample
              [⟨MembershipConcept.feature, true⟩])
        ((MembershipCounts.veWeight MembershipCounts.positiveExample
            [⟨MembershipConcept.witness, true⟩] : ℝ) /
          MembershipCounts.veWeight MembershipCounts.positiveExample []) := by
  simpa using
    MembershipCounts.finitePointwiseLogRatioBits_semanticInterpretation_feature_witness_eq_ve_query_score
      MembershipCounts.positiveExample

theorem positiveTable_witnessPrior_eq_ve_ratio :
    FiniteWitnessFeatureTable.witnessPrior positiveExampleTable =
      (FiniteWitnessFeatureTable.veWeight positiveExampleTable
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight positiveExampleTable [] := by
  simpa [positiveExampleTable] using
    FiniteWitnessFeatureTable.witnessPrior_eq_veWeight_ratio positiveExampleTable

theorem positiveTable_featureToWitness_eq_bp_ratio :
    FiniteWitnessFeatureTable.featureToWitnessStrength positiveExampleTable =
      if FiniteWitnessFeatureTable.featureMessage positiveExampleTable true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief positiveExampleTable
          (FiniteWitnessFeatureTable.ttJointAssign positiveExampleTable) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage positiveExampleTable true := by
  simpa [positiveExampleTable] using
    FiniteWitnessFeatureTable.featureToWitnessStrength_eq_bp_ratio positiveExampleTable

theorem positiveExample_generic_semantic_prior_eq_generated_ve_ratio :
    Interpretation.finitePriorProb
        (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
        MembershipConcept.witness =
      (FiniteWitnessFeatureTable.veWeight
        (Interpretation.toFiniteWitnessFeatureTable
          (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
          MembershipConcept.feature
          MembershipConcept.witness)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
            MembershipConcept.feature
            MembershipConcept.witness) [] := by
  simpa using
    Interpretation.finitePriorProb_eq_veWeight_ratio
      (I := MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
      (feature := MembershipConcept.feature)
      (witness := MembershipConcept.witness)

theorem positiveExample_semantic_prior_tv_strength_eq_generated_ve_ratio :
    (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.conceptPriorTV
        (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
        MembershipConcept.witness).strength =
      (FiniteWitnessFeatureTable.veWeight
        (Interpretation.toFiniteWitnessFeatureTable
          (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
          MembershipConcept.feature
          MembershipConcept.witness)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
            MembershipConcept.feature
            MembershipConcept.witness) [] := by
  simpa using positiveExample_generic_semantic_prior_eq_generated_ve_ratio

theorem positiveExample_semantic_induction_conf_eq_min_capped :
    (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.truthInduction
      (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.stvToWMTruthValue
        (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.conceptPriorTV
          (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
          MembershipConcept.feature))
      (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.stvToWMTruthValue
        (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.conceptPriorTV
          (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
          MembershipConcept.witness))
      (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.stvToWMTruthValue
        (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.conceptPriorTV
          (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
          MembershipConcept.feature))
      (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.stvToWMTruthValue
        (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.inheritanceTV
          (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
          MembershipConcept.feature
          MembershipConcept.witness))
      (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.stvToWMTruthValue
        (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.inheritanceTV
          (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
          MembershipConcept.witness
          MembershipConcept.feature))).c =
    min
      (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.capConf
        (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.inheritanceTV
          (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
          MembershipConcept.feature
          MembershipConcept.witness).confidence)
      (Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions.capConf
        (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.inheritanceTV
          (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
          MembershipConcept.witness
          MembershipConcept.feature).confidence) := by
  simpa using
    Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.inheritanceTV_truthInduction_conf_eq_min_capped_conceptPrior
      (I := MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
      (sub := MembershipConcept.feature)
      (mid := MembershipConcept.witness)
      (super := MembershipConcept.feature)

theorem positiveExample_generic_semantic_ext_eq_generated_bp_ratio :
    Interpretation.finiteExtensionalProb
        (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
        MembershipConcept.feature
        MembershipConcept.witness =
      if FiniteWitnessFeatureTable.featureMessage
          (Interpretation.toFiniteWitnessFeatureTable
            (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
            MembershipConcept.feature
            MembershipConcept.witness) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (Interpretation.toFiniteWitnessFeatureTable
            (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
            MembershipConcept.feature
            MembershipConcept.witness)
          (FiniteWitnessFeatureTable.ttJointAssign
            (Interpretation.toFiniteWitnessFeatureTable
              (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
              MembershipConcept.feature
              MembershipConcept.witness)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (Interpretation.toFiniteWitnessFeatureTable
              (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
              MembershipConcept.feature
              MembershipConcept.witness) true := by
  simpa using
    Interpretation.finiteExtensionalProb_eq_bp_ratio
      (I := MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
      (feature := MembershipConcept.feature)
      (witness := MembershipConcept.witness)

theorem positiveExample_generic_semantic_score_eq_generated_ve_query_score :
    Interpretation.finitePointwiseLogRatioBits
        (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
        MembershipConcept.feature
        MembershipConcept.witness =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
              MembershipConcept.feature
              MembershipConcept.witness)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
              MembershipConcept.feature
              MembershipConcept.witness)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
                MembershipConcept.feature
                MembershipConcept.witness)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
              MembershipConcept.feature
              MembershipConcept.witness)
            [⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
              MembershipConcept.feature
              MembershipConcept.witness) []) := by
  simpa using
    Interpretation.finitePointwiseLogRatioBits_eq_ve_query_score
      (I := MembershipCounts.semanticInterpretation MembershipCounts.positiveExample)
      (feature := MembershipConcept.feature)
      (witness := MembershipConcept.witness)

noncomputable abbrev toyMembershipContext :=
  Mettapedia.KR.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
    (State := ToyState) membershipBuilder

noncomputable abbrev toySemanticInterpretation :=
  EvidenceMembershipContext.crispInterpretationAt toyMembershipContext gate toyWM

noncomputable abbrev toyPenguinBirdTable :=
  Interpretation.toFiniteWitnessFeatureTable
    toySemanticInterpretation Concept.penguin Concept.bird

noncomputable abbrev toyBirdFlyTable :=
  Interpretation.toFiniteWitnessFeatureTable
    toySemanticInterpretation Concept.bird Concept.fly

noncomputable def toyObservationSurface :
    Mettapedia.KR.ConceptOntology.ObservationSurface
      ToyMembershipObservation Creature Concept BinaryEvidence where
  observe o q :=
    match o with
    | .seen x c =>
        if q.1 = x ∧ q.2 = c then yes else 0

noncomputable def toyObservationData : Multiset ToyMembershipObservation :=
  ({ToyMembershipObservation.seen Creature.tweety Concept.bird} : Multiset _) +
    {ToyMembershipObservation.seen Creature.tweety Concept.bird} +
    {ToyMembershipObservation.seen Creature.tweety Concept.fly} +
    {ToyMembershipObservation.seen Creature.tweety Concept.fly} +
    {ToyMembershipObservation.seen Creature.pingu Concept.bird} +
    {ToyMembershipObservation.seen Creature.pingu Concept.bird} +
    {ToyMembershipObservation.seen Creature.pingu Concept.penguin} +
    {ToyMembershipObservation.seen Creature.pingu Concept.penguin}

noncomputable def toyObservationContext :
    letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
      Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
    Mettapedia.KR.ConceptOntology.EvidenceMembershipContext
      (Multiset ToyMembershipObservation) Creature Concept BinaryEvidence := by
  letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
    Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
  exact toyObservationSurface.inducedContext

noncomputable def toyObservationInterpretation :
    letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
      Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
    Interpretation Concept Creature Concept := by
  letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
    Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
  exact EvidenceMembershipContext.crispInterpretationAt toyObservationContext gate toyObservationData

noncomputable def toyObservationPenguinBirdTable :
    letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
      Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
    FiniteWitnessFeatureTable := by
  letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
    Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
  exact Interpretation.toFiniteWitnessFeatureTable
    toyObservationInterpretation Concept.penguin Concept.bird

noncomputable def toyObservationBirdFlyTable :
    letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
      Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
    FiniteWitnessFeatureTable := by
  letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
    Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
  exact Interpretation.toFiniteWitnessFeatureTable
    toyObservationInterpretation Concept.bird Concept.fly

theorem toy_penguinBird_generic_semantic_prior_eq_generated_ve_ratio :
    Interpretation.finitePriorProb toySemanticInterpretation Concept.bird =
      (FiniteWitnessFeatureTable.veWeight
        toyPenguinBirdTable
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight toyPenguinBirdTable [] := by
  simpa [toySemanticInterpretation, toyMembershipContext, toyPenguinBirdTable] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.MembershipQueryBuilderBridge.finitePriorProb_toEvidenceMembershipContext_eq_veWeight_ratio
      (enc := membershipBuilder)
      (G := gate)
      (W := toyWM)
      (feature := Concept.penguin)
      (witness := Concept.bird)

theorem toy_penguinBird_generic_semantic_ext_eq_generated_bp_ratio :
    Interpretation.finiteExtensionalProb
        toySemanticInterpretation
        Concept.penguin
        Concept.bird =
      if FiniteWitnessFeatureTable.featureMessage toyPenguinBirdTable true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          toyPenguinBirdTable
          (FiniteWitnessFeatureTable.ttJointAssign toyPenguinBirdTable) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage toyPenguinBirdTable true := by
  simpa [toySemanticInterpretation, toyMembershipContext, toyPenguinBirdTable] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.MembershipQueryBuilderBridge.finiteExtensionalProb_toEvidenceMembershipContext_eq_bp_ratio
      (enc := membershipBuilder)
      (G := gate)
      (W := toyWM)
      (feature := Concept.penguin)
      (witness := Concept.bird)

theorem toy_penguinBird_generic_semantic_score_eq_generated_ve_query_score :
    Interpretation.finitePointwiseLogRatioBits
        toySemanticInterpretation
        Concept.penguin
        Concept.bird =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            toyPenguinBirdTable
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            toyPenguinBirdTable
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              toyPenguinBirdTable
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
            toyPenguinBirdTable
            [⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight toyPenguinBirdTable []) := by
  simpa [toySemanticInterpretation, toyMembershipContext, toyPenguinBirdTable] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.MembershipQueryBuilderBridge.finitePointwiseLogRatioBits_toEvidenceMembershipContext_eq_ve_query_score
      (enc := membershipBuilder)
      (G := gate)
      (W := toyWM)
      (feature := Concept.penguin)
      (witness := Concept.bird)

theorem toy_birdFly_generic_semantic_ext_eq_generated_bp_ratio :
    Interpretation.finiteExtensionalProb
        toySemanticInterpretation
        Concept.bird
        Concept.fly =
      if FiniteWitnessFeatureTable.featureMessage toyBirdFlyTable true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          toyBirdFlyTable
          (FiniteWitnessFeatureTable.ttJointAssign toyBirdFlyTable) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage toyBirdFlyTable true := by
  simpa [toySemanticInterpretation, toyMembershipContext, toyBirdFlyTable] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.MembershipQueryBuilderBridge.finiteExtensionalProb_toEvidenceMembershipContext_eq_bp_ratio
      (enc := membershipBuilder)
      (G := gate)
      (W := toyWM)
      (feature := Concept.bird)
      (witness := Concept.fly)

theorem toy_birdFly_generic_semantic_score_eq_generated_ve_query_score :
    Interpretation.finitePointwiseLogRatioBits
        toySemanticInterpretation
        Concept.bird
        Concept.fly =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            toyBirdFlyTable
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            toyBirdFlyTable
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              toyBirdFlyTable
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
            toyBirdFlyTable
            [⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight toyBirdFlyTable []) := by
  simpa [toySemanticInterpretation, toyMembershipContext, toyBirdFlyTable] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.MembershipQueryBuilderBridge.finitePointwiseLogRatioBits_toEvidenceMembershipContext_eq_ve_query_score
      (enc := membershipBuilder)
      (G := gate)
      (W := toyWM)
      (feature := Concept.bird)
      (witness := Concept.fly)

theorem toyObservation_penguinBird_prior_eq_generated_ve_ratio :
    letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
      Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
    Interpretation.finitePriorProb toyObservationInterpretation Concept.bird =
      (FiniteWitnessFeatureTable.veWeight
        toyObservationPenguinBirdTable
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight toyObservationPenguinBirdTable [] := by
  letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
    Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
  simpa [toyObservationContext, toyObservationInterpretation, toyObservationPenguinBirdTable] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.ObservationSurfaceBridge.finitePriorProb_inducedContext_eq_veWeight_ratio
      (S := toyObservationSurface)
      (G := gate)
      (σ := toyObservationData)
      (feature := Concept.penguin)
      (witness := Concept.bird)

theorem toyObservation_penguinBird_ext_eq_generated_bp_ratio :
    letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
      Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
    Interpretation.finiteExtensionalProb
        toyObservationInterpretation
        Concept.penguin
        Concept.bird =
      if FiniteWitnessFeatureTable.featureMessage toyObservationPenguinBirdTable true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          toyObservationPenguinBirdTable
          (FiniteWitnessFeatureTable.ttJointAssign toyObservationPenguinBirdTable) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage toyObservationPenguinBirdTable true := by
  letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
    Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
  simpa [toyObservationContext, toyObservationInterpretation, toyObservationPenguinBirdTable] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.ObservationSurfaceBridge.finiteExtensionalProb_inducedContext_eq_bp_ratio
      (S := toyObservationSurface)
      (G := gate)
      (σ := toyObservationData)
      (feature := Concept.penguin)
      (witness := Concept.bird)

theorem toyObservation_birdFly_score_eq_generated_ve_query_score :
    letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
      Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
    Interpretation.finitePointwiseLogRatioBits
        toyObservationInterpretation
        Concept.bird
        Concept.fly =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            toyObservationBirdFlyTable
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            toyObservationBirdFlyTable
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              toyObservationBirdFlyTable
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
            toyObservationBirdFlyTable
            [⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight toyObservationBirdFlyTable []) := by
  letI : Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType (Multiset ToyMembershipObservation) :=
    Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType ToyMembershipObservation
  simpa [toyObservationContext, toyObservationInterpretation, toyObservationBirdFlyTable] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.ObservationSurfaceBridge.finitePointwiseLogRatioBits_inducedContext_eq_ve_query_score
      (S := toyObservationSurface)
      (G := gate)
      (σ := toyObservationData)
      (feature := Concept.bird)
      (witness := Concept.fly)

noncomputable def toyThreeByTwoCountTable :
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable (Fin 3) (Fin 2) where
  count
    | 0, 0 => 2
    | 0, 1 => 1
    | 1, 0 => 5
    | 1, 1 => 0
    | 2, 0 => 1
    | 2, 1 => 4
  total_pos := by decide

def toyThreeByTwoFeature2 : Fin 3 := ⟨2, by decide⟩

def toyThreeByTwoWitness0 : Fin 2 := ⟨0, by decide⟩

def toyThreeByTwoWitness1 : Fin 2 := ⟨1, by decide⟩

theorem toyThreeByTwo_witness0_prior_eq_generated_ve_ratio :
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.witnessPrior
        toyThreeByTwoCountTable
        toyThreeByTwoWitness0 =
      (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.veWeight
        toyThreeByTwoCountTable
        [⟨MembershipConcept.witness, toyThreeByTwoWitness0⟩] : ℝ) /
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.veWeight
          toyThreeByTwoCountTable [] := by
  simpa [toyThreeByTwoWitness0] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.witnessPrior_eq_veWeight_ratio
      toyThreeByTwoCountTable toyThreeByTwoWitness0

theorem toyThreeByTwo_feature2_witness1_strength_eq_generated_bp_ratio :
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.witnessGivenFeatureStrength
        toyThreeByTwoCountTable
        toyThreeByTwoFeature2
        toyThreeByTwoWitness1 =
      if Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.featureMessage
          toyThreeByTwoCountTable
          toyThreeByTwoFeature2 = 0 then
        0
      else
        (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.jointFactorBelief
          toyThreeByTwoCountTable
          (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.jointAssign
            toyThreeByTwoCountTable
            toyThreeByTwoFeature2
            toyThreeByTwoWitness1) : ℝ) /
          Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.featureMessage
            toyThreeByTwoCountTable
            toyThreeByTwoFeature2 := by
  simpa [toyThreeByTwoFeature2, toyThreeByTwoWitness1] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.witnessGivenFeatureStrength_eq_bp_ratio
      toyThreeByTwoCountTable
      toyThreeByTwoFeature2
      toyThreeByTwoWitness1

theorem toyThreeByTwo_feature2_witness1_score_eq_generated_ve_query_score :
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.logRatioBits
        toyThreeByTwoCountTable
        toyThreeByTwoFeature2
        toyThreeByTwoWitness1 =
      logRatioInformationGainFromEvidence
        (if Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.veWeight
            toyThreeByTwoCountTable
            [⟨MembershipConcept.feature, toyThreeByTwoFeature2⟩] = 0 then
          0
        else
          (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.veWeight
            toyThreeByTwoCountTable
            [⟨MembershipConcept.feature, toyThreeByTwoFeature2⟩,
              ⟨MembershipConcept.witness, toyThreeByTwoWitness1⟩] : ℝ) /
            Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.veWeight
              toyThreeByTwoCountTable
              [⟨MembershipConcept.feature, toyThreeByTwoFeature2⟩])
        ((Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.veWeight
            toyThreeByTwoCountTable
            [⟨MembershipConcept.witness, toyThreeByTwoWitness1⟩] : ℝ) /
          Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.veWeight
            toyThreeByTwoCountTable []) := by
  simpa [toyThreeByTwoFeature2, toyThreeByTwoWitness1] using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteFeatureWitnessCountTable.logRatioBits_eq_ve_query_score
      toyThreeByTwoCountTable
      toyThreeByTwoFeature2
      toyThreeByTwoWitness1

theorem formedConcept_prior_tv_strength_eq_generated_ve_ratio
    {Obj Attr Q : Type*}
    [Preorder Q] [Fintype Obj] [Nonempty Obj] [Fintype Attr]
    (G : Mettapedia.KR.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept G M) :
    (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.conceptPriorTV
        (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation G M)
        witness).strength =
      (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteWitnessFeatureTable.veWeight
        (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation G M)
          feature witness)
        [⟨Mettapedia.KR.ConceptGeometry.IntensionalInheritance.MembershipConcept.witness, true⟩] : ℝ) /
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.FiniteWitnessFeatureTable.veWeight
          (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.KR.ConceptGeometry.AbstractInheritance.formedConceptInterpretation G M)
            feature witness) [] := by
  simpa using
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.AbstractInheritance.finitePriorProb_formedConceptInterpretation_eq_veWeight_ratio
      G M feature witness

theorem formedConcept_formConjoint_universal
    {Obj Attr Q : Type*}
    [Preorder Q] [Fintype Obj] [Fintype Attr]
    (G : Mettapedia.KR.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    {A B C : Mettapedia.KR.ConceptGeometry.AbstractInheritance.FormedConcept G M}
    (hCA : Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.Inherits C.1 A.1)
    (hCB : Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.Inherits C.1 B.1) :
    Mettapedia.KR.ConceptGeometry.AbstractInheritance.DualConcept.Inherits C.1
      (Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.formConjointConcept A.1 B.1) := by
  exact
    Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.formConjointConcept_universal
      hCA hCB

end Mettapedia.KR.ConceptGeometry.Examples.IntensionalInheritanceAllCanary
