import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.ConfidenceCharacterization
import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.DefinableCuts
import Mettapedia.PLN.Bridges.KR.ConceptFormationControlCanary
import Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge
import Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge
import Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionBayesianGrounding
import Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionCredalEnvelope
import Mettapedia.PLN.Bridges.Languages.PLNContextGuardOSLFDescentBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevisionProfile
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInductionAbductionProfile
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNContextGuardBridge

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


/-! ## Whole truth-theory package -/

/-- Top-level package for the current confidence / strength / ITV theory
profile.  The fields are theorem-profile values, so importing this package
gives a compact proof-carrying index of the current formal story. -/
structure TruthTheoryPackage where
  confidenceCharacterizationEndpoint : ConfidenceCharacterizationEndpointProfile
  confidenceFormulaAudit : ConfidenceFormulaAuditProfile
  confidenceChartTorsor : ConfidenceChartTorsorProfile
  confidenceRevisionCharts : ConfidenceRevisionChartProfile
  genericITV : GenericITVProfile
  bayesCredible : BayesCredibleProfile
  walleyBinary : WalleyBinaryProfile
  walleyCategorical : WalleyCategoricalProfile
  strengthProjection : StrengthProjectionProfile
  subjectiveLogicEvidenceBeta : SubjectiveLogicEvidenceBetaProfile
  revisionRuleFamily :
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.RevisionRuleFamilyProfile
  revisionBayesianGrounding :
    Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionBayesianGrounding.RevisionBayesianGroundingProfile
  revisionCredalEnvelope :
    Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionCredalEnvelope.RevisionCredalEnvelopeProfile
  inductionAbductionRuleFamily :
    Mettapedia.PLN.RuleFamilies.FirstOrder.InductionAbductionRuleFamilyProfile
  assocPatChapter12Consumer : AssocPatChapter12ConsumerProfile
  meanConcentration : MeanConcentrationProfile
  informationGeometry : InformationGeometryLiftProfile
  amplitudePhase : AmplitudePhasePLNProfile
  sufficientStatisticQueries : SufficientStatisticQueryProfile
  typedITVOperations : TypedITVOperationProfile
  worldModelTypedITVs : WorldModelTypedITVProfile
  credalForcedQueries : CredalForcedQueryProfile
  credalProjectionTower : CredalProjectionTowerProfile
  naturalExtension : NaturalExtensionProfile
  definableCutTightness : DefinableCutTightnessProfile.{0, 0}
  conceptFormationITVBridge :
    Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge.ConceptFormationITVBridgeProfile
  conceptFormationControlCanary :
    Mettapedia.PLN.Bridges.KR.ConceptFormationControlCanary.ConceptFormationControlCanaryProfile.{0}
  conceptFormationDeFinettiPrefixBridge :
    Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge.ConceptFormationDeFinettiPrefixBridgeProfile
  contextGuardBridge :
    Mettapedia.PLN.RuleFamilies.HigherOrder.PLNContextGuardBridge.ContextGuardBridgeProfile.{0, 0, 0, 0, 0, 0, 0}
  contextGuardOSLFDescentBridge :
    Mettapedia.PLN.Bridges.Languages.PLNContextGuardOSLFDescentBridge.ContextGuardOSLFDescentBridgeProfile
  projectiveCredal : Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.ProjectiveCredalProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  infiniteMLNCredalBridge : Mettapedia.Logic.MarkovLogicInfiniteCredalBridge.InfiniteMLNCredalBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  dlrQueryOutcomePLNBridge : Mettapedia.Logic.MarkovLogicPLNTruthBridge.DLRQueryOutcomePLNBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  projectiveDeFinettiCredalBridge : Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.ProjectiveDeFinettiCredalBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  coreFourCompletion : CoreFourCompletionProfile
  crispnessCollapse : CrispnessCollapseProfile
  degreesOfFreedomForcing : DegreesOfFreedomForcingProfile
  formulaCharacterization : FormulaCharacterizationProfile
  paperFacingSynthesis : PaperFacingDOFForcingSynthesisProfile
  didacticWitnesses : Mettapedia.PLN.TruthValues.PLNDidacticWitnesses.DidacticWitnessProfile
  runtimeParity : RuntimeParityManifest

/-- The current proof-carrying package for the confidence / strength / ITV
theory profile. -/
noncomputable def plnTruthTheoryPackage : TruthTheoryPackage where
  confidenceCharacterizationEndpoint :=
    confidenceCharacterizationEndpointProfile
  confidenceFormulaAudit := confidenceFormulaAuditProfile
  confidenceChartTorsor := confidenceChartTorsorProfile
  confidenceRevisionCharts := confidenceRevisionChartProfile
  genericITV := genericITVProfile
  bayesCredible := bayesCredibleProfile
  walleyBinary := walleyBinaryProfile
  walleyCategorical := walleyCategoricalProfile
  strengthProjection := strengthProjectionProfile
  subjectiveLogicEvidenceBeta := subjectiveLogicEvidenceBetaProfile
  revisionRuleFamily :=
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionRuleFamilyProfile
  revisionBayesianGrounding :=
    Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionBayesianGrounding.revisionBayesianGroundingProfile
  revisionCredalEnvelope :=
    Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionCredalEnvelope.revisionCredalEnvelopeProfile
  inductionAbductionRuleFamily :=
    Mettapedia.PLN.RuleFamilies.FirstOrder.inductionAbductionRuleFamilyProfile
  assocPatChapter12Consumer := assocPatChapter12ConsumerProfile
  meanConcentration := meanConcentrationProfile
  informationGeometry := informationGeometryLiftProfile
  amplitudePhase := amplitudePhasePLNProfile
  sufficientStatisticQueries := sufficientStatisticQueryProfile
  typedITVOperations := typedITVOperationProfile
  worldModelTypedITVs := worldModelTypedITVProfile
  credalForcedQueries := credalForcedQueryProfile
  credalProjectionTower := credalProjectionTowerProfile
  naturalExtension := naturalExtensionProfile
  definableCutTightness := definableCutTightnessProfile
  conceptFormationITVBridge :=
    Mettapedia.PLN.Bridges.KR.ConceptFormationITVBridge.conceptFormationITVBridgeProfile
  conceptFormationControlCanary :=
    Mettapedia.PLN.Bridges.KR.ConceptFormationControlCanary.conceptFormationControlCanaryProfile
  conceptFormationDeFinettiPrefixBridge :=
    Mettapedia.PLN.Bridges.KR.ConceptFormationDeFinettiBridge.conceptFormationDeFinettiPrefixBridgeProfile
  contextGuardBridge :=
    Mettapedia.PLN.RuleFamilies.HigherOrder.PLNContextGuardBridge.contextGuardBridgeProfile
  contextGuardOSLFDescentBridge :=
    Mettapedia.PLN.Bridges.Languages.PLNContextGuardOSLFDescentBridge.contextGuardOSLFDescentBridgeProfile
  projectiveCredal :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.projectiveCredalProfile
  infiniteMLNCredalBridge :=
    Mettapedia.Logic.MarkovLogicInfiniteCredalBridge.infiniteMLNCredalBridgeProfile
  dlrQueryOutcomePLNBridge :=
    Mettapedia.Logic.MarkovLogicPLNTruthBridge.dlrQueryOutcomePLNBridgeProfile
  projectiveDeFinettiCredalBridge :=
    Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge.projectiveDeFinettiCredalBridgeProfile
  coreFourCompletion := coreFourCompletionProfile
  crispnessCollapse := crispnessCollapseProfile
  degreesOfFreedomForcing := degreesOfFreedomForcingProfile
  formulaCharacterization := formulaCharacterizationProfile
  paperFacingSynthesis := paperFacingDOFForcingSynthesisProfile
  didacticWitnesses := Mettapedia.PLN.TruthValues.PLNDidacticWitnesses.didacticWitnessProfile
  runtimeParity := plnITVIDMRuntimeParityManifest


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
