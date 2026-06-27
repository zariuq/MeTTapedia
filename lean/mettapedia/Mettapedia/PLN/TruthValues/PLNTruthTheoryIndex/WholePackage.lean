import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.ConfidenceCharacterization

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
surface.  The fields are theorem-profile values, so importing this package
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
  runtimeParity : RuntimeParitySurface

/-- The current proof-carrying package for the confidence / strength / ITV
theory surface. -/
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
  runtimeParity := plnITVIDMRuntimeParitySurface


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
