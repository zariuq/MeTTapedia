import Mettapedia.Logic.HOL.TH0ComputationalTrinity
import Mettapedia.PLN.Bridges.GSLT.ProbabilityWorldModelDischarge
import Mettapedia.PLN.WorldModel.WMCalculusForgetBoundary
import Mettapedia.TypeTheory.LocallyThinOpenEndedProofRelevantProfile
import Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentChoiceMatrix
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalTransportDiscriminator

/-!
# The currently proved Prime metatheory choice braid

This module is a theorem-level integration boundary for the current Prime
design exploration.  It does not select an object-language identity theory,
a higher-order search calculus, a probability model, a forgetting operation,
or a globally truncated mode theory.  Instead, it bundles the results that
constrain any later selection:

* dependent O/I/E modalities have three positive right-adjoint orientations
  and three explicit reverse/image obstructions;
* locally thin mode comparisons coexist with raw comparison history,
  proof-relevant TH0 execution, and an open observation tail;
* mode-comparison thinness is independent of identity-route UIP and endpoint
  reflection;
* rho and graph context cells can have dependent consumers even when the
  selected semantic mode cells do not;
* named TH0 elaboration, dialect-independent meaning, operational
  realization, and exact native-checker refinement share one typed waist;
* higher-order algorithms share that waist but have incomparable additional
  requirements;
* finite search is a sound accelerator while a genuinely infinitary rule may
  remain absent from every finite stage;
* source non-reuse is not stochastic independence;
* the present WM calculus laws do not determine forgetting; and
* canonical-example agreement is weaker than an all-input native refinement.

`CurrentBoundary` contains proofs of those claims rather than status flags.
It is therefore an importable constraint on future profiles, not a declaration
that the remaining choices have already been made.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PrimeMetatheoryChoiceBraid

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition
open Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.HigherOrderAlgorithmProfiles
open Mettapedia.Logic.HOL.TH0ComputationalTrinity
open Mettapedia.Logic.HOL.TH0SyntacticUnifierService
open Mettapedia.Logic.OpenEndedReasoningEnvelope
open Mettapedia.TypeTheory.CwfDependentRightAdjoint
open Mettapedia.TypeTheory.DiscreteOnDependentRightAdjoint
open Mettapedia.TypeTheory.EvidenceCompletionDependentRightAdjoint
open Mettapedia.TypeTheory.OperationalFamilyCwf
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentFactorization
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.RouteFamilyCwf
open Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint

/-! ## Named propositions at the integration waist -/

def LocalModeOpenEvidenceBoundary : Prop :=
  Mettapedia.TypeTheory.LocallyThinOpenEndedProofRelevantProfile.oieOpenTH0.ComparisonThin ∧
    Mettapedia.TypeTheory.LocallyThinOpenEndedProofRelevantProfile.oieOpenTH0.OpenTail ∧
    Mettapedia.TypeTheory.LocallyThinOpenEndedProofRelevantProfile.oieOpenTH0.Reachable ∧
    Mettapedia.TypeTheory.LocallyThinOpenEndedProofRelevantProfile.oieOpenTH0.EvidenceRich

def ModeIdentityIndependenceBoundary : Prop :=
  (¬ ∀ profile :
      Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality.Profile.{0, 0, 0},
      profile.ModeThin → profile.IdentityUIP) ∧
  (¬ ∀ profile :
      Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality.Profile.{0, 0, 0},
      profile.IdentityUIP → profile.ModeThin) ∧
  (¬ ∀ profile :
      Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality.Profile.{0, 0, 0},
      profile.ModeThin → profile.ReflectsEndpoints) ∧
  (¬ ∀ profile :
      Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality.Profile.{0, 0, 0},
      profile.ReflectsEndpoints → profile.ModeThin)

def DependentModeBoundary : Prop :=
  Nonempty (DependentRightAdjoint dynCwf.{0} routeCwf.{0}) ∧
    Nonempty (DependentRightAdjoint routeCwf.{0} extCwf.{0}) ∧
    Nonempty (DependentRightAdjoint extCwf.{0} routeCwf.{0}) ∧
    (∃ (context : RouteType.{0})
        (family : DynFamily (forgetReflexivity.obj context)),
      ¬ Nonempty (UnchangedRouteLift family)) ∧
    (∃ (context : RouteType.{0}) (family : context.carrier → Type),
      ¬ Nonempty (RouteAction context family)) ∧
    (∃ (context : RouteType.{0}) (family : RouteFamily context),
      ¬ InRightImageUpToFibreEquivalence context family) ∧
    (∀ context : DynSys.{0},
      Nonempty
        (routeQuotient.obj (evidenceCompletion.obj context) ≅
          dynQuotient.obj context))

def ContextCellDiscriminatorBoundary : Prop :=
  Mettapedia.TypeTheory.OperationalIntensionalExtensionalTwoComputad.factorRoundTrip ≠
      Mettapedia.TypeTheory.OperationalIntensionalExtensionalCellThinness.factorIdentityCell ∧
    ¬ Mettapedia.TypeTheory.RouteTransportDiscriminator.HasWhiskeredFamilyDiscriminator
      (Mettapedia.TypeTheory.OperationalIntensionalExtensionalTwoComputad.interpretCell.{0}
        Mettapedia.TypeTheory.OperationalIntensionalExtensionalTwoComputad.factorRoundTrip).toNatTrans
      (Mettapedia.TypeTheory.OperationalIntensionalExtensionalTwoComputad.interpretCell.{0}
        Mettapedia.TypeTheory.OperationalIntensionalExtensionalCellThinness.factorIdentityCell).toNatTrans ∧
    Mettapedia.TypeTheory.RouteTransportDiscriminator.HasDependentFamilyDiscriminator
      Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentCellBoundary.rhoZeroPointCell
      Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentCellBoundary.rhoOnePointCell ∧
    Mettapedia.TypeTheory.RouteTransportDiscriminator.HasDependentFamilyDiscriminator
      Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentCellBoundary.graphDirectPointCell
      Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentCellBoundary.graphDetourPointCell

def TH0VerticalBoundary : Prop :=
  ∃ formula : ClosedFormula Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary.Constant,
    (Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary.uniformDialectAdapters .he).decode
        Mettapedia.TypeTheory.TH0NamedElaborationBridge.Canary.identityPacket =
      some formula ∧
    (Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary.uniformDialectAdapters .petta).decode
        Mettapedia.TypeTheory.TH0NamedElaborationBridge.Canary.identityPacket =
      some formula ∧
    Nonempty
      (OperationalRealization
        (reflexiveProblemOf
          Mettapedia.TypeTheory.TH0NamedElaborationBridge.Canary.identityPacket))

def HigherOrderAlgorithmBoundary : Prop :=
  (∀ role : ReasoningRole,
    portableTH0Guarantees ⊆ requirements role ∧
      .independentReplay ∈ requirements role) ∧
  Incomparable (requirements .uniformProofSearch)
    (requirements .lambdaSuperposition) ∧
  Incomparable (requirements .proofPlanning)
    (requirements .lambdaSuperposition) ∧
  Incomparable (requirements .higherOrderInductiveLearning)
    (requirements .finiteModelFinding) ∧
  Incomparable (requirements .infinitaryProofSearch)
    (requirements .lambdaSuperposition)

def FiniteAndInfinitaryBoundary : Prop :=
  (¬ Nonempty
      (TH0SyntacticUnifierService.Canary.producer.EvidenceFor
        TH0SyntacticUnifierService.Canary.baseProblem 0) ∧
    Nonempty
      (OperationalRealization
        TH0SyntacticUnifierService.Canary.baseProblem)) ∧
  ((indexedDerivationAuthority
      (Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary.UnionIndexedRules
        Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary.OmegaCanary.StageRules)).Meaning
      none ∧
    ∀ stage,
      ¬ Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary.IndexedDerives
        (Mettapedia.TypeTheory.InfinitaryProofAndObservationBoundary.OmegaCanary.StageRules
          stage)
        none)

def ProvenanceProbabilityBoundary : Prop :=
  ¬ (Mettapedia.Evidence.SourceScoped.Independent
        Mettapedia.Evidence.SourceScopeProbabilityBoundary.correlatedLeft
        Mettapedia.Evidence.SourceScopeProbabilityBoundary.correlatedRight →
      _root_.ProbabilityTheory.IndepSet
        Mettapedia.Evidence.SourceScopeProbabilityBoundary.correlatedLeft.event
        Mettapedia.Evidence.SourceScopeProbabilityBoundary.correlatedRight.event
        Mettapedia.Evidence.SourceScopeProbabilityBoundary.fairWorldMeasure)

def WorldModelForgettingBoundary : Prop :=
  ∃ first second :
      Mettapedia.PLN.WorldModel.WMCalculusSoundness.WMCalculus Nat Unit Nat,
    (∀ left right, first.revise left right = left + right) ∧
    (∀ state query, first.extract state query = state) ∧
    (∀ left right, first.revise left right = second.revise left right) ∧
    (∀ state query, first.extract state query = second.extract state query) ∧
    first.forget ≠ second.forget

def NativeAllInputBoundary : Prop :=
  Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition.Canary.cReference.check
      (some (some true)) (some (some ())) = true ∧
    Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition.Canary.cReference.check
      none (some (some ())) = false ∧
    ¬ DirectNativeCheckerPipeline
      Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement.Canary.source
      Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement.Canary.claimCodec
      Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement.Canary.certificateCodec
      Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement.Canary.referenceChecker
      Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition.Canary.outerClaimCodec
      Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition.Canary.outerCertificateCodec
      Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition.Canary.canonicalOnlyC

/-! ## The certified bundle -/

structure CurrentBoundary : Prop where
  localModeOpenEvidence : LocalModeOpenEvidenceBoundary
  modeIdentityIndependent : ModeIdentityIndependenceBoundary
  dependentModes : DependentModeBoundary
  contextCellDiscriminators : ContextCellDiscriminatorBoundary
  th0Vertical : TH0VerticalBoundary
  higherOrderAlgorithms : HigherOrderAlgorithmBoundary
  finiteAndInfinitary : FiniteAndInfinitaryBoundary
  provenanceNotProbability : ProvenanceProbabilityBoundary
  worldModelForgettingOpen : WorldModelForgettingBoundary
  nativeAllInput : NativeAllInputBoundary

/-- The live theorem collection inhabits the integrated boundary without
selecting any of its deliberately open branches. -/
theorem currentBoundary : CurrentBoundary := by
  refine
    { localModeOpenEvidence :=
        Mettapedia.TypeTheory.LocallyThinOpenEndedProofRelevantProfile.oieOpenTH0_has_all_three_axes
      modeIdentityIndependent := ?_
      dependentModes :=
        Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentChoiceMatrix.dependent_modality_choice_matrix
      contextCellDiscriminators := ?_
      th0Vertical := TH0ComputationalTrinity.Canary.named_identity_traverses_the_trinity
      higherOrderAlgorithms := ?_
      finiteAndInfinitary := ?_
      provenanceNotProbability :=
        Mettapedia.PLN.Bridges.GSLT.ProbabilityAssumptionDischarge.sourceNonreuse_cannot_discharge_eventIndependence
      worldModelForgettingOpen :=
        ?_
      nativeAllInput := ?_ }
  · exact
      ⟨Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality.modeThin_does_not_imply_identityUIP,
        Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality.identityUIP_does_not_imply_modeThin,
        Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality.modeThin_does_not_imply_endpointReflection,
        Mettapedia.TypeTheory.ModeComparisonIdentityOrthogonality.endpointReflection_does_not_imply_modeThin⟩
  · exact
      ⟨Mettapedia.TypeTheory.OperationalIntensionalExtensionalTransportDiscriminator.raw_factor_history_distinct_without_semantic_discriminator.{0}.1,
        Mettapedia.TypeTheory.OperationalIntensionalExtensionalTransportDiscriminator.raw_factor_history_distinct_without_semantic_discriminator.{0}.2,
        Mettapedia.TypeTheory.OperationalIntensionalExtensionalTransportDiscriminator.rho_revision_has_dependent_discriminator,
        Mettapedia.TypeTheory.OperationalIntensionalExtensionalTransportDiscriminator.graph_work_has_dependent_discriminator⟩
  · refine ⟨?_,
      uniform_proofs_and_lambda_superposition_are_incomparable,
      proof_planning_and_lambda_superposition_are_incomparable,
      learning_and_model_finding_are_incomparable,
      infinitary_and_finitary_superposition_are_incomparable⟩
    intro role
    exact ⟨every_role_consumes_the_portable_core role,
      every_role_requires_independent_replay role⟩
  · exact
      ⟨TH0ComputationalTrinity.Canary.finite_miss_then_operational_success,
        InfinitaryCanary.limit_meaning_without_finite_stage⟩
  · exact
      ⟨Mettapedia.PLN.WorldModel.WMCalculusForgetBoundary.withoutForget,
        Mettapedia.PLN.WorldModel.WMCalculusForgetBoundary.withArbitraryForget,
        by intro left right; rfl,
        by intro state query; rfl,
        Mettapedia.PLN.WorldModel.WMCalculusForgetBoundary.same_revision_and_extraction.1,
        Mettapedia.PLN.WorldModel.WMCalculusForgetBoundary.same_revision_and_extraction.2,
        Mettapedia.PLN.WorldModel.WMCalculusForgetBoundary.forgetting_differs⟩
  · exact
      ⟨Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition.Canary.canonical_true_accepts,
        Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition.Canary.malformed_outer_claim_rejected,
        Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition.Canary.canonicalOnlyC_not_direct⟩

/-! ## Audited theorem crown -/

#print axioms currentBoundary

end Mettapedia.TypeTheory.PrimeMetatheoryChoiceBraid
