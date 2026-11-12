#!/usr/bin/env python3
"""Check the declared specification boundary against the source import graph.

This checks dependency direction and entry-point coverage, not theorem truth,
semantic necessity, or native runtime conformance. Paths are relative to the
Lean project, so the gate can run in another checkout without configuration.
"""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
CANDIDATE = "Mettapedia.Languages.MeTTa.PrimeCandidates"
CURRENT = "Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent"
COMPARISONS = "Mettapedia.Languages.MeTTa.PrimeComparisons"
# Foreign implementations are clients of SemanticService, not Prime foundation dependencies.
# Reusable HOL/set mathematics belongs under Logic or TypeTheory. Integration
# with a named prover belongs in PrimeComparisons, even when it shares Data.
FOREIGN_FOUNDATIONS = (
    "Mettapedia.Languages.Megalodon",
    "Mettapedia.Languages.Egal",
    "Mettapedia.Languages.Dedukti",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG",
    "Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonHOTG",
)
CORE_ROOTS = (
    "Mettapedia.TypeTheory.NamedValueContexts",
    "Mettapedia.TypeTheory.NamedContextDataflow",
    "Mettapedia.TypeTheory.ContextualEvaluationReferences",
    "Mettapedia.TypeTheory.ContextualBindingConflict",
    "Mettapedia.TypeTheory.GroundBindingCategory",
    "Mettapedia.GSLT.LanguageDef.EmptyDemandCoherence",
    "Mettapedia.Languages.FiniteChoice.EmptinessTaxonomy",
    "Mettapedia.Languages.FiniteChoice.CollapseSuperposeRoundTrip",
    "Mettapedia.TypeTheory.MonoidIndexedTransportCoherence",
    "Mettapedia.TypeTheory.RetainedPresentationViews",
    "Mettapedia.TypeTheory.InductionRecursionBoundary",
    "Mettapedia.TypeTheory.CwfTarskiUniverse",
    "Mettapedia.TypeTheory.TarskiUniverseEmbedding",
    "Mettapedia.TypeTheory.FamilyEnclosingUniverseTower",
    "Mettapedia.TypeTheory.TarskiDecodedFamilyCoherence",
    "Mettapedia.TypeTheory.TarskiClosureRankObstruction",
    "Mettapedia.TypeTheory.TarskiCumulativeCodeCoherenceBoundary",
    "Mettapedia.TypeTheory.ContextualIdentitySubstitution",
    "Mettapedia.TypeTheory.ContextualTypeOperations",
    "Mettapedia.TypeTheory.ContextualBasedIdentityOperations",
    "Mettapedia.TypeTheory.ContextualBasedIdentityScope",
    "Mettapedia.TypeTheory.ContextualRetainedIdentityOperations",
    "Mettapedia.TypeTheory.AuthorityOutcomeViews",
    "Mettapedia.TypeTheory.IndexedPolynomialListRelSmall",
    "Mettapedia.TypeTheory.HenkinLogicalCodeDescent",
    "Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyInterpretation",
    "Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyCoherence",
    "Mettapedia.Logic.HOL.Embedding.UniformListPredicateFamily",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation",
    "Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure",
    "Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofFamily",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofConversion",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNaturalDeductionNativeTranslation",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizProofComparison",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofSourceSubstitution",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizZFSetInterpretation",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofConfluence",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizInterface",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizRules",
    "Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts",
    "Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizDerived",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeProofTranslation",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizMapFusionNative",
    "Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetContextualUniverseInterpretation",
    "Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetLiftedCarrierInterpretation",
    "Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveInterpretationComposition",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTypeInterpretation",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTermInterpretation",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLContextualInterpretation",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofDecoderBoundary",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLWeakProofDecoding",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLContextualProofConsumption",
    "Mettapedia.Logic.HOL.Embedding.ZFSetIndexedClosure",
    "Mettapedia.Logic.HOL.Embedding.ZFSetList",
    "Mettapedia.Logic.HOL.Embedding.ZFSetListContextual",
    "Mettapedia.Logic.HOL.Embedding.ZFSetListClosure",
    "Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts",
    "Mettapedia.Logic.HOL.Embedding.ZFSetTraceContextual",
    "Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTypeInterpretation",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTermInterpretation",
    "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceProofDecoding",
    "Mettapedia.Logic.HOL.Embedding.ZFSetTraceListContextual",
    "Mettapedia.Logic.HOL.Embedding.ZFSetUniformListModel",
    "Mettapedia.Logic.HOL.Embedding.ZFSetUniformListProofConsumption",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation",
    "Mettapedia.OSLF.MeTTaIL.ContextualStepFuel",
    "Mettapedia.OSLF.MeTTaIL.ContextualStepClosedSubsystem",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMapComputation",
    "Mettapedia.GSLT.LanguageDef.PresentationEvidence",
    "Mettapedia.GSLT.Dynamics.ServiceEffectProtocol",
    "Mettapedia.GSLT.Dynamics.ServiceResumption",
    "Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation",
    "Mettapedia.GSLT.LanguageDef.SemanticServiceResumption",
    "Mettapedia.GSLT.LanguageDef.EvidenceConditionedBranching",
    "Mettapedia.GSLT.LanguageDef.OutcomeViewControls",
    "Mettapedia.GSLT.LanguageDef.FiniteSetRepresentationService",
    "Mettapedia.GSLT.LanguageDef.PolicyFamilyAdmission",
    "Mettapedia.GSLT.LanguageDef.EquationPremiseStability",
    "Mettapedia.GSLT.LanguageDef.ContextualEffectTreeLanguage",
    "Mettapedia.GSLT.LanguageDef.ContextualEffectTreeExactness",
    "Mettapedia.GSLT.LanguageDef.DialectGluing",
    "Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms",
    "Mettapedia.GSLT.Core.PolicyFamilyOperationClosure",
    "Mettapedia.GSLT.Core.PolicyFamilyDependentDescent",
    "Mettapedia.GSLT.Core.PolicyFamilyContextClosure",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.SyntacticPolicyDependentDescent",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLUniformList",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.OpaqueRelatorExtension",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveCompletedRelatorPreservation",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveBasedIdentity",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualComparison",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualQuotient",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientCwf",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientComprehensionSyntax",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientInterpretation",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientDeclarations",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation",
    "Mettapedia.TypeTheory.JointObservationDependentDescent",
    "Mettapedia.Logic.HOL.UniformListInduction",
    "Mettapedia.Logic.HOL.UniformListMapFusion",
    "Mettapedia.Logic.HOL.ProofSyntax",
    "Mettapedia.Logic.HOL.ProofSyntaxStructural",
    "Mettapedia.Logic.HOL.Embedding.GroundUnaryEquationalProofSyntax",
    "Mettapedia.Logic.HOL.UniformListInductionChart",
    "Mettapedia.Logic.HOL.UniformListInductionRevisionViews",
    "Mettapedia.Languages.MeTTa.Experimental.StagedReflective.Presentation",
    "Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow",
    "Mettapedia.GSLT.Dynamics.RevisionedOccurrenceReturnedFibre",
    "Mettapedia.GSLT.Dynamics.RevisionedOccurrenceExactImage",
    "Mettapedia.GSLT.ReproducibleBuild.GSLTIL",
    "Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection",
    "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.ReductionActivationOrthogonality",
    "Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler",
    "Mettapedia.PLN.Bridges.GSLT",
    "Mettapedia.OSLF.Framework.ReductionViewIndexedModalities",
)


CORE_ROOTS += (
    "Mettapedia.GSLT.LanguageDef.GSLTILNativeKernel",
    "Mettapedia.GSLT.LanguageDef.ScopedBindingCaptureSupport",
    "Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission",
    "Mettapedia.Machines.DemandBoundary",
    "Mettapedia.GSLT.LanguageDef.AuthorityLedger",
    "Mettapedia.GSLT.LanguageDef.BootstrapCell.CheckingWeakness",
    "Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCorrect",
    "Mettapedia.GSLT.LanguageDef.BootstrapCell.ReflexiveLayer",
    "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodecMatching",
)

# Candidate integration evidence is inventoried separately from reusable
# foundations; it must remain independent of the current-runtime branch.
CANDIDATE_EVIDENCE_ROOTS = (
    "Mettapedia.Languages.MeTTa.PrimeCandidates.Index.Requirements",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.Strategies.QuotationDemand",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveNativeHOLMapExecution",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLProofListIntegration",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLLeibnizDenotation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizRepresentationSemantics",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizNativeProofAdequacy",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedListElimination",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedHOLProofRules",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedPreservation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedComputationControls",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedLeibnizRules",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListConstantBodies",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListLength",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListDeclarationInterpretation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListInduction",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListEquationInputs",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListProofInputs",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListProofConsumption",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecution",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecutionBeta",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedOperationalDecomposition",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataRoots",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataCompleteness",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeListHOLPredicateObservation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationSpecification",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationObservation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationEffectTree",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireRelatorCompatibility",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveCompletedConversion",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientUniverses",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProducts",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientUniverseProducts",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProductRepresentation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProductTermRepresentation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentity",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientBasedContextRepresentation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityGeometry",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientBasedJRepresentation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityInputCoherence",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityReindexing",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityNativeReindexing",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientRetainedIdentity",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientRetainedIdentityInterface",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveContextSourceObstruction",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeIdentityLevelInstantiation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireRelatorPreservation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.MatchedIndexDependentTransport",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationContextViews",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListChartService",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListChartProofSyntax",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLFragmentDenotation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeUniverseModelBoundary",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeCumulativeFormationCoherenceBoundary",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeMatchedTransportDenotation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireDataDenotation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListCognitiveWorkload",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.OpaqueRelatorScopedComputation",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SpaceOperationalViewBoundary",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SpaceActivationPolicyBoundary",
    "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.LanguageDefDerivedActivationBoundary",
)
EVIDENCE_ROOTS = CORE_ROOTS + CANDIDATE_EVIDENCE_ROOTS
GATE_ROOTS = {
    "isolation.requirement-interface": (
        "Mettapedia.TypeTheory.NamedValueContexts",
        "Mettapedia.TypeTheory.NamedContextDataflow",
        "Mettapedia.TypeTheory.ContextualEvaluationReferences",
        "Mettapedia.TypeTheory.ContextualBindingConflict",
        "Mettapedia.TypeTheory.GroundBindingCategory",
        "Mettapedia.GSLT.LanguageDef.EmptyDemandCoherence",
        "Mettapedia.Languages.FiniteChoice.EmptinessTaxonomy",
        "Mettapedia.Languages.FiniteChoice.CollapseSuperposeRoundTrip",
        "Mettapedia.TypeTheory.MonoidIndexedTransportCoherence",
        "Mettapedia.TypeTheory.RetainedPresentationViews",
        "Mettapedia.TypeTheory.InductionRecursionBoundary",
        "Mettapedia.TypeTheory.CwfTarskiUniverse",
        "Mettapedia.TypeTheory.TarskiUniverseEmbedding",
        "Mettapedia.TypeTheory.FamilyEnclosingUniverseTower",
        "Mettapedia.TypeTheory.TarskiDecodedFamilyCoherence",
        "Mettapedia.TypeTheory.TarskiClosureRankObstruction",
        "Mettapedia.TypeTheory.TarskiCumulativeCodeCoherenceBoundary",
        "Mettapedia.TypeTheory.ContextualIdentitySubstitution",
        "Mettapedia.TypeTheory.ContextualTypeOperations",
        "Mettapedia.TypeTheory.ContextualRetainedIdentityOperations",
        "Mettapedia.TypeTheory.AuthorityOutcomeViews",
        "Mettapedia.GSLT.LanguageDef.OutcomeViewControls",
        "Mettapedia.TypeTheory.IndexedPolynomialListRelSmall",
        "Mettapedia.TypeTheory.HenkinLogicalCodeDescent",
        "Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyInterpretation",
        "Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyCoherence",
        "Mettapedia.Logic.HOL.Embedding.UniformListPredicateFamily",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation",
        "Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure",
        "Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofFamily",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofConversion",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNaturalDeductionNativeTranslation",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizProofComparison",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveNativeHOLMapExecution",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofSourceSubstitution",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizZFSetInterpretation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLProofListIntegration",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofConfluence",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizInterface",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizRules",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLLeibnizDenotation",
        "Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts",
        "Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizDerived",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeProofTranslation",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizMapFusionNative",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizRepresentationSemantics",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizNativeProofAdequacy",
        "Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetContextualUniverseInterpretation",
        "Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetLiftedCarrierInterpretation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedListElimination",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedHOLProofRules",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedPreservation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedComputationControls",
        "Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedLeibnizRules",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListConstantBodies",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListLength",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListDeclarationInterpretation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListInduction",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListEquationInputs",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListProofInputs",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListProofConsumption",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveInterpretationComposition",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTypeInterpretation",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTermInterpretation",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLContextualInterpretation",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofDecoderBoundary",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLWeakProofDecoding",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLContextualProofConsumption",
        "Mettapedia.Logic.HOL.Embedding.ZFSetIndexedClosure",
        "Mettapedia.Logic.HOL.Embedding.ZFSetList",
        "Mettapedia.Logic.HOL.Embedding.ZFSetListContextual",
        "Mettapedia.Logic.HOL.Embedding.ZFSetListClosure",
        "Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts",
        "Mettapedia.Logic.HOL.Embedding.ZFSetTraceContextual",
        "Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTypeInterpretation",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTermInterpretation",
        "Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceProofDecoding",
        "Mettapedia.Logic.HOL.Embedding.ZFSetTraceListContextual",
        "Mettapedia.Logic.HOL.Embedding.ZFSetUniformListModel",
        "Mettapedia.Logic.HOL.Embedding.ZFSetUniformListProofConsumption",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation",
        "Mettapedia.OSLF.MeTTaIL.ContextualStepFuel",
        "Mettapedia.OSLF.MeTTaIL.ContextualStepClosedSubsystem",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecution",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecutionBeta",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedOperationalDecomposition",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodecMatching",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataRoots",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleDataCompleteness",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMapComputation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeListHOLPredicateObservation",
        "Mettapedia.GSLT.LanguageDef.PresentationEvidence",
        "Mettapedia.GSLT.Dynamics.ServiceEffectProtocol",
        "Mettapedia.GSLT.Dynamics.ServiceResumption",
        "Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation",
        "Mettapedia.GSLT.LanguageDef.SemanticServiceResumption",
        "Mettapedia.GSLT.LanguageDef.ContextualEffectTreeLanguage",
        "Mettapedia.GSLT.LanguageDef.ContextualEffectTreeExactness",
        "Mettapedia.GSLT.Core.PolicyFamilyOperationClosure",
        "Mettapedia.GSLT.Core.PolicyFamilyDependentDescent",
        "Mettapedia.GSLT.Core.PolicyFamilyContextClosure",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationSpecification",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationObservation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationEffectTree",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.SyntacticPolicyDependentDescent",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLUniformList",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireRelatorCompatibility",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.OpaqueRelatorExtension",
        "Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveCompletedRelatorPreservation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveCompletedConversion",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualComparison",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualQuotient",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientCwf",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientUniverses",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientComprehensionSyntax",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProducts",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientUniverseProducts",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProductRepresentation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProductTermRepresentation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentity",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientBasedContextRepresentation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityGeometry",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientBasedJRepresentation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityInputCoherence",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityReindexing",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityNativeReindexing",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientRetainedIdentity",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientRetainedIdentityInterface",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientInterpretation",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientDeclarations",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveContextSourceObstruction",
        "Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeIdentityLevelInstantiation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireRelatorPreservation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.MatchedIndexDependentTransport",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationContextViews",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListChartService",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLFragmentDenotation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeUniverseModelBoundary",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeCumulativeFormationCoherenceBoundary",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeMatchedTransportDenotation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireDataDenotation",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListCognitiveWorkload",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.OpaqueRelatorScopedComputation",
        "Mettapedia.TypeTheory.JointObservationDependentDescent",
        "Mettapedia.Logic.HOL.UniformListInduction",
        "Mettapedia.Logic.HOL.UniformListMapFusion",
        "Mettapedia.Logic.HOL.ProofSyntax",
        "Mettapedia.Logic.HOL.UniformListInductionChart",
        "Mettapedia.Logic.HOL.UniformListInductionRevisionViews",
    ),
    "isolation.staged-reflective": (
        "Mettapedia.Languages.MeTTa.Experimental.StagedReflective.Presentation",
        "Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow",
        "Mettapedia.GSLT.Dynamics.RevisionedOccurrenceReturnedFibre",
        "Mettapedia.GSLT.Dynamics.RevisionedOccurrenceExactImage",
        "Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT",
        "Mettapedia.GSLT.ReproducibleBuild.GSLTIL",
    ),
    "isolation.dialect-gluing": (
        "Mettapedia.GSLT.LanguageDef.DialectGluing",
        "Mettapedia.GSLT.LanguageDef.DialectGluingMorphisms",
    ),
}
# Reviewed applications have exact finite membership. New files are not admitted
# by a directory-prefix exception. Every other HostingStyles/Cost owner is
# checked below as independent source mathematics.
HOSTING_APPLICATION_PROFILES = {
    'AmbientRegions': {
        "reason": 'Named headed/ambient regions of the calibration host, with scope and hosting observers.',
        "modules": (
            'AllHeaded AllHeadedHosting AtomSubjects Containment HeadedContainment '
            'HeadedNested HeadedRoots HeadedScoped Hosting InRuns '
            'Inclusions Language Nested Rules RunTerms '
            'RunsOfAtoms Scoping Summary TwoSpaces WeakEvaluator '
            'WithoutRun '
        ).split(),
    },
    'AmbientSpace': {
        "reason": 'Space-host profiles and their chosen run or quotation interfaces.',
        "modules": (
            'Atoms BesideRun ChangedSpace Contexts Hosting '
            'Language RootSubject RulesFromSpace ShapedContexts Steps '
            'Sum Tokens '
        ).split(),
    },
    'AtomsReduce': {
        "reason": 'A selected atom-reduction language and its quotation/static-equivalence observer.',
        "modules": (
            'Contexts Defects Encoding FreeRightSide Hosting '
            'Language Matching Programs PureFragment Quotation '
            'Rules ScopedContexts Statics Steps Summary '
        ).split(),
    },
    'AuthoredEvaluators': {
        "reason": 'Evaluator programs compared on the calibration presentation and its chosen engine.',
        "modules": (
            'AuthoredEvaluator BetaProgram BetaSpec ClimbProgram EquationProofs '
            'EvaluatorTable MatchingProgram MatchingSpec ProgramSentence RunAnswers '
            'RunningChecker WeakEvaluators '
        ).split(),
    },
    'ContextReadings': {
        "reason": 'Linear, separate-sort and proof-data readings of the calibration presentation.',
        "modules": (
            'Conservation EquationShapes PresentedReadings ProbeReadings ProofSystemsAsData '
            'RawPatterns SeparateSort Summary '
        ).split(),
    },
    'Guests': {
        "reason": 'Explicit guest/checker experiments on the selected untyped hosting presentation.',
        "modules": (
            'AuthoredProofSystems CertificateChecker CheckerAgainstSpace CheckerContexts CheckerSimulation '
            'HostedRuns MM0Checker MM0Derivations MM0Table '
        ).split(),
    },
    'LocatedAtoms': {
        "reason": 'A selected located-atom language, evaluator and normal-form observer.',
        "modules": (
            'Compare Contexts Evaluator FreeRightSide Language '
            'Limits NormalForm Reading Spellings Steps '
            'Summary TwoSpaces '
        ).split(),
    },
    'NameEquality': {
        "reason": 'Selected name-equality service profiles and their operational/refusal observations.',
        "modules": (
            'AdmissionRunNames CheckNames CheckRunNames DataEquality Family '
            'FreshnessPremise KernelNames LibraryOver LocalTable NamesAsConstants '
            'Numbers OrderOfEquations Renaming RepeatedVariable RunningNames '
            'SequentialOver StoredNames Summary VerificationRefusalNames VerificationRunNames '
        ).split(),
    },
    'PrimeCandidate': {
        "reason": 'Calibration-presentation hosting studies; these do not specify a native kernel.',
        "modules": (
            'AdmissibleEvaluators CandidateSentence ChoiceExtension CombinedCandidate ContractionComplete '
            'DeterminedExactly DeterminedTables HostSentence LambdaPiUnion MatchingEvaluator '
            'MatchingLimits PresentedSteps ProbeData ProbeDynamics Reentry '
            'RunExtension SortClosure SpaceExtension SpellingEvaluator TuringUnion '
        ).split(),
    },
    'SpacesAndRegions': {
        "reason": 'Comparisons of selected stored, sealed and assembled space presentations.',
        "modules": (
            'Assembled Candidate Generated Kernel Readings '
            'Sealed SealedAsWritten SealedContexts SealedPart SealedReducts '
            'SealedSteps SealedStored SealingSpaces Stored Summary '
            'Trees '
        ).split(),
    },
    'StoredPrograms': {
        "reason": 'Stored equation-program profiles and their checker/hosting comparisons.',
        "modules": (
            'Admission Candidate Check Comparison Conversion '
            'Firing Instantiation Inventory LargerHost Letters '
            'Lists Lookup Naturals NormalForms Obstruction '
            'OneTable Overlap Replay Restriction Running '
            'SeparatedTables Sequential SharedHost Simulation SmallPrograms '
            'Summary TableCheck Translation Verification '
        ).split(),
    },
}
HOSTING_DIRECT_CROSSINGS = {
    "PrimeCandidate.HostSentence": [COMPARISONS + ".HostingStyles.KernelReading"],
    "PrimeCandidate.ProbeDynamics": [COMPARISONS + ".HostingStyles.ProbeStatics"],
}
# These twelve applications use the concrete COMM funding/generated-code
# fixture. Only the two stated owners import its comparison module directly;
# the independent cost rules and all other cost modules remain protected.
RHO_COST_APPLICATIONS = {
    'ActivationAtomicPathControls': 'Generated/activated COMM fixture, with its exact source or occurrence observations.',
    'ActivationGeneratedControls': 'Generated/activated COMM fixture, with its exact source or occurrence observations.',
    'ActivationGeneratedFundingControls': 'Generated/activated COMM fixture, with its exact source or occurrence observations.',
    'ActivationGeneratedNormalizationControls': 'Generated/activated COMM fixture, with its exact source or occurrence observations.',
    'ActivationGeneratedReceiverControls': 'Generated/activated COMM fixture, with its exact source or occurrence observations.',
    'ActivationGeneratedSignatureControls': 'Generated/activated COMM fixture, with its exact source or occurrence observations.',
    'ActivationImageControls': 'Generated/activated COMM fixture, with its exact source or occurrence observations.',
    'ActivationOccurrenceAccountingControls': 'Generated/activated COMM fixture, with its exact source or occurrence observations.',
    'ActivationOccurrencePathControls': 'Generated/activated COMM fixture, with its exact source or occurrence observations.',
    'ExecutableBudgetControls': 'Concrete unit-funding COMM fixture and executable spending/refusal observations.',
    'UnitPolicyControls': 'Concrete unit-funding COMM fixture and executable spending/refusal observations.',
    'UnitReturn': 'Concrete unit-funding COMM fixture and executable spending/refusal observations.',
}
RHO_COST_DIRECT_CROSSINGS = {
    "UnitPolicyControls": [COMPARISONS + ".Rho.TypedCommunicationVerticalBraid"],
    "ActivationGeneratedControls": [COMPARISONS + ".Rho.TypedCommunicationVerticalBraid"],
}
HOSTING_PREFIX = "Mettapedia.Logic.HostingStyles."
RHO_COST_PREFIX = "Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost."
HOSTING_APPLICATION_MODULES = {
    HOSTING_PREFIX + family + "." + member
    for family, profile in HOSTING_APPLICATION_PROFILES.items()
    for member in profile["modules"]
}
RHO_COST_APPLICATION_MODULES = {
    RHO_COST_PREFIX + member for member in RHO_COST_APPLICATIONS
}
# All remaining source owners in these subjects must be integration-free.
# Exact application membership prevents a new dependency from weakening this
# protection merely by appearing in a familiar directory.
def protected_subject_modules(graph):
    return {
        module for module in graph
        if ((module.startswith(HOSTING_PREFIX)
             and module not in HOSTING_APPLICATION_MODULES)
            or (module.startswith(RHO_COST_PREFIX)
                and module not in RHO_COST_APPLICATION_MODULES))
    }


EXTERNAL_INTEGRATIONS = {
    "Mettapedia": None,
    "Mettapedia.Languages.MeTTa.PrimeOptions.Graph": [
        COMPARISONS + ".Weights.WeightAlgebras"],
    "Mettapedia.GSLT.ReproducibleBuild.ReplayInstances": [
        CURRENT + ".Calibration.PeTTaChainerDAGReplayV1"],
    # Cost observation adapter using this candidate's certified schedule pair.
    # This exact crossing does not classify the adapter as a reusable foundation.
    "Mettapedia.GSLT.Dynamics.CostObservation": [
        CANDIDATE + ".Native.NativeCostLayerReceiptObservation"],
    # Status tracker whose evidence text (line ~819) cites these controls; admitted 2026-10-20 by main:9 under Zar's overnight mandate; reviewable.
    "Mettapedia.OSLF.Framework.FULLStatus": [
        CANDIDATE + ".DeclarationBased.NativeFormedPresheafControls"],
    # Concrete membership readings use the candidate comparison triangle.
    "Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTrinity": [
        CANDIDATE + ".Trinity.Triangle"],
}
EXTERNAL_INTEGRATIONS.update({
    module: HOSTING_DIRECT_CROSSINGS.get(module.removeprefix(HOSTING_PREFIX), [])
    for module in HOSTING_APPLICATION_MODULES
})
EXTERNAL_INTEGRATIONS.update({
    module: RHO_COST_DIRECT_CROSSINGS.get(module.removeprefix(RHO_COST_PREFIX), [])
    for module in RHO_COST_APPLICATION_MODULES
})

BUILD_ROOTS = (
    "Mettapedia",
    "Mettapedia.Languages.MeTTa.PrimeComparisons.StudyBuild",
    "Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ClosedFormationGSLTMeTTaExport",
    # The linked request client remains separate from the library barrels.
    "Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.CheckCandidateServices",
    "Mettapedia.GSLT.LanguageDef.CheckAuthoredBindingEquations",
    CANDIDATE + ".DeclarationBased.CheckCandidateBindingEquations",
    # This exporter defines main and is checked as a separate executable root.
    CANDIDATE + ".DeclarationBased.ContextualJudgmentExamples",
    "Mettapedia.OSLF.MeTTaIL.CheckAuthoredPremises",
)
IMPORT = re.compile(r"^(?:public\s+)?import\s+([\w.]+)\s*$", re.MULTILINE)
INTEGRATION_REFERENCE = re.compile(
    r"\b(PrimeCandidates|PrimeCeTTaCurrent|PrimeComparisons)\b")
REFERENCE_PREFIXES = {
    "PrimeCandidates": CANDIDATE,
    "PrimeCeTTaCurrent": CURRENT,
    "PrimeComparisons": COMPARISONS,
}
RETIRED_FOUNDATION = re.compile(
    r"\bPrime\.(?:Id|List|Vec)\.|"
    r"\bnamespace\s+Mettapedia\.Languages\.MeTTa\.Prime\b")


def source_code(source):
    """Mask comments and string contents for the supplemental lexical audit.

    This is not a Lean parser. Compilation remains necessary, particularly for
    name resolution and syntax extensions. Nested comments are handled so prose
    about a candidate does not make a generic result an integration dependency.
    """
    result, index, depth = [], 0, 0
    quoted = False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                result.append("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                result.append("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif quoted:
            if char == "\\":
                result.append("  ")
                index += 2
            else:
                quoted = char != '"'
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            result.append("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            result.append(" " * (end - index))
            index = end
        elif char == '"':
            quoted = True
            result.append(" ")
            index += 1
        else:
            result.append(char)
            index += 1
    return "".join(result)


def integration_references(source):
    if not INTEGRATION_REFERENCE.search(source):
        return set()
    return {REFERENCE_PREFIXES[name]
            for name in INTEGRATION_REFERENCE.findall(source_code(source))}


def import_only(source):
    return not IMPORT.sub("", source_code(source)).strip()


def imports(root):
    files = list((root / "Mettapedia").rglob("*.lean")) + [root / "Mettapedia.lean"]
    return {
        ".".join(path.relative_to(root).with_suffix("").parts):
            IMPORT.findall(path.read_text(encoding="utf-8"))
        for path in files
    }


def closure(graph, roots):
    seen, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module in seen or module not in graph:
            continue
        seen.add(module)
        pending.extend(graph[module])
    return seen


def under(module, prefix):
    return module == prefix or module.startswith(prefix + ".")


def violations(graph, root, forbidden):
    return sorted(module for module in closure(graph, [root])
                  if any(under(module, prefix) for prefix in forbidden))


def foreign_foundation_edges(graph):
    """Reachable foreign dependencies of every native candidate module."""
    return {root: bad for root in graph if under(root, CANDIDATE)
            if (bad := violations(graph, root, FOREIGN_FOUNDATIONS))}


def boundary_crossings(graph):
    integrations = [CANDIDATE, CURRENT, COMPARISONS]
    return {
        module: [dependency for dependency in dependencies
                 if any(under(dependency, prefix) for prefix in integrations)]
        for module, dependencies in graph.items()
        if not any(under(module, prefix) for prefix in integrations)
        and any(any(under(dependency, prefix) for prefix in integrations)
                for dependency in dependencies)
    }


def self_test(verbose=True):
    # Negative control follows a transitive leak, not just a direct import.
    graph = {"Core": ["Helper"], "Helper": [CANDIDATE], CANDIDATE: []}
    assert violations(graph, "Core", [CANDIDATE]) == [CANDIDATE]
    # A joint integration point is legitimate; the branches remain independent.
    graph = {"Core": [], CANDIDATE: ["Core"], CURRENT: [],
             COMPARISONS: [CANDIDATE, CURRENT]}
    assert not violations(graph, CANDIDATE, [CURRENT, COMPARISONS])
    assert not violations(graph, CURRENT, [CANDIDATE, COMPARISONS])
    assert CURRENT in closure(graph, [COMPARISONS])
    # A guest comparison may use both kernels; a candidate may not inherit
    # the guest, including through an apparently general helper module.
    native = CANDIDATE + ".NativeFragment"
    for prefix in FOREIGN_FOUNDATIONS:
        foreign = prefix + ".SelectedTheoryProfile"
        graph = {native: ["DTT"], "DTT": [], foreign: [],
                 COMPARISONS: [native, foreign]}
        assert not foreign_foundation_edges(graph)
        graph["DTT"] = [foreign]
        assert foreign_foundation_edges(graph) == {native: [foreign]}
    assert boundary_crossings({"UnexpectedCore": [CANDIDATE]}) == {
        "UnexpectedCore": [CANDIDATE]}
    # A fully qualified use can be hidden behind a now-removed transitive import.
    assert integration_references(
        "def specimen := Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language"
    ) == {CANDIDATE}
    assert not integration_references(
        '/- PrimeCandidates /- PrimeCeTTaCurrent -/ -/\n'
        '-- PrimeComparisons\ndef label := "PrimeCandidates.LanguageDef"')
    assert import_only("import Example.Core\n/- Collection documentation. -/")
    assert not import_only("import Example.Core\nprivate def hidden := 1")
    assert not RETIRED_FOUNDATION.search(source_code('def wire := "Prime.Id.old"'))
    assert RETIRED_FOUNDATION.search(source_code(
        "namespace Mettapedia.Languages.MeTTa.Prime"))
    # Exact application membership is not a blanket subject exemption.
    generic_host = HOSTING_PREFIX + "Unreviewed.Foundation"
    generic_cost = RHO_COST_PREFIX + "UnreviewedRules"
    reviewed = RHO_COST_PREFIX + "UnitPolicyControls"
    assert protected_subject_modules({generic_host: [], generic_cost: [], reviewed: []}) == {
        generic_host, generic_cost}
    assert generic_host not in EXTERNAL_INTEGRATIONS
    assert generic_cost not in EXTERNAL_INTEGRATIONS
    assert COMPARISONS + ".Rho.TypedCommunicationVerticalBraid" in EXTERNAL_INTEGRATIONS[reviewed]
    assert CANDIDATE + ".Unexpected" not in EXTERNAL_INTEGRATIONS[reviewed]
    cost_observation = "Mettapedia.GSLT.Dynamics.CostObservation"
    assert EXTERNAL_INTEGRATIONS[cost_observation] == [
        CANDIDATE + ".Native.NativeCostLayerReceiptObservation"]
    assert CANDIDATE + ".Unexpected" not in EXTERNAL_INTEGRATIONS[cost_observation]
    if verbose:
        print("Import-boundary and qualified-reference positive/negative controls passed.")


def main():
    from check_type_theory_subject_boundaries import main as check_subject_boundaries

    passed_only = sys.argv[1:] == ["--passed-gates"]
    native_only = sys.argv[1:] == ["--native-foundation"]
    if sys.argv[1:] and not (passed_only or native_only):
        print("Usage: check_prime_spec_boundary.py [--passed-gates | --native-foundation]", file=sys.stderr)
        return 2
    self_test(verbose=not passed_only)
    graph = imports(ROOT)
    if native_only:
        bad = foreign_foundation_edges(graph)
        for root, dependencies in bad.items():
            for dependency in dependencies:
                print(f"Native candidate reaches foreign foundation: {root} -> {dependency}")
        print(f"Native foundation gate: {sum(under(m, CANDIDATE) for m in graph)} candidate modules; "
              f"{len(bad)} foreign-foundation violations")
        return int(bool(bad))
    references = {
        module: integration_references(
            ROOT.joinpath(*module.split(".")).with_suffix(".lean").read_text(encoding="utf-8"))
        for module in graph
    }
    failures = []
    foreign_edges = foreign_foundation_edges(graph)
    failures.extend(f"Native candidate reaches foreign foundation: {root} -> {dependency}"
                    for root, dependencies in foreign_edges.items()
                    for dependency in dependencies)
    if not passed_only:
        print(f"Native candidate/foreign-foundation isolation: {len(foreign_edges)} violations")
    if check_subject_boundaries(verbose=not passed_only):
        failures.append("Reusable type-theory/machine subject boundary audit failed")
    root_passed = {}
    passed_gates = []
    for root in CORE_ROOTS:
        if root not in graph:
            failures.append(f"Missing core entry: {root}")
            root_passed[root] = False
            continue
        bad = violations(graph, root, [CANDIDATE, CURRENT, COMPARISONS])
        referenced = sorted(module for module in closure(graph, [root])
                            if references[module])
        root_passed[root] = not bad and not referenced
        failures.extend(f"{root} imports integration: {module}" for module in bad)
        failures.extend(f"{root} reaches integration name reference in: {module}"
                        for module in referenced)
        if not passed_only:
            print(f"Core closure {root}: {len(closure(graph, [root]))} project modules; "
                  f"{len(bad)} integration dependencies")
    protected = protected_subject_modules(graph)
    protected_failures = len(failures)
    for root in sorted(protected):
        bad = violations(graph, root, [CANDIDATE, CURRENT, COMPARISONS])
        referenced = sorted(module for module in closure(graph, [root])
                            if references[module])
        failures.extend(f"Protected subject {root} imports integration: {module}"
                        for module in bad)
        failures.extend(f"Protected subject {root} reaches integration name: {module}"
                        for module in referenced)
    if not passed_only:
        hosting_count = sum(module.startswith(HOSTING_PREFIX) for module in protected)
        cost_count = sum(module.startswith(RHO_COST_PREFIX) for module in protected)
        print(f"Independent hosting/cost subjects: {hosting_count}/{cost_count} modules; "
              f"{len(failures) - protected_failures} findings")
    for root in CANDIDATE_EVIDENCE_ROOTS:
        if root not in graph:
            failures.append(f"Missing candidate evidence entry: {root}")
            root_passed[root] = False
            continue
        bad = violations(graph, root, [CURRENT, COMPARISONS])
        referenced = sorted(module for module in closure(graph, [root])
                            if references[module].intersection([CURRENT, COMPARISONS]))
        root_passed[root] = not bad and not referenced
        failures.extend(f"{root} imports opposite branch: {module}" for module in bad)
        failures.extend(f"{root} reaches opposite-branch reference in: {module}"
                        for module in referenced)
    for gate, roots in GATE_ROOTS.items():
        if all(root_passed.get(root, False) for root in roots):
            passed_gates.append(gate)
    before_branches = len(failures)
    for root in [CANDIDATE + ".Index.Specification", CANDIDATE + ".Index.DevelopmentPlan", CURRENT]:
        if root not in graph:
            failures.append(f"Missing independent entry: {root}")
    for root in graph:
        if under(root, CANDIDATE):
            forbidden = [CURRENT, COMPARISONS]
        elif under(root, CURRENT):
            forbidden = [CANDIDATE, COMPARISONS]
        else:
            continue
        failures.extend(f"{root} imports opposite branch: {module}"
                        for module in violations(graph, root, forbidden))
        failures.extend(f"{root} reaches opposite-branch reference in: {module}"
                        for module in closure(graph, [root])
                        if references[module].intersection(forbidden))
    for module in graph:
        source = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        content = source.read_text(encoding="utf-8")
        if under(module, CURRENT):
            # Preserve historical wire strings, not retired code namespaces.
            content = source_code(content)
        if RETIRED_FOUNDATION.search(content):
            failures.append(f"Retired foundation spelling in active source: {module}")
    if len(failures) == before_branches:
        passed_gates.append("isolation.integration-direction-and-names")
    before_classification = len(failures)
    crossings = boundary_crossings(graph)
    for module, mentioned in references.items():
        if mentioned and not any(under(module, prefix)
                                 for prefix in [CANDIDATE, CURRENT, COMPARISONS]):
            if module not in EXTERNAL_INTEGRATIONS:
                failures.append(f"Unclassified integration-name consumer: {module}")
    for module, dependencies in crossings.items():
        if module not in EXTERNAL_INTEGRATIONS:
            failures.append(f"Unclassified integration consumer: {module}")
            continue
        admitted = EXTERNAL_INTEGRATIONS[module]
        if admitted is None:
            source = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
            if not import_only(source.read_text(encoding="utf-8")):
                failures.append(f"Import-only entry now contains declarations: {module}")
        else:
            failures.extend(f"Unreviewed crossing from {module}: {dependency}"
                            for dependency in dependencies if dependency not in admitted)
    if len(failures) == before_classification and all(root_passed.values()):
        passed_gates.append("isolation.classified-crossings")
    reachable = closure(graph, BUILD_ROOTS)
    collection = {module for module in graph
                  if under(module, CANDIDATE) or under(module, CURRENT)}
    missing = sorted(collection - reachable)
    failures.extend(f"Outside declared combined build roots: {module}" for module in missing)
    missing_core = sorted(set(EVIDENCE_ROOTS) - reachable)
    failures.extend(f"Semantic evidence outside declared combined build roots: {module}"
                    for module in missing_core)
    if not passed_only:
        print(f"Candidate/current collection coverage: {len(collection - set(missing))}"
              f"/{len(collection)} modules via declared combined roots")
        print(f"Declared semantic-root coverage: {len(EVIDENCE_ROOTS) - len(missing_core)}"
              f"/{len(EVIDENCE_ROOTS)} roots via declared combined roots")
        print(f"Reviewed external integration consumers: {len(crossings)}; "
              f"{sum(map(len, crossings.values()))} direct boundary edges")
        print(f"Plan source gates: {len(passed_gates)}/{len(GATE_ROOTS) + 2}")
    else:
        print("\n".join(passed_gates))
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    if not passed_only:
        print("Declared roots are independent. Reviewed application/build entries "
              "remain integrations, not foundations; classifications do not prove prose claims.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
