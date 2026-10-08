import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.ScopedSyntax
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Types
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ContextualCommunication
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.RedexPosition
import Mettapedia.OSLF.Framework.GeneratedHypercube
import Mettapedia.OSLF.Framework.GeneratedHypercubeInstances
import Mettapedia.OSLF.Framework.GeneratedModality
import Mettapedia.OSLF.Framework.GeneratedModalFamily
import Mettapedia.OSLF.Framework.GeneratedModalityRho
import Mettapedia.OSLF.Framework.RelyPossiblyScheme
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.InitialModalSchema
import Mettapedia.OSLF.Framework.PureInternalization
import Mettapedia.OSLF.Framework.ArithmeticEquationCalculus
import Mettapedia.UniversalAlgebra.OSLF.ModalSemantics
import Mettapedia.UniversalAlgebra.NIK.Authority
import Mettapedia.OSLF.Framework.InitialityConsistencySeparation
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.LanguageMorphism
import Mettapedia.OSLF.Framework.LanguageEqCategory
import Mettapedia.OSLF.Framework.LanguageEqCategoryLaws
import Mettapedia.OSLF.Framework.ModeTheory
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.OSLF.Framework.IndexedModalFunctor
import Mettapedia.OSLF.Framework.Mode2Skeleton
import Mettapedia.OSLF.Framework.Mode2PureBoundary
import Mettapedia.OSLF.Framework.Mode2SkeletonLaws
import Mettapedia.OSLF.Framework.ModeMapPredCommutingSquares
import Mettapedia.OSLF.Framework.MATTProvableNow
import Mettapedia.OSLF.Framework.MATTClaimMap
import Mettapedia.OSLF.Framework.FULLStatus
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.SelectedNativeTypeCalculusCompilerTransport
import Mettapedia.OSLF.Framework.DisplayedRewriteOccurrenceTyping
import Mettapedia.OSLF.StructuralModal.Recursive
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL
import Mettapedia.OSLF.Framework.GeneratedTyping
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.Framework.LanguagePresheafSharing
import Mettapedia.OSLF.Framework.LambdaInstance
import Mettapedia.OSLF.Framework.PetriNetInstance
import Mettapedia.OSLF.Framework.TinyMLInstance
import Mettapedia.OSLF.Framework.MeTTaMinimalInstance
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Framework.PLNSelectorGSLT
import Mettapedia.OSLF.Framework.PLNSelectorLanguageDef
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.Languages.MeTTa.OSLFCore.Premises
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef
import Mettapedia.OSLF.Framework.MeTTaFullLegacyInstance
import Mettapedia.OSLF.Framework.MeTTaLegacyToNTT
import Mettapedia.OSLF.Framework.OSLFNTTWMBridge
import Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure
import Mettapedia.OSLF.Framework.ModalSubobjectBridge
import Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure
import Mettapedia.OSLF.Formula
import Mettapedia.GSLT.LanguageDef.BinderAlphaSemantics
import Mettapedia.GSLT.LanguageDef.DerivedEquationCanaries
import Mettapedia.OSLF.StructuralModal.EquationInvariance
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SpatialReadingCanary
import Mettapedia.GSLT.Logic.HennessyMilnerDirections
import Mettapedia.GSLT.Logic.AdmissibleContextCongruence
import Mettapedia.OSLF.StructuralModal.SeparatingConjunction
import Mettapedia.OSLF.Framework.ObserverExtension
import Mettapedia.OSLF.Framework.ObserverBisimilarity
import Mettapedia.OSLF.Framework.ObserverReconstruction
import Mettapedia.OSLF.Framework.FormulaFixpoint
import Mettapedia.OSLF.Framework.TubeShape
import Mettapedia.OSLF.Framework.GeneratedScope
import Mettapedia.OSLF.Framework.GeneratedScopeRho
import Mettapedia.OSLF.Framework.SourceGenerator
import Mettapedia.OSLF.StructuralModal.AdmissibleEquations
import Mettapedia.OSLF.Framework.ScopeComparison
import Mettapedia.OSLF.Framework.SortedEquationFrame
import Mettapedia.OSLF.Framework.GeneratorLength
import Mettapedia.GSLT.Dynamics.EvidenceWeighting
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSlotLaws
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformValidation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformModalFamily
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSubstitutability
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquations
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquationDiscipline
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSourceScope
import Mettapedia.OSLF.Framework.RelyPossiblyTypeFormer
import Mettapedia.OSLF.Framework.GeneratedScopeSignature
import Mettapedia.GSLT.Logic.LeastEnablerBox
import Mettapedia.GSLT.Logic.IPOBox
import Mettapedia.GSLT.Logic.RelativePushout
import Mettapedia.GSLT.Logic.RedexRelativeCongruence
import Mettapedia.GSLT.Logic.BagRelativePushout
import Mettapedia.GSLT.Logic.RedexRelativeEnabling
import Mettapedia.GSLT.Logic.ParallelLeastEnablerFails
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.AdmissibleContexts
import Mettapedia.GSLT.Logic.HennessyMilnerTransport
import Mettapedia.OSLF.Framework.FormulaAdequacy
import Mettapedia.OSLF.Framework.EnumeratedAdequacy
import Mettapedia.OSLF.Framework.IndexedOperationalAdequacy
import Mettapedia.OSLF.StructuralModal.BehaviouralAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionInterpretationCanary
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.GSLT.Logic.HigherOrderHML
import Mettapedia.GSLT.Logic.HigherOrderHMLControls
import Mettapedia.GSLT.Logic.MinimalEnablingContext
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
import Mettapedia.OSLF.Framework.HigherOrderNativeTypeControls
import Mettapedia.OSLF.Framework.ConcreteHennessyMilnerBridge
import Mettapedia.OSLF.Framework.MinimalContextNativeTypes
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerInstance
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.BackwardBranchingBoundary
import Mettapedia.OSLF.Decidability
import Mettapedia.OSLF.QuantifiedFormula
import Mettapedia.OSLF.QuantifiedFormula2
import Mettapedia.OSLF.Framework.DistinctionGraph
import Mettapedia.OSLF.Framework.DistinctionGraph.Weighted
import Mettapedia.OSLF.Framework.DistinctionGraph.WorldModel
import Mettapedia.OSLF.Framework.DistinctionGraph.Entropy
import Mettapedia.OSLF.Bridges.Foundation.Kripke
import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.OSLF.Syntax.PartialRenaming
import Mettapedia.OSLF.Syntax.ScopedMatching
import Mettapedia.OSLF.Syntax.RedexPositionIsExtraInput
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema
import Mettapedia.OSLF.Syntax.SemanticSchemaNaturality
import Mettapedia.OSLF.Syntax.RhoSchemaSemanticNaturality
import Mettapedia.OSLF.Syntax.SemanticContextualMetavariables
import Mettapedia.OSLF.Syntax.AuthoredPositionedRulePolynomial
import Mettapedia.OSLF.Syntax.AuthoredPositionedRootComparison
import Mettapedia.OSLF.Syntax.RhoPositionedOperationalModel
import Mettapedia.OSLF.Syntax.SemanticScopedPremiseInterpretation
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPolynomial
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalFreeGenerators
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalFiniteContextSemantics
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalRelativeLexClassification
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalFiniteContextChange
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalTotalContext
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalClassifierContext
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalClassifierSetSemantics
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalClassifierSetControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalActedFiniteContext
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalActedBaseChange
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFree
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFiniteContext
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedBaseChange
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedEquivalence
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedBindingRestriction
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTypeComparisonNaturality
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFoldComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetCoherence
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetProgramTransport
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetOperations
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetClassificationFold
import Mettapedia.OSLF.Syntax.CategoricalBindingClosedTargetChange
import Mettapedia.OSLF.Syntax.CategoricalBindingSquareTargetControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTypeComparisonControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramProducts
import Mettapedia.OSLF.Syntax.ContextualEquationInstances
import Mettapedia.OSLF.Syntax.ContextualEquationCongruence
import Mettapedia.OSLF.Syntax.CategoricalContextualEquationSoundness
import Mettapedia.OSLF.Syntax.CategoricalContextualSatisfactionEquivalence
import Mettapedia.OSLF.Syntax.CategoricalVaryingEquationSatisfactionCounterexample
import Mettapedia.OSLF.Syntax.MonoidContextualEquationControl
import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionEquations
import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionEvaluation
import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionYonedaControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafExtensionFold
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramSelectedExponentials
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramParameterApplication
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaVariableMeaning
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramMeaningApplication
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramMeaningRepresentatives
import Mettapedia.OSLF.Syntax.CategoricalBindingGenericApplication
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramData
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramArgumentProjection
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramConstructorMetavariable
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramBinderCurrying
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramDataProjections
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaStructured
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafProgramModel
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEvents
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafContextHom
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafSubstitution
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafNaturalEvidence
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEventPowers
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEventFunctions
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafActions
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafReduction
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafSharedComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafExtensionControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedJsonClassifiedInstance
import Mettapedia.OSLF.Syntax.IntrinsicScopedMonoidClassifiedInstance
import Mettapedia.OSLF.Syntax.IntrinsicScopedLambdaClassifiedMultiplicity
import Mettapedia.OSLF.Syntax.IntrinsicScopedRhoExecutorClassifiedInstance
import Mettapedia.OSLF.Syntax.IntrinsicScopedClassifiedTelescopeCoverageControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedClassifiedSubstitutionGapControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafLambdaControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafMultiplicityControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafCoproductControl
import Mettapedia.OSLF.Syntax.PresheafStructuredExtensionTargetChange
import Mettapedia.OSLF.Syntax.PresheafStructuredExtensionCoproduct
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafEvents
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafEventsExtension
import Mettapedia.OSLF.Syntax.PresheafEventImageComparisonControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedTelescopeCoverageControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionGapControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitution
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPresheaf
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalClosedInterpretation
import Mettapedia.OSLF.Syntax.Chapter7ClosedBindingControl
import Mettapedia.OSLF.Syntax.BindingOperationPresheaf
import Mettapedia.OSLF.Syntax.BindingFunctionArgumentComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelPresheaf
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalModelPresheafControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedSharedLocalComparisonControls
import Mettapedia.OSLF.Syntax.ModelPresheafExtraEventControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelHistory
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelModal
import Mettapedia.OSLF.Syntax.Chapter7LambdaModelHistoryModal
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelObservation
import Mettapedia.OSLF.Syntax.ScopedOperationalEvidenceExponential
import Mettapedia.OSLF.Syntax.CategoricalScopedEventPremise
import Mettapedia.OSLF.Syntax.ScopedOperationalPremiseModel
import Mettapedia.OSLF.Syntax.IntrinsicRulePremiseRequest
import Mettapedia.OSLF.Syntax.IntrinsicRuleActionComparison
import Mettapedia.OSLF.Syntax.ScopedPremiseEvidenceComparison
import Mettapedia.OSLF.Syntax.Chapter7LambdaScopedEvidence
import Mettapedia.OSLF.Syntax.SecondOrderContextCategory
import Mettapedia.OSLF.Syntax.SecondOrderEquationUniversal
import Mettapedia.OSLF.Syntax.Chapter7MonoidSecondOrderEquations
import Mettapedia.OSLF.Syntax.SecondOrderBindingAlgebraMap
import Mettapedia.OSLF.Syntax.SecondOrderAuthoredEquationPresentation
import Mettapedia.OSLF.Syntax.SecondOrderEquationRepresentability
import Mettapedia.OSLF.Syntax.SecondOrderEquationProducts
import Mettapedia.OSLF.Syntax.SecondOrderEquationLexCompletion
import Mettapedia.OSLF.Syntax.SecondOrderEquationModelFiber
import Mettapedia.OSLF.Syntax.SecondOrderOperationalEventObject
import Mettapedia.OSLF.Syntax.SecondOrderOperationalHistory
import Mettapedia.OSLF.Syntax.SecondOrderOperationalClosedComparison
import Mettapedia.OSLF.Syntax.SecondOrderOperationalDiagramInterpretation
import Mettapedia.OSLF.Syntax.Chapter7SecondOrderOperationalInstances
import Mettapedia.OSLF.Syntax.Chapter7PatternSecondOrderEquations
import Mettapedia.OSLF.Syntax.RhoPayloadPresentation
import Mettapedia.OSLF.Syntax.RhoPayloadTranslation
import Mettapedia.OSLF.Syntax.RhoPayloadExecutorComparison
import Mettapedia.OSLF.Syntax.RhoWholeNameAdmission
import Mettapedia.OSLF.Syntax.RhoCanonicalWholeNameAdmission
import Mettapedia.OSLF.Syntax.RhoPayloadConstruction
import Mettapedia.OSLF.Syntax.RhoPayloadResources
import Mettapedia.OSLF.Syntax.RhoExecutorResources
import Mettapedia.OSLF.Syntax.CategoricalBindingGroupoid
import Mettapedia.OSLF.Syntax.CategoricalBindingInterpretationMaps
import Mettapedia.OSLF.Syntax.CategoricalBindingEquivalence
import Mettapedia.OSLF.Syntax.CategoricalBindingEquationEquivalence
import Mettapedia.OSLF.Syntax.CategoricalBindingQuotientEquivalence
import Mettapedia.OSLF.Syntax.CategoricalBindingOperationalReindex
import Mettapedia.OSLF.Syntax.CategoricalBindingEventEquivalence
import Mettapedia.OSLF.Syntax.CategoricalBindingEventImage
import Mettapedia.OSLF.Syntax.CategoricalScopedRuleActionMaps
import Mettapedia.OSLF.Syntax.CategoricalScopedEventBaseChange
import Mettapedia.OSLF.Syntax.CategoricalScopedEventContravariantTransport
import Mettapedia.OSLF.Syntax.CategoricalAuthoredRuleInterpretation
import Mettapedia.OSLF.Syntax.CategoricalAuthoredProgramCarrierMaps
import Mettapedia.OSLF.Syntax.CategoricalAuthoredScopedInterpretationMaps
import Mettapedia.OSLF.Syntax.CategoricalAuthoredOperationalModels
import Mettapedia.OSLF.Syntax.CategoricalAuthoredExtraEvents
import Mettapedia.OSLF.Syntax.CategoricalAuthoredReductionObservations
import Mettapedia.OSLF.Syntax.CategoricalAuthoredEventPaths
import Mettapedia.OSLF.Syntax.CategoricalAuthoredEventModal
import Mettapedia.OSLF.Syntax.CategoricalAuthoredProgramRestriction
import Mettapedia.OSLF.Syntax.CategoricalAuthoredEventCocones
import Mettapedia.OSLF.Syntax.CategoricalAuthoredRulePolynomial
import Mettapedia.OSLF.Syntax.CategoricalAuthoredRuleFamilyAlgebra
import Mettapedia.OSLF.Syntax.CategoricalAuthoredRuleFamilyPolynomial
import Mettapedia.OSLF.Syntax.CategoricalAuthoredFreeAlgebraBoundary
import Mettapedia.OSLF.Syntax.CategoricalAuthoredNullaryFree
import Mettapedia.OSLF.Syntax.CategoricalAuthoredNullaryInstances
import Mettapedia.OSLF.Syntax.CategoricalAuthoredNullaryAdjunction
import Mettapedia.OSLF.Syntax.IntrinsicCategoricalRuleMapComparison
import Mettapedia.OSLF.Syntax.IntrinsicLambdaScopedConditionalExample
import Mettapedia.OSLF.Syntax.IntrinsicLambdaFourRulePresentation
import Mettapedia.OSLF.Syntax.RhoDropProfile
import Mettapedia.OSLF.Syntax.RhoOperationalClosure
import Mettapedia.OSLF.Syntax.RhoAuthoredDropProfile
import Mettapedia.OSLF.Syntax.RhoEventMultiplicity
import Mettapedia.OSLF.Syntax.RewriteEventHistory
import Mettapedia.OSLF.Syntax.RewriteClassEventHistory
import Mettapedia.OSLF.Syntax.RewriteEventGraphObject
import Mettapedia.OSLF.Syntax.ContextualRootEvents
import Mettapedia.OSLF.Syntax.ContextualLocatedEvents
import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents
import Mettapedia.OSLF.Syntax.ContextualEventHistoryComparison
import Mettapedia.OSLF.Syntax.ContextualReductionSubobject
import Mettapedia.OSLF.Syntax.FreeBindingTermsRho
import Mettapedia.OSLF.Syntax.BindingSubstitutionAlgebraRho
import Mettapedia.OSLF.Syntax.FreeBindingClone
import Mettapedia.OSLF.Syntax.RhoSemanticMetavariables
import Mettapedia.OSLF.Syntax.RhoEquationModelControls
import Mettapedia.OSLF.Syntax.RhoFreeBindingEquationModel
import Mettapedia.OSLF.Syntax.RhoDropBoundary
import Mettapedia.OSLF.Syntax.RhoIntrinsicEncoding
import Mettapedia.OSLF.Syntax.RhoSubstitutionEncoding
import Mettapedia.OSLF.Syntax.RhoEquationEncoding
import Mettapedia.OSLF.Syntax.BindingEquationExtension
import Mettapedia.OSLF.Syntax.RhoSourceEquationModel
import Mettapedia.OSLF.Syntax.RuleListEventEmbedding
import Mettapedia.OSLF.Syntax.RhoSourceEventComparison
import Mettapedia.OSLF.Syntax.EquationExtensionEventGraph
import Mettapedia.OSLF.Syntax.RhoEquationEventComparison
import Mettapedia.OSLF.Syntax.RhoContextScopeComparison
import Mettapedia.OSLF.Syntax.JsonTermRung
import Mettapedia.OSLF.Syntax.JsonAuthoredComparison
import Mettapedia.OSLF.Syntax.JsonCollectionRepresentationBoundary
import Mettapedia.OSLF.Syntax.JsonTaggedDataEncoding
import Mettapedia.OSLF.Syntax.MonoidEquationRung
import Mettapedia.OSLF.Syntax.MonoidAuthoredComparison
import Mettapedia.OSLF.Syntax.Chapter7AlgebraicOperationalInstances
import Mettapedia.OSLF.Syntax.MonoidFiniteModelBoundary
import Mettapedia.OSLF.Syntax.LambdaContextualRung
import Mettapedia.OSLF.Syntax.LambdaAuthoredBoundary
import Mettapedia.OSLF.Syntax.BinderLocalPremise
import Mettapedia.OSLF.Syntax.LambdaIntrinsicPresentation
import Mettapedia.OSLF.Syntax.Chapter7ReductionSubobjectInstances
import Mettapedia.OSLF.Syntax.LambdaReductionSubobject
import Mettapedia.OSLF.Syntax.LambdaCategoricalModel
import Mettapedia.OSLF.Syntax.LambdaDerivationGraph
import Mettapedia.OSLF.Syntax.LambdaFreePresheafEvents
import Mettapedia.OSLF.Syntax.ContextualTermAbstraction
import Mettapedia.OSLF.Syntax.BoundTermExponential
import Mettapedia.OSLF.Syntax.LambdaExponentialComparison
import Mettapedia.OSLF.Syntax.LambdaChosenExponential
import Mettapedia.OSLF.Syntax.BindingCloneContextComparison
import Mettapedia.OSLF.Syntax.BindingEquationContextExtension
import Mettapedia.OSLF.Syntax.BindingEquationOperationRepresentable
import Mettapedia.OSLF.Syntax.RhoEquationContextRepresentability
import Mettapedia.OSLF.Syntax.LawvereFiniteLimitBoundary
import Mettapedia.OSLF.Syntax.FiniteLimitShapes
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedYoneda
import Mettapedia.OSLF.Syntax.FormalFiniteLimitObjects
import Mettapedia.OSLF.Syntax.FormalFiniteLimitAuthoredBoundary
import Mettapedia.OSLF.Syntax.CartesianContextModels
import Mettapedia.OSLF.Syntax.CartesianContextProducts
import Mettapedia.OSLF.Syntax.CartesianModelOrthogonality
import Mettapedia.OSLF.Syntax.CartesianModelReflection
import Mettapedia.OSLF.Syntax.CartesianModelLocalPresentability
import Mettapedia.OSLF.Syntax.CartesianModelFinitePresentations
import Mettapedia.OSLF.Syntax.CartesianModelFiniteGeneration
import Mettapedia.OSLF.Syntax.CartesianModelSetSemantics
import Mettapedia.OSLF.Syntax.CartesianModelLexRestriction
import Mettapedia.OSLF.Syntax.CartesianModelLexTarget
import Mettapedia.OSLF.Syntax.CartesianModelLexUniqueness
import Mettapedia.OSLF.Syntax.CartesianModelLexGenerationDual
import Mettapedia.OSLF.Syntax.CartesianModelLexInternalGeneration
import Mettapedia.OSLF.Syntax.CartesianModelLexPropertyTransport
import Mettapedia.OSLF.Syntax.CartesianModelLexRepresentability
import Mettapedia.OSLF.Syntax.CartesianModelLexPresheafExtension
import Mettapedia.OSLF.Syntax.CartesianModelLexYonedaExtension
import Mettapedia.OSLF.Syntax.CartesianModelLexTargetDescent
import Mettapedia.OSLF.Syntax.CartesianModelLexPresheafFullness
import Mettapedia.OSLF.Syntax.CartesianModelLexTargetFullness
import Mettapedia.OSLF.Syntax.CartesianModelLexTargetEquivalence
import Mettapedia.OSLF.Syntax.CartesianModelLexEventInterpretations
import Mettapedia.OSLF.Syntax.CartesianModelFormalComparison
import Mettapedia.OSLF.Syntax.CartesianModelSiftedColimits
import Mettapedia.OSLF.Syntax.RhoCartesianContextModels
import Mettapedia.OSLF.Syntax.RhoCartesianModelOrthogonality
import Mettapedia.OSLF.Syntax.RhoCartesianModelReflection
import Mettapedia.OSLF.Syntax.RhoCartesianModelLocalPresentability
import Mettapedia.OSLF.Syntax.RhoCartesianModelFiniteGeneration
import Mettapedia.OSLF.Syntax.RhoCartesianModelSetSemantics
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexRestriction
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexTarget
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexGenerationDual
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexInternalGeneration
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexPresheafExtension
import Mettapedia.OSLF.Syntax.RhoCartesianModelLexTargetEquivalence
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedPresheaves
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedContextEmbedding
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedExactInclusion
import Mettapedia.OSLF.Syntax.FiniteLimitUniversalBoundary
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedAuthoredContexts
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedWithObjects
import Mettapedia.OSLF.Syntax.RhoEventQuotientDescentBoundary
import Mettapedia.OSLF.Syntax.RhoOperationalFiniteLimitCategory
import Mettapedia.OSLF.Syntax.Chapter6Communication
import Mettapedia.OSLF.Syntax.FreePresheafEventExtension
import Mettapedia.OSLF.Syntax.FreePresheafEventGeneratorMaps
import Mettapedia.OSLF.Syntax.StableRewriteRelationBoundary
import Mettapedia.OSLF.Syntax.RepresentedReductionTheory
import Mettapedia.OSLF.Syntax.LanguageReductionRepresentation
import Mettapedia.OSLF.Syntax.RhoFreePresheafEvents
import Mettapedia.OSLF.Syntax.FreePresheafEventImage
import Mettapedia.OSLF.Syntax.RhoSourceEquationLexClassification
import Mettapedia.OSLF.Syntax.LambdaLexExponentialComparison
import Mettapedia.OSLF.Syntax.ContextualExponentialStructure
import Mettapedia.OSLF.Syntax.LambdaBetaEtaContextQuotient
import Mettapedia.OSLF.Syntax.LambdaRuleDerivationPolynomial
import Mettapedia.OSLF.Syntax.LambdaRuleTreeSubstitution
import Mettapedia.OSLF.Syntax.LambdaRuleTreeSubstitutionComparison
import Mettapedia.OSLF.Syntax.LambdaRuleLocalPremiseComparison
import Mettapedia.OSLF.Syntax.FiniteRulePremiseLists
import Mettapedia.OSLF.Syntax.CanonicalConditionalRuleFrames
import Mettapedia.OSLF.Syntax.CanonicalConditionalOperationalClassification
import Mettapedia.OSLF.Syntax.RhoCanonicalConditionalRuleFrames
import Mettapedia.OSLF.Syntax.CanonicalRelationQueryEvents
import Mettapedia.OSLF.Syntax.CanonicalRelationQueryTranslations
import Mettapedia.OSLF.Syntax.RhoCanonicalRelationQueryEvents
import Mettapedia.OSLF.Syntax.LambdaFiniteRulePremiseComparison
import Mettapedia.OSLF.Syntax.RuleAlgebraInterpretationCoherence
import Mettapedia.OSLF.Syntax.LambdaSemanticRulePolynomial
import Mettapedia.OSLF.Syntax.IndexedRulePolynomialMorphisms
import Mettapedia.OSLF.Syntax.IndexedRuleFreeTransport
import Mettapedia.OSLF.Syntax.IndexedRulePresentationCategory
import Mettapedia.OSLF.Syntax.IndexedRuleTreeFunctor
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraMorphisms
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraCategory
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraPullback
import Mettapedia.OSLF.Syntax.IndexedOperationalPresentationCategory
import Mettapedia.OSLF.Syntax.IndexedOperationalModelsOver
import Mettapedia.OSLF.Syntax.LambdaRulePolynomialMorphism
import Mettapedia.OSLF.Syntax.LambdaOperationalPresentationComparison
import Mettapedia.OSLF.Syntax.LambdaBindingEquationOperationalInterpretation
import Mettapedia.OSLF.Syntax.LambdaEquationRuleModels
import Mettapedia.OSLF.Syntax.LambdaAuthoredRulePolynomialComparison
import Mettapedia.OSLF.Syntax.EventGraphNullaryPolynomial
import Mettapedia.OSLF.Syntax.RhoEventPolynomialComparison
import Mettapedia.OSLF.Syntax.EventGraphNullaryPresentationFunctor
import Mettapedia.OSLF.Syntax.RhoRuleListPolynomialFunctor
import Mettapedia.OSLF.Syntax.RhoSemanticRulePolynomial
import Mettapedia.OSLF.Syntax.RhoRulePolynomialMorphism
import Mettapedia.OSLF.Syntax.RhoEquationRuleModels
import Mettapedia.OSLF.Syntax.RhoClosedDropComparison
import Mettapedia.OSLF.Syntax.RhoAuthoredCommRuleCover
import Mettapedia.OSLF.Syntax.RhoQuoteSafeCommComparison
import Mettapedia.OSLF.Syntax.RhoParCongResidualSimulation
import Mettapedia.OSLF.Syntax.PresheafEventGraphTransport
import Mettapedia.OSLF.Syntax.EventGraphPolynomialTransport
import Mettapedia.OSLF.Syntax.RhoSourceLexEventInterpretations
import Mettapedia.OSLF.Syntax.RhoOperationalProfileInclusion
import Mettapedia.OSLF.Syntax.GenericEventFreeAdjunction
import Mettapedia.OSLF.Syntax.EventGraphSlice
import Mettapedia.OSLF.Syntax.LambdaGeneratedEventGraph
import Mettapedia.OSLF.Syntax.EventGraphImageMorphism
import Mettapedia.OSLF.Syntax.LambdaEventImageMultiplicity
import Mettapedia.OSLF.Syntax.OperationalImageReflection
import Mettapedia.OSLF.Syntax.CategoricalEventObservations
import Mettapedia.OSLF.Syntax.VaryingEventObservations
import Mettapedia.OSLF.Syntax.VaryingEventObservationTargetChange
import Mettapedia.OSLF.Syntax.IndexedOperationalModelReindex
import Mettapedia.OSLF.Syntax.IndexedOperationalPresentationTransport
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionComparison
import Mettapedia.OSLF.Syntax.CartesianModelLexOperationalInterpretations
import Mettapedia.OSLF.Syntax.CartesianModelLexObservedInterpretations
import Mettapedia.OSLF.Syntax.RhoSourceLexObservedInterpretations
import Mettapedia.OSLF.Syntax.PresentationEventModalComparison
import Mettapedia.OSLF.Syntax.EventGraphModalTransport
import Mettapedia.OSLF.Syntax.RewriteEventHistoryForward
import Mettapedia.OSLF.Syntax.RhoRepresentedReduction
import Mettapedia.OSLF.Syntax.RhoCommunicationEncoding
import Mettapedia.OSLF.Syntax.RhoCombinedInterpretedStep
import Mettapedia.OSLF.Syntax.RhoScopedCombinedComparison
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCaptureCanary
import Mettapedia.OSLF.Syntax.ProcAsBindingSignature
import Mettapedia.OSLF.Syntax.SignatureMorphism
import Mettapedia.OSLF.Syntax.SignatureMorphismMetas
import Mettapedia.OSLF.Syntax.TheoryMorphism
import Mettapedia.OSLF.Syntax.PositionEnumeration
import Mettapedia.OSLF.Syntax.EquationalQuotient
import Mettapedia.OSLF.Syntax.EquationTransport
import Mettapedia.OSLF.Syntax.PatternAsBindingSignature
import Mettapedia.OSLF.Syntax.StepRelationCaptureWitness
import Mettapedia.OSLF.Syntax.PatternRepairWitness
import Mettapedia.OSLF.Syntax.PatternSubstEquation
import Mettapedia.OSLF.Syntax.SubstitutionRegressionGuard
import Mettapedia.OSLF.Syntax.CollectionRestWitness
import Mettapedia.OSLF.Syntax.CollectionRestCaptureWitness
import Mettapedia.OSLF.Syntax.RuleVariableSurvivalWitness
import Mettapedia.OSLF.MeTTaIL.RuleBindingRegression
import Mettapedia.OSLF.MeTTaIL.CollectionMatchingRegression
import Mettapedia.OSLF.Syntax.ObservationClosure
import Mettapedia.OSLF.Syntax.ObservationClosureWitness
import Mettapedia.OSLF.Syntax.NormalFormStrength
import Mettapedia.OSLF.Syntax.ScopedShift
import Mettapedia.OSLF.Syntax.ContextualSplitting
import Mettapedia.OSLF.Syntax.FireSparseness
import Mettapedia.OSLF.Syntax.SyntacticCategory
import Mettapedia.OSLF.Syntax.SyntacticTermPresheaf
import Mettapedia.OSLF.Syntax.Presentation
import Mettapedia.OSLF.Framework.GeneratedLayerAdjunction
import Mettapedia.OSLF.Framework.LogicalMetric
import Mettapedia.OSLF.Framework.ScopeStratum
import Mettapedia.OSLF.Framework.ObserverIdempotence
import Mettapedia.OSLF.Framework.TypeFormerExtension
import Mettapedia.OSLF.SourceLedger
import Mettapedia.OSLF.Syntax.UniqueDecompositionFails
import Mettapedia.OSLF.Syntax.UniqueDecompositionRepaired
import Mettapedia.OSLF.Syntax.UnfoldingBreaksDecomposition
import Mettapedia.OSLF.Syntax.GSLTBridge
import Mettapedia.OSLF.Syntax.ModalityAndObservation
import Mettapedia.OSLF.Syntax.ContextCategory
import Mettapedia.OSLF.Syntax.LinearContexts
import Mettapedia.OSLF.Syntax.TermClone
import Mettapedia.OSLF.Syntax.LawvereContextBoundary
import Mettapedia.OSLF.MeTTaIL.DepthAlignmentAudit
import Mettapedia.GSLT.Logic.ImageFinitenessNecessary
import Mettapedia.OSLF.Syntax.TransitionsAreEvents
import Mettapedia.OSLF.MeTTaIL.ScopedStepPremise
import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
import Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise
import Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
import Mettapedia.OSLF.Syntax.ScopedPremiseElaborationExecution
import Mettapedia.OSLF.Syntax.CanonicalScopedRuleExecution
import Mettapedia.OSLF.Syntax.CanonicalContextOracle
import Mettapedia.OSLF.Syntax.CanonicalContextFreeModel
import Mettapedia.OSLF.Syntax.SortIndexedScopedOperationalPresentation
import Mettapedia.OSLF.Syntax.SortIndexedScopedTreeLifting
import Mettapedia.OSLF.Syntax.SortIndexedScopedFreeModel
import Mettapedia.OSLF.Syntax.ResultSortedScopedFreeModel
import Mettapedia.OSLF.Syntax.AdmittedJudgmentRulePresentation
import Mettapedia.OSLF.Syntax.SortIndexedScopedTypingAdmission
import Mettapedia.OSLF.Syntax.CanonicalScopedOperationalClassification
import Mettapedia.GSLT.Examples.ScopedPremiseAuthoring
import Mettapedia.OSLF.Syntax.LambdaScopedAuthoringComparison
import Mettapedia.OSLF.Syntax.BindingPatternRendering
import Mettapedia.OSLF.Syntax.LambdaPatternRendering
import Mettapedia.OSLF.Syntax.LambdaAuthoredBetaExecutionComparison
import Mettapedia.OSLF.Syntax.LambdaAuthoredLamCongExecutionComparison
import Mettapedia.OSLF.Syntax.LambdaAuthoredFullRuleProfile
import Mettapedia.OSLF.Syntax.LambdaAuthoredAppCongExecutionComparison
import Mettapedia.OSLF.Syntax.LambdaAuthoredCanonicalFreeComparison
import Mettapedia.OSLF.Syntax.LambdaAuthoredTypingComparison
import Mettapedia.OSLF.Syntax.CanonicalCompiledRuleShapeAdmission
import Mettapedia.OSLF.Syntax.LambdaAuthoredResultSortedShapes
import Mettapedia.OSLF.Syntax.CanonicalCompiledOneFuelAdmission
import Mettapedia.OSLF.Syntax.LambdaAuthoredOneFuelResultSorted
import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
import Mettapedia.GSLT.Examples.ScopedLamCongExecution
import Mettapedia.GSLT.Examples.CanonicalScopedRuleExecution
import Mettapedia.GSLT.Examples.CanonicalContextOracle
import Mettapedia.GSLT.Examples.SortIndexedScopedLamCong
import Mettapedia.GSLT.Examples.ResultSortedScopedLamCongTree
import Mettapedia.GSLT.Examples.CanonicalScopedFreeModel
import Mettapedia.GSLT.Examples.TypedScopedLamCongOccurrence
import Mettapedia.GSLT.LanguageDef.TypedRootPremiseAssignment
import Mettapedia.GSLT.Examples.TypedRootPremiseAssignment
import Mettapedia.GSLT.LanguageDef.TypedFullSpineRecovery
import Mettapedia.GSLT.LanguageDef.TypedPermutedSpineRecovery
import Mettapedia.GSLT.LanguageDef.RestAwareSupportSubstitution
import Mettapedia.GSLT.LanguageDef.TypedPartialSpineRecovery
import Mettapedia.GSLT.LanguageDef.TypedPartialSpineStepResults
import Mettapedia.GSLT.LanguageDef.TypedOrderedPremiseExecution
import Mettapedia.GSLT.LanguageDef.TypedOrderedRootPremiseActions
import Mettapedia.GSLT.Examples.TypedMixedPremiseHistory
import Mettapedia.OSLF.Syntax.ResultSortedMixedPremises
import Mettapedia.OSLF.Syntax.SelectedResultSortedMixedPremises
import Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier
import Mettapedia.GSLT.Examples.MixedPremiseExactChild
import Mettapedia.GSLT.Examples.MixedPremiseSortedTree
import Mettapedia.OSLF.Syntax.CartesianTreeLiftCriterion
import Mettapedia.OSLF.Syntax.ResultSortedScopedTreeLiftCriterion
import Mettapedia.GSLT.Examples.MixedPremiseTreeLiftCriterion
import Mettapedia.GSLT.Examples.ScopedExecutionSortingBoundary
import Mettapedia.GSLT.Examples.TypedRootProjectionWitness
import Mettapedia.GSLT.Examples.MixedPremiseAllNodesAdmission
import Mettapedia.GSLT.Examples.TypedPartialSpineCapture
import Mettapedia.GSLT.Examples.TypedPartialSpinePremise
import Mettapedia.GSLT.LanguageDef.TypedFullSpineStepResults
import Mettapedia.GSLT.Examples.TypedFullSpineLamCong
import Mettapedia.OSLF.Syntax.CanonicalScopedClassificationBoundary
import Mettapedia.GSLT.Examples.ScopedLamCongConstructorFrame
import Mettapedia.GSLT.Examples.ScopedRuleConstructorFrame
import Mettapedia.GSLT.Examples.ScopedLamCongStepShape
import Mettapedia.GSLT.Examples.ScopedLamCongPremiseSkeleton
import Mettapedia.GSLT.Examples.ScopedLamCongFreeModel
import Mettapedia.OSLF.MeTTaIL.OraclePremiseTransport
import Mettapedia.GSLT.Examples.ScopedLamCongOracleTransport
import Mettapedia.GSLT.Examples.OrderedPremiseOracleTransport
import Mettapedia.GSLT.Topos.PresheafPredicateHigherOrderControls
import Mettapedia.TypeTheory.PresheafCodomainFoundationControls
import Mettapedia.TypeTheory.PresheafEventSubstitution
import Mettapedia.OSLF.Syntax.DeterministicGSOSEdgeControls
import Mettapedia.OSLF.Syntax.DeterministicGSOSImageFiniteBoundary
import Mettapedia.OSLF.Syntax.DeterministicGSOSPresentationControls
import Mettapedia.OSLF.Syntax.BehavioralCorrespondence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionObservationBoundary
import Mettapedia.OSLF.Framework.FindingMindScopeClassification
import Mettapedia.OSLF.Framework.FindingMindGeneratedRhoCertificates
-- SpecIndex.lean imports Main (not vice versa) — no cycle

/-!
# Operational Semantics in Logical Form (OSLF)

Re-exports for the OSLF formalization, connecting MeTTaIL language definitions
to categorical semantics via the OSLF algorithm.

## Module Structure

```
OSLF/
├── Main.lean                -- This file (re-exports)
├── Framework/
│   ├── RewriteSystem.lean         -- Abstract OSLF: RewriteSystem -> OSLFTypeSystem
│   ├── RhoInstance.lean           -- ρ specialization of the canonical GSLT→OSLF construction
│   ├── DerivedModalities.lean     -- Derived ◇/□ from adjoint triple (0 sorries)
│   ├── CategoryBridge.lean        -- Categorical lift: GaloisConnection → Adjunction
│   ├── FULLStatus.lean            -- FULL-OSLF done/missing tracker
│   ├── TypeSynthesis.lean         -- LanguageDef → OSLFTypeSystem (auto Galois)
│   ├── GeneratedTyping.lean       -- Generated typing rules from grammar
│   ├── LambdaInstance.lean        -- Lambda calculus OSLF instance (2nd example)
│   ├── PetriNetInstance.lean      -- Petri net OSLF instance (3rd, binder-free)
│   ├── TinyMLInstance.lean        -- CBV λ-calculus + booleans/pairs/thunks (4th, multi-sort)
│   ├── MeTTaMinimalInstance.lean  -- MeTTa state client (eval/unify/chain/collapse/superpose/return)
│   ├── ConstructorCategory.lean   -- Sort quiver + free category from LanguageDef
│   ├── ConstructorFibration.lean  -- SubobjectFibration + ChangeOfBase over constructors
│   ├── ModalEquivalence.lean      -- Constructor change-of-base ↔ OSLF modalities
│   ├── DerivedTyping.lean         -- Generic typing rules from categorical structure
│   ├── PLNSelectorGSLT.lean       -- Core PLN selector rules as OSLF/GSLT rewrite system
│   └── BeckChevalleyOSLF.lean    -- Substitution ↔ change-of-base (Beck-Chevalley)
├── MeTTaIL/
│   ├── Syntax.lean          -- LanguageDef AST (types, terms, equations, rewrites)
│   ├── Semantics.lean       -- InterpObj, pattern interpretation
│   ├── Substitution.lean    -- Capture-avoiding substitution
│   ├── Match.lean           -- Generic pattern matching (multiset, locally nameless)
│   ├── Engine.lean          -- Root-rule and base-premise evaluators
│   ├── ContextualStep.lean  -- Least relation generated by authored contextual rules
│   └── MatchSpec.lean       -- Relational matching spec (proven ↔ executable)
├── Languages/ProcessCalculi/RhoCalculus/
│   ├── Types.lean           -- Namespaces, codespaces, bisimulation
│   ├── Reduction.lean       -- COMM with structural and parallel closure; raw modalities
│   ├── Soundness.lean       -- Substitutability, progress, type preservation
│   ├── StructuralCongruence.lean
│   ├── CommRule.lean
│   ├── SpiceRule.lean
│   ├── PresentMoment.lean
│   └── Engine.lean         -- Executable rewrite engine (reduceStep, proven sound)
├── Formula.lean             -- Formula AST + bounded model checker (proven sound)
└── NativeType/
    └── Construction.lean    -- NT as (sort, pred) pairs, type formation rules
```

## Architecture

The formalization has two layers:

### Abstract Layer (Framework/)
- `RewriteSystem`: sorts + terms + reduction (INPUT to OSLF)
- `OSLFTypeSystem`: predicates + Frame + diamond/box + Galois connection (OUTPUT)
- `NativeTypeOf`: native type = (sort, predicate) pair

### Concrete Layer (RhoCalculus/)
- `rhoReflectiveGSLT`: the closed, well-sorted, reflection-aware semantic
  object derived from `rhoCalc`
- `Reduces`: the paper-faithful Type-valued receipt relation retained below
  the propositionally truncated GSLT step
- `rhoOSLF`: the canonical GSLT→OSLF construction specialized to rho
- `HasType`: typing judgment with substitutability and progress

The rho specialization uses the same equation-invariant predicate frame and
modulo-equations reduction construction as every other GSLT.

## References

- Williams & Stay, "Native Type Theory" (ACT 2021)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF

-- Re-export MeTTaIL modules
export Mettapedia.OSLF.MeTTaIL.Syntax (
  CollType
  TypeExpr
  TermParam
  SyntaxItem
  GrammarRule
  Pattern
  FreshnessCondition
  Premise
  Equation
  RewriteRule
  LanguageDef
  rhoCalc
)

export Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended (
  rhoCalcExecExt
  rhoCalcSetExt
  rhoCalcExtended
  rhoCalcExtendedWithNativeFolds
)

export Mettapedia.OSLF.MeTTaIL.Semantics (
  InterpObj
  WellFormedLanguage
)

export Mettapedia.OSLF.MeTTaIL.Substitution (
  SubstEnv
  applySubst
  freeVars
  isFresh
  commSubst
)

export Mettapedia.OSLF.MeTTaIL.Match (
  matchPattern
  matchBag
  matchArgs
  applyBindings
  applyRule
  rewriteStep
)

export Mettapedia.OSLF.MeTTaIL.Engine (
  rewriteStepNoPremises
  RelationEnv
  premiseHoldsWithEnv
  premisesHoldWithEnv
  applyRuleWithPremisesUsing
  rewriteStepWithPremisesUsing
  premiseHolds
  premisesHold
  applyRuleWithPremises
  rewriteStepWithPremises
)

export Mettapedia.OSLF.MeTTaIL.ContextualStep (
  BasePremiseEvaluator
  engineBasePremises
  premiseStepUsing
  premisesUsing
  applyRuleUsing
  rewriteAt
  PremiseAt
  PremisesAt
  StepAt
  Step
  mem_rewriteAt_iff_stepAt
  NoncontextualPremises
  RootStep
  step_of_rule
  step_of_single_congruence_rule
  step_iff_rootStep_of_noncontextualRules
  exists_mem_rewriteAt_iff_step
)

export Mettapedia.OSLF.MeTTaIL.MatchSpec (
  MatchRel
  MatchArgsRel
  MatchBagRel
  matchPattern_sound
  matchArgs_sound
  matchBag_sound
  matchRel_complete
  matchArgsRel_complete
  matchBagRel_complete
  matchPattern_iff_matchRel
)

-- Re-export RhoCalculus modules
export Mettapedia.Languages.ProcessCalculi.RhoCalculus (
  ProcObj
  NameObj
  NamePred
  ProcPred
  BarbedParams
  BarbedRelation
  ProcEquiv
)

export Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness (
  NativeType
  TypingContext
  HasType
  substitutability
  comm_preserves_type
  quoteDropEmpty_irreducible
)

export Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction (
  Reduces
  ioCount
  ioCount_SC
  redWeight
  redWeight_SC
  redWeight_pos_of_reduces
  emptyBag_SC_irreducible
)

-- Re-export Engine module
export Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine (
  reduceStep
  reduceToNormalForm
  reduceAll
  emptyBag_reduceStep_nil
  reduceStep_sound
)

-- Re-export Framework modules
export Mettapedia.OSLF.Framework (
  RewriteSystem
  OSLFTypeSystem
  NativeTypeOf
  Substitutability
)

export Mettapedia.OSLF.Framework.RhoInstance (
  rhoGSLT
  rhoRewriteSystem
  rhoOSLF
  rhoGeneratedNTT
  rho_mathlib_galois
  rhoOSLF_sees_communication
  rhoGeneratedNTT_sees_communication
  rhoOSLF_keeps_freeDrop_inert
  rhoOSLF_cannot_distinguish_presentations
)

export Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho (
  presentedRhoQuotientEndpointRuntime
  presentedRhoCanonicalEquationNormalizer
  presentedRhoSuccessorClassEnumeration
  presentedRhoSuccessorClasses_exact
  presentedRhoNormalizedSuccessorClasses_exact
)

export Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory (
  InterpretedPresentation
)

export Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory.InterpretedPresentation (
  structural
  toGSLTUsing
  toRewriteSystemUsing
  toOSLFUsing
  NativeTypeUsing
  toOSLFUsing_eq_gsltOSLF
)

export Mettapedia.OSLF.Framework.GSLTTypeSynthesis (
  EquationInvariant
  EquationPredicate
  gsltRewriteSystem
  gsltSpan
  semanticDiamond
  semanticBox
  semanticGalois
  gsltOSLF
  GSLTNativeType
)

export Mettapedia.OSLF.Framework.DerivedModalities (
  ReductionSpan
  derivedDiamond
  derivedBox
  derived_galois
)

export Mettapedia.OSLF.Framework.ToposReduction (
  InternalReductionGraph
  ReductionGraphObj
  patternConstPresheaf
  pairConstPresheaf
  reductionSubfunctorUsing
  reductionSubfunctor
  reductionSourceUsing
  reductionTargetUsing
  reductionGraphUsing
  reductionGraph
  reductionGraphObjUsing
  reductionGraphObj
  mem_reductionSubfunctorUsing_iff
  reductionGraphUsing_edge_endpoints_iff
  langDiamondUsing_iff_exists_graphStep
  langBoxUsing_iff_forall_graphIncoming
  langDiamondUsing_iff_exists_graphObjStep
  langBoxUsing_iff_forall_graphObjIncoming
  langDiamondUsing_iff_exists_internalStep
  langBoxUsing_iff_forall_internalStep
  langDiamond_iff_exists_graphStep
  langBox_iff_forall_graphIncoming
  langDiamond_iff_exists_internalStep
  langBox_iff_forall_internalStep
  exec_mem_reductionSubfunctorUsing
  reductionSubfunctorUsing_mem_decomposes
)

export Mettapedia.OSLF.Framework.GeneratedTyping (
  GenNativeType
  GenTypingContext
  GenHasType
  topPred
)

export Mettapedia.OSLF.Framework.CategoryBridge (
  langDiamond_monotone
  langBox_monotone
  PredLattice
  langGaloisL
  langModalAdjunction
  rhoModalAdjunction
  SortCategoryInterface
  defaultSortCategoryInterface
  lambdaTheorySortInterface
  typeSortsRewriteSystem
  typeSortsLambdaTheory
  typeSortsLambdaInterface
  SortCategory
  SortPresheafCategory
  predFibrationSortApprox
  predFibrationUsing
  predFibration
  predFibration_presheafSortApprox_agreement
  oslf_fibrationSortApprox
  oslf_fibrationUsing
  oslf_fibration
  typeSortsPredFibrationViaLambdaInterface
  langOSLFFiberFamily
  langOSLFFibrationUsing_presheafAgreement
  rhoLangOSLFFiberFamily
  rhoLangOSLFFibrationUsing_presheafAgreement
  languagePresheafObj
  languagePresheafLambdaTheory
  languageSortRepresentableObj
  languageSortFiber
  languageSortPredNaturality
  commDiPred
  commDiWitnessLifting
  PathSemClosedPred
  CommDiPathSemLiftPkg
  commDiPathSemLiftPkg_of_liftEq
  commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
  commDiWitnessLifting_of_pathSemLiftPkg
  languageSortPredNaturality_commDi_pathSemClosed_of_pkg
  pathSem_commSubst
  pathSemClosedPred_closed
  languageSortPredNaturality_commDi
  commDiWitnessLifting_of_pathSemClosed
  languageSortPredNaturality_commDi_pathSemClosed
  commDiWitnessLifting_of_lift
  commDiWitnessLifting_of_pathSemLift
  languageSortFiber_ofPatternPred
  languageSortFiber_ofPatternPred_map_mem
  languageSortFiber_ofPatternPred_subobject
  languageSortFiber_ofPatternPred_characteristicMap
  languageSortFiber_ofPatternPred_characteristicMap_spec
  languageSortFiber_ofPatternPred_mem_iff
  languageSortFiber_ofPatternPred_mem_iff_satisfies
  rhoProc_langOSLF_predicate_to_fiber_mem_iff
  rho_proc_pathSemLift_pkg
  rho_proc_commDiWitnessLifting_of_pkg
  rhoProcOSLFUsingPred
  rhoProcOSLFUsingPred_to_languageSortFiber
  rhoProcOSLFUsingPred_to_languageSortFiber_mem_iff
  languageSortFiber_characteristicEquiv
  languageSortPredicateFibration
  rhoProcRepresentableObj
  rhoProcSortFiber
  rhoProcSortFiber_characteristicEquiv
  rhoSortPredicateFibration
)

export Mettapedia.OSLF.Framework.LangMorphism (
  LangReducesStar
  TargetSC
  LanguageMorphism
  idLanguageMorphism
  composeLanguageMorphism
  LanguageMorphism.forward_multi_eq
  LanguageMorphism.backward_multi_eq
  LanguageMorphism.preserves_diamond
  LanguageMorphism.operational_correspondence_forward
)

export Mettapedia.OSLF.Framework.LanguageEqCategory (
  Obj
  Hom
  id
  comp
  HomEq
  mapPred
  mapPred_comp_fn
)

export Mettapedia.OSLF.Framework.LanguageEqCategoryLaws (
  EqCategoryLaws
  languageEqCategoryLaws
  left_id_holds
  right_id_holds
  assoc_holds
  mapPred_id_holds
  mapPred_comp_holds
)

export Mettapedia.OSLF.Framework.ModeTheory (
  RuntimeBehavioralIndexedDoctrine
  mettaILRuntimeBehavioralDoctrine
  doctrine_modalAdjunction_eq
  doctrine_galois_eq
  doctrine_fiberAgreement
  doctrine_morphism_preserves_diamond
)

export Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor (
  LanguageEqHom
  predPullback
  IndexedPredFunctor
  runtimePredicatePullbackFunctor
  diamond_witness_transport
  diamond_witness_transport_comp
  ModalTranslation
  ModallyCoveredTheory
  forgetIncoming
  ModalPredicateTheory
  oslfModalObject
  oslfModalObject_agrees_gsltOSLF
  oslfModalFunctor
  ReifiedNativeTheory
  NativeTypeEssentialImage
  nativeType_obj_mem_essentialImage
  reifiedOSLF
  reifiedOSLF_obj_mem_essentialImage
  OSLFComparison
  EffectiveStructure.StepDecision
  EffectiveStructure.EquationDecision
  EffectiveStructure.SuccessorEnumeration
  EffectiveStructure.SuccessorClassEnumeration
  EffectiveStructure.PredecessorEnumeration
  EffectiveStructure.CanonicalEquationNormalizer
  EffectiveStructure.QuotientEndpointRuntime
  EffectiveStructure.ReductionNormalizer
  EffectiveStructure.ContextualClosure
  EffectiveStructure.SubstitutionClosure
  EffectiveStructure.ProofRelevantRequirement
)

export Mettapedia.OSLF.Framework.IndexedModalFunctor (
  ForwardModalPredicateTheory
  oslfForwardModalObject
  oslfForwardModalFunctor
  forgetExactModal
  forwardIndexedOSLF
  exactIndexedOSLF
  forwardIndexedOSLFFunctor
  exactIndexedOSLFFunctor
  modal_pullback_diamond_exact
  modal_pullback_box_exact
)

export Mettapedia.OSLF.Framework.Mode2Skeleton (
  ModeObj
  ModeHom
  runtimeToBehavioralCanonical
  runtimeToBehavioral_diamond_witness
  behavioralModalAdjunction
)

export Mettapedia.OSLF.Framework.Mode2PureBoundary (
  no_pure_to_runtime
  no_pure_to_behavioral
  no_runtime_to_pure
  no_behavioral_to_pure
  pure_endo_unique
  pure_boundary_characterization
  twoSortDependentRuntimeObj
  twoSortDependentBehavioralObj
  twoSortDependentRuntimeToBehavioral
  twoSortDependent_runtime_behavioral_diamond_transport
)

export Mettapedia.OSLF.Framework.Mode2SkeletonLaws (
  ModeHomLaws
  mode2SkeletonLaws
  left_id_holds
  right_id_holds
  assoc_holds
  mapPred_id_holds
  mapPred_comp_holds
)

export Mettapedia.OSLF.Framework.ModeMapPredCommutingSquares (
  runtime_runtime_square
  runtime_runtime_square_comp
  runtime_behavioral_square
  runtime_behavioral_square_comp
  mapPred_commuting_squares_bundle
)

export Mettapedia.OSLF.Framework.MATTProvableNow (
  doctrine_galois_is_langGalois
  doctrine_adjunction_is_langModalAdjunction
  eqCategory_mapPred_functorial
  eqCategory_law_bundle_agrees
  runtime_mode_mapPred_agrees
  runtime_mode_termMap_agrees
  runtime_mode_comp_coherence
  runtime_runtime_square_coherence
  runtime_behavioral_square_coherence
  runtime_mode_diamond_transport
  runtime_mode_diamond_transport_comp
  pure_mode_isolation
  twoSortDependent_runtime_behavioral_transport
  matt_provable_now_bundle
  matt_provable_now_bundle_ext
  matt_provable_now_bundle_transport
)

export Mettapedia.OSLF.Framework.MATTClaimMap (
  MATTClaimStatus
  MATTClaim
  mattClaimList
  countByStatus
  provenCount_eq
  outOfScopeCount_eq
  matt_pure_boundary_package
  matt_canonical_runtime_behavioral_package
)

export Mettapedia.OSLF.Framework.FULLStatus (
  MilestoneStatus
  Milestone
  tracker
  countBy
  remaining
  remainingCount
)

export Mettapedia.OSLF.Framework.LambdaInstance (
  lambdaCalc
  lambdaOSLF
  lambdaGalois
)

export Mettapedia.OSLF.Framework.PetriNetInstance (
  petriNet
  petriNet_validate
  validatedPetriNet
  petriOSLF
  petriGalois
  petriDCNativeType
  petriGeneratedNTT
  petriNet_BA_semanticStep_DC
  petriNet_BA_not_rawStep_DC
  petriNet_BA_satisfies_DC_nativeType
  petriGeneratedNTT_accepts_BA_to_DC
)

export Mettapedia.OSLF.Framework.TinyMLInstance (
  tinyML
  tinyMLOSLF
  tinyMLGalois
  tinyML_crossings
  tinyExprObj
  tinyValObj
  injectArrow
  thunkArrow
  injectMor
  thunkMor
  inject_di_pb_adj
  thunk_di_pb_adj
  thunk_is_quoting
  inject_is_reflecting
  thunk_action_eq_diamond
  inject_action_eq_box
  tinyML_typing_action_galois
  tinyML_commDiPathSemLiftPkg_of_liftEq
  tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph
  tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
)

export Mettapedia.OSLF.Framework.MeTTaMinimalInstance (
  mettaMinimal
  mettaMinimalOSLF
  mettaMinimalGalois
  mettaState
  mettaMinimal_pathOrder
  mettaMinimal_commDiPathSemLiftPkg_of_liftEq
  mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph
  mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
  mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  mettaSpecAtomCheck
  mettaSpecAtomSem
  mettaMinimal_checkLangUsing_sat_sound_specAtoms
  mettaMinimal_checkLang_sat_sound_specAtoms
)

export Mettapedia.Languages.MeTTa.OSLFCore.Premises (
  space0Atomspace
  space0EqEntries
  space0TypeEntries
  space0Entries
  mkCanonicalSpace
  space0Pattern
  spaceEntriesOfPattern?
  atomspaceOfPattern?
  eqnLookupTuples
  noEqnLookupTuples
  neqTuples
  typeOfTuples
  notTypeOfTuples
  castTuples
  notCastTuples
  groundedCallTuples
  noGroundedCallTuples
)

export Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef (
  mettaFullLegacy
  mettaFullLegacyOSLF
  mettaFullLegacyGalois
  mettaFullLegacyRelEnv
  mettaFull
  mettaFullOSLF
  mettaFullGalois
  mettaFullRelEnv
)

export Mettapedia.OSLF.Framework.MeTTaFullInstance (
  mettaFullLegacy_pathOrder
  mettaFullLegacy_checker_sat_to_pathSemClosed_commDi_bc_graph
  mettaFullLegacy_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  mettaFullLegacySpecAtomCheck
  mettaFullLegacySpecAtomSem
  mettaFullLegacy_checkLangUsing_sat_sound_specAtoms
  mettaFullLegacy_checkLang_sat_sound_specAtoms
  mettaFull_pathOrder
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  mettaFullSpecAtomCheck
  mettaFullSpecAtomSem
  mettaFull_checkLangUsing_sat_sound_specAtoms
  mettaFull_checkLang_sat_sound_specAtoms
)

export Mettapedia.OSLF.Framework.MeTTaToNTT (
  mettaEvidenceToNT
  mettaEvidenceToNT_hom
  mettaSemE
  mettaSemE_atom
  mettaSemE_atom_revision
  mettaFormulaToNT
  mettaFormulaToNT_snd
  mettaFormulaToNT_atom
  mettaFormulaToNT_hom
)

export Mettapedia.OSLF.Framework.OSLFNTTWMBridge (
  oslf_atom_ntt_wm_triangle
  oslf_atom_ntt_wm_triangle_categorical
  oslf_formula_ntt_evidence_component
  oslf_dia_formula_graph_witness_transport
  oslf_dia_formula_ntt_graph_witness_transport
  oslf_formula_ntt_graph_triangle
  oslf_formula_ntt_graph_triangle_categorical
)

export Mettapedia.OSLF.Framework.ModalSubobjectBridge (
  modalFiberOfPatternPred
  modalSubobjectOfPatternPred
  modalSubobjectAsFiber
  modalSubobjectAsFiber_eq_modalFiber
  modalFiber_mem_iff
  modalSubobject_mem_iff
  modalFiber_map_mem
  modalSubobject_subst_map_mem
  modalSubobject_commDi_beckChevalley_of_pathSemLiftPkg
  modalSubobject_commDi_bc_graph_endpoint_of_pathSemLiftPkg
  mettaFullLegacy_modalSubobject_commDi_bc_graph_endpoint
  mettaFull_modalSubobject_commDi_bc_graph_endpoint
)

export Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure (
  oslf_ntt_wm_step_sound
  oslf_ntt_wm_star_sound
)

export Mettapedia.OSLF.Framework.ConstructorCategory (
  LangSort
  baseSortOf
  unaryCrossings
  SortArrow
  SortPath
  ConstructorObj
  constructorCategory
  arrowSem
  pathSem
  pathSem_comp
  liftFunctor
  lift_map_unique
)

export Mettapedia.OSLF.Framework.ConstructorFibration (
  constructorFibration
  constructorPullback
  constructorDirectImage
  constructorUniversalImage
  constructorChangeOfBase
)

export Mettapedia.OSLF.Framework.ModalEquivalence (
  nquoteTypingAction
  pdropTypingAction
  typing_action_galois
  diamondAction
  boxAction
  action_galois
)

export Mettapedia.OSLF.Framework.DerivedTyping (
  ConstructorRole
  classifyArrow
  typingAction
  DerivedHasType
  nquote_is_quoting
  pdrop_is_reflecting
  nquote_action_eq_diamond
  pdrop_action_eq_box
)

export Mettapedia.OSLF.Framework.PLNSelectorGSLT (
  PLNSelectorSort
  PLNSelectorExpr
  PLNSelectorExpr.Reduces
  PLNSelectorExpr.reduces_sound_strength
  PLNSelectorExpr.rtc_reduces_sound_strength
  plnSelectorRewriteSystem
  plnSelectorOSLF
  oslf_diamond_extBayes2
  oslf_diamond_extBayesFamily
  oslf_diamond_stagedFamily_roundtrip
  oslf_box_stagedFamily_roundtrip
)

export Mettapedia.OSLF.Framework.PLNSelectorLanguageDef (
  plnSelectorLanguageDef
  NormalizeFiniteNonzero
  EncodeInjective
  plnSelector_checkLangUsing_sat_sound
  plnSelector_checkLangUsing_sat_sound_graph
)

export Mettapedia.OSLF.Framework.BeckChevalleyOSLF (
  presheafPrimary_beckChevalley_transport
  presheaf_beckChevalley_square_direct
  representable_patternPred_beckChevalley
  representable_commDi_patternPred_beckChevalley
  representable_commDi_patternPred_beckChevalley_of_lifting
  representable_commDi_patternPred_beckChevalley_of_pathSemLift
  representable_commDi_patternPred_beckChevalley_of_pathSemClosed
  representable_commDi_patternPred_beckChevalley_of_pathSemLiftPkg
  representable_commDi_bc_and_graphDiamond
  representable_commDi_bc_and_graphDiamond_of_lifting
  representable_commDi_bc_and_graphDiamond_of_pathSemLift
  representable_commDi_bc_and_graphDiamond_of_pathSemClosed
  representable_commDi_bc_and_graphDiamond_of_pathSemLiftPkg
  rhoProc_commDi_bc_and_graphDiamond_of_pathSemLift_pkg
  langDiamondUsing_graph_transport
  langBoxUsing_graph_transport
  commDi_diamond_graph_step_iff
  commDi_diamond_graphObj_square
  commDi_diamond_graphObj_square_direct
  galoisConnection_comp
  commMap
  commPb
  commDi
  commUi
  comm_di_pb_adj
  comm_pb_ui_adj
  diamond_commDi_galois
  commDi_diamond_galois
  typedAt
  substitutability_pb
  substitutability_di
  comm_beck_chevalley
  commSubst_eq_open_constructorSem
  strong_bc_fails
)

-- Re-export Formula module (OSLF output artifact)
export Mettapedia.OSLF.Formula (
  OSLFFormula
  sem
  sem_dia_eq_langDiamondUsing
  sem_dia_eq_graphStepUsing
  sem_box_eq_graphIncomingUsing
  sem_box_eq_graphObjIncomingUsing
  sem_box_eq_graphIncoming
  sem_dia_eq_langDiamond
  sem_box_eq_langBoxUsing
  sem_box_eq_langBox
  formula_galoisUsing
  formula_galois
  rhoCalc_SC_empty_sem_diaTop_unsat_reduceStep
  CheckResult
  check
  checkLangUsing
  checkLang
  check_sat_sound
  checkLangUsing_sat_sound
  checkLangUsing_sat_sound_sort_fiber
  checkLangUsing_sat_sound_sort_fiber_mem_iff
  checkLangUsing_sat_sound_proc_fiber
  checkLang_sat_sound_proc_fiber
  checkLangUsing_sat_sound_graph
  checkLangUsing_sat_sound_graph_box
  checkLang_sat_sound
  aggregateBox
  aggregateBox_sat
  checkWithPred
  checkWithPred_sat_sound
  checkLangUsingWithPred
  checkLangWithPred
  checkLangUsingWithPred_sat_sound
  checkLangUsingWithPred_sat_sound_graph_box
  checkLangUsingWithPred_sat_sound_graphObj_dia
  checkLangUsingWithPred_sat_sound_graphObj_box
  checkLangWithPred_sat_sound
  rhoAtoms
  rhoAtomSem
  rhoAtoms_sound
)

end Mettapedia.OSLF
