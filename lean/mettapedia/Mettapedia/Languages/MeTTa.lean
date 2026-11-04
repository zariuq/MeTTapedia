import Mettapedia.Languages.MeTTa.GuardedAtomRuleBoundary
import Mettapedia.Languages.MeTTa.HE
import Mettapedia.Languages.MeTTa.OSLFCore
import Mettapedia.Languages.MeTTa.MeTTaZero
import Mettapedia.Languages.MeTTa.MeTTaZeroAnswerAlgebra
import Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
import Mettapedia.Languages.MeTTa.SpaceQueryPolicy
import Mettapedia.Languages.MeTTa.SpaceKinds
import Mettapedia.Languages.MeTTa.SpaceKindContracts
import Mettapedia.Languages.MeTTa.SpaceKindRefinement
import Mettapedia.Languages.MeTTa.SpaceKindSupportBridge
import Mettapedia.Languages.MeTTa.SpaceValues
import Mettapedia.Languages.MeTTa.SpaceContainers
import Mettapedia.Languages.MeTTa.TensorSpaces
import Mettapedia.Languages.MeTTa.SpaceDeltas
import Mettapedia.Languages.MeTTa.SpaceSinks
import Mettapedia.Languages.MeTTa.StreamableSinks
import Mettapedia.Languages.MeTTa.TransformQuantifiers
import Mettapedia.Languages.MeTTa.TransformComposition
import Mettapedia.Languages.MeTTa.TransformRemovalInstances
import Mettapedia.Languages.MeTTa.CollectionPatternQuery
import Mettapedia.Languages.MeTTa.CollectionValueBridges
import Mettapedia.Languages.MeTTa.LayerEffects
import Mettapedia.Languages.MeTTa.AnnotationCapabilities
import Mettapedia.Languages.MeTTa.SpecRunObserver
import Mettapedia.Languages.MeTTa.MeTTaZeroWorkClosure
import Mettapedia.Languages.MeTTa.MeTTaZeroTransformEvaluation
import Mettapedia.Languages.MeTTa.MeTTaZeroUV
import Mettapedia.Languages.MeTTa.MeTTaInteraction
import Mettapedia.Languages.MeTTa.MeTTaInteractionBind
import Mettapedia.Languages.MeTTa.MeTTaInteractionResources
import Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
import Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution
import Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEvalCollapse
import Mettapedia.Languages.MeTTa.StigmergicSpace
import Mettapedia.Logic.Query.Coverage
import Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire
import Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
import Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy
import Mettapedia.Languages.MeTTa.MeTTaZeroNativeKernel
import Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel
import Mettapedia.Languages.MeTTa.MeTTaZeroHornFragment
import Mettapedia.Languages.MeTTa.MeTTaZeroCertifiedPlanning
import Mettapedia.Languages.MeTTa.PeTTa
import Mettapedia.Languages.MeTTa.PeTTa.TypingResearch
import Mettapedia.Languages.MeTTa.PLeaTTa
import Mettapedia.Languages.MeTTa.CoreProfile
import Mettapedia.Languages.MeTTa.DialectProfile
import Mettapedia.Languages.MeTTa.RuntimeSpec
import Mettapedia.Languages.MeTTa.DialectProjectionBoundary
import Mettapedia.Machines.DeterministicTail
import Mettapedia.Machines.FinitePullProducer
import Mettapedia.Logic.Unification.BinaryPatternViews
import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.MeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.SearchPolicyContract
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.CheckingService
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.CompleteDevelopment
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.TypedCompleteDevelopment
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.BidirectionalChecking
import Mettapedia.Languages.MeTTa.ElaboratedCore
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.HOLLogicalInductionBridge
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PresentationBoundary
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PresentationTypingBridge
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Structural
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.DefEq
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.NormalizationBoundary
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.NormalizationAlgorithm
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Reducibility
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.KripkeCandidates
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.CandidateSemantics
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.CandidateCoherence
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.HeadExpansion
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.ContextualCandidates
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.ContextualPi
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.ContextualSigma
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.AccessibleConversion
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.ContextualIdentity
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SemanticUniverse
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SemanticCoherence
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Fundamental
import Mettapedia.TypeTheory.UniverseLevel.Algebra
import Mettapedia.Languages.MeTTa.AbstractMachineBoundary
import Mettapedia.Languages.MeTTa.CeTTaSpaceEngineRefinement
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.HEFragmentBridge
import Mettapedia.Languages.MeTTa.DTTSeedProofPath
import Mettapedia.Languages.MeTTa.DTTTutorialStatus
import Mettapedia.Languages.MeTTa.Experimental.NoValueZoo
import Mettapedia.Languages.MeTTa.Experimental.NullDesigns
import Mettapedia.Logic.Query.MultisetAscription
import Mettapedia.TypeTheory.Calculi.StagedScopedReflective.SuperpositionOccurrencePressure
import Mettapedia.GSLT.LanguageDef.ScopedProofIrrelevance
import Mettapedia.GSLT.LanguageDef.IdentityComputationCalibration
import Mettapedia.Machines.BranchLocalNeed.Worlds
import Mettapedia.Machines.BranchLocalNeed.InferenceControl
import Mettapedia.Machines.BranchLocalNeed.ProtocolBridge
import Mettapedia.Machines.BranchLocalNeed.InteractionAuthority
import Mettapedia.Machines.BranchLocalNeed.InteractionValuation
import Mettapedia.Machines.DemandBoundary
import Mettapedia.Languages.FiniteChoice.FrontierAlgebra
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra
import Mettapedia.Languages.MeTTa.SequenceProjection
import Mettapedia.Languages.MeTTa.EquationKernel
import Mettapedia.Languages.MeTTa.Seal
import Mettapedia.Languages.MeTTa.MetavariableFrame
import Mettapedia.Languages.MeTTa.MetavariableFrameStore
import Mettapedia.Languages.MeTTa.MetavariableFrameStoreEscape
import Mettapedia.Languages.MeTTa.MetavariableFrameLineage
import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
import Mettapedia.Languages.MeTTa.MetavariableFrameStoreGrowth
import Mettapedia.Languages.MeTTa.MetavariableFrameReclamation
import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaNeedHistory
import Mettapedia.Languages.MeTTa.FreshFrameOccursCheck
import Mettapedia.Languages.MeTTa.PatternSelection
import Mettapedia.Languages.MeTTa.AnswerProducerHandoff
import Mettapedia.Languages.MeTTa.SpecializerRelevance
import Mettapedia.Languages.MeTTa.UndeclaredOperandType
import Mettapedia.Languages.MeTTa.GroundClosureSharing
import Mettapedia.Languages.MeTTa.BindingVersions
import Mettapedia.Data.List.OrderedOccurrenceCursor
import Mettapedia.Languages.MeTTa.SearchStateStack
import Mettapedia.Languages.MeTTa.TermView
import Mettapedia.Languages.FiniteChoice.SpaceExtensionality
import Mettapedia.Languages.FiniteChoice.UltrainfiniteRetractionInstance
import Mettapedia.Languages.FiniteChoice.UniversalObservers
import Mettapedia.Languages.FiniteChoice.ZeroObserverExpressibility
import Mettapedia.Languages.FiniteChoice.ObserverFamilies
import Mettapedia.Languages.FiniteChoice.OrderObservability
import Mettapedia.Languages.FiniteChoice.WeakestAdequate
import Mettapedia.Languages.FiniteChoice.ObserverLattice
import Mettapedia.Languages.FiniteChoice.UnitAndChoiceZero
import Mettapedia.Languages.FiniteChoice.CollapseSuperposeRoundTrip
import Mettapedia.Languages.FiniteChoice.EmptinessTaxonomy
import Mettapedia.GSLT.Dynamics.SourceFallback
import Mettapedia.Languages.LazyArithPair.Semantics
import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.Machines.BranchLocalNeed.DependentService
import Mettapedia.OSLF.Framework.CandidateDependentWorldModel
import Mettapedia.Languages.MeTTa.HE.HOLContract.Guest
import Mettapedia.Languages.MeTTa.HE.HOLContract.Backend
import Mettapedia.Languages.MeTTa.HE.HOLContract.BackendRoutes
import Mettapedia.Languages.MeTTa.EvaluationControl.ArgumentModes
import Mettapedia.Languages.MeTTa.EvaluationControl.SequencingForms

/-!

# MeTTa Language Formalizations

This aggregate collects source profiles and separate experimental adapters.
`Mettapedia.Languages.GuardedAtomRule.Evidence` owns the separate guarded
atom-rule calculus;
its source judgments and dependency closure are available through that owner
without importing this aggregate.

## Variants
- `HE` - Hyperon Experimental MeTTa (authoritative HE spec)
- `Core` - MeTTa core state machine and language definition
- `PeTTa` - Prolog-based MeTTa profile

## Bridges
- `HE.HOLContract.Guest` - the HOL contract of HE's type declarations and the
  hosted HOL Light checker
- `HE.HOLContract.Backend` - replaceable backends of the contract
- `HE.HOLContract.BackendRoutes` - admitted backends as conservative routes: every client
  borrows the same theory through each of them
-/
