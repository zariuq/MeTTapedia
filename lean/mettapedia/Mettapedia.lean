import Mettapedia.Languages.FiniteChoice
import Mettapedia.TypeTheory.Models.RevisionedFamilies
import Mettapedia.Languages.LazyArithPair.Semantics
import Mettapedia.Logic.ProofSearch
import Mettapedia.Logic.Function.EventualStability
import Mettapedia.Machines.DeterministicTail
import Mettapedia.Machines.FinitePullProducer
import Mettapedia.Data.List.OrderedOccurrenceCursor
import Mettapedia.Logic.Unification.BinaryPatternViews
import Mettapedia.GSLT.Core.OrderedQueryCompilation
import Mettapedia.GSLT.LanguageDef.GroundDenseQueryCompilation
import Mettapedia.Logic.Query.Coverage
import Mettapedia.Logic.Query.MultisetAscription
import Mettapedia.OSLF.Framework.ReductionViewIndexedModalities
import Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory
import Mettapedia.TypeTheory.CompositionalRelationLifting
/-
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

# Mettapedia - Encyclopedia of Formalized Mathematics

A comprehensive formalization of mathematics across multiple domains,
inspired by Wikipedia's breadth and Metamath's rigor.

## Project Structure

- **GraphTheory/**: Graph theory (Bondy & Murty, Diestel)
- **ProbabilityTheory/**: Probability theory (Kolmogorov, Billingsley, Durrett)
- **SetTheory/**: Set theory foundations
- **Combinatorics/**: Combinatorial mathematics
- **NumberTheory/**: Number theory
- **Topology/**: Topological spaces
- **Algebra/**: Algebraic structures
- **Logic/**: Mathematical logic
- **Analysis/**: Real and complex analysis

## Tools

- **LeanHammer**: ATP integration (Zipperposition prover)
- **Mathlib**: Lean's standard math library

-/

-- Graph Theory: Mathlib-facing declarative foundations and proved
-- Hamiltonicity degree conditions.
import Mettapedia.GraphTheory.Basic
import Mettapedia.GraphTheory.Hamiltonicity
import Mettapedia.GraphTheory.Representation
import Mettapedia.GraphTheory.Walk

-- Probability Theory
import Mettapedia.ProbabilityTheory.Basic
import Mettapedia.ProbabilityTheory.Moments
import Mettapedia.ProbabilityTheory.Exchangeability
import Mettapedia.ProbabilityTheory.Cox
import Mettapedia.ProbabilityTheory.ImpreciseProbability
import KnuthSkilling
import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling
import Mettapedia.ProbabilityTheory.OptimalTransport

-- Probability Theory: outside-closure cluster promoted to the verified core at
-- Lean 4.31.  Each module below compiles cleanly, is genuinely `sorry`-free, and
-- is axiom-clean (`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}).
-- (Modules in this cluster with genuine 4.31 proof-level breakage are NOT imported
--  anywhere yet — they stay outside-closure pending repair; they cannot enter the
--  WIP tier either, since that tier must still compile error-free.)
import Mettapedia.ProbabilityTheory.CommonFoundations
import Mettapedia.ProbabilityTheory.Common.CombinationRule
import Mettapedia.ProbabilityTheory.Common.Lattice
import Mettapedia.ProbabilityTheory.Common.LatticeSummation
import Mettapedia.ProbabilityTheory.Structures.Valuation.Basic
import Mettapedia.ProbabilityTheory.Foundations.Distributions.ProbDist
import Mettapedia.ProbabilityTheory.MeasureBridge
import Mettapedia.ProbabilityTheory.Unified
import Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingSchedule
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingLiterature
import Mettapedia.ProbabilityTheory.FreeProbability.NoncrossingPartitions
import Mettapedia.ProbabilityTheory.HigherOrderProbability.GiryMonad
import Mettapedia.ProbabilityTheory.HigherOrderProbability.KyburgFlattening
import Mettapedia.ProbabilityTheory.QuantumProbability
import Mettapedia.ProbabilityTheory.Hypercube.CentralQuestionCounterexample
import Mettapedia.ProbabilityTheory.Hypercube.Examples
import Mettapedia.ProbabilityTheory.Hypercube.NovelTheories
import Mettapedia.ProbabilityTheory.Hypercube.OperationalSemantics
import Mettapedia.ProbabilityTheory.Hypercube.PLNEvidencePointer
import Mettapedia.ProbabilityTheory.Hypercube.StayWellsConstruction
import Mettapedia.ProbabilityTheory.Hypercube.UnifiedTheory

-- Previously-held-back ProbabilityTheory cluster, repaired in place for Lean 4.31 and
-- now folded in.  The breakage was the mechanical transparency set: `simp`/`simpa`
-- run at `.reducible` since 4.31 (→ projection/synonym-defeq mismatches closed with
-- `simpa … using!`, term/`show` mode, or explicit `rw`-in-hypothesis), `def`s no longer
-- unfolding for anonymous constructors, plus mathlib renames (`Finset.not_mem_empty`→
-- `notMem_empty`, `Finset.sum_eq_add_sum_diff_singleton`→`…sum_eq_add_sum_sdiff_singleton_of_mem`,
-- `HasCompl`→`Compl`), the ambient zero-argument `zero_le` (→ `bot_le`), the flipped
-- `add_lt_add_left/right` convention (→ `gcongr`), and `_root_.`-qualifying the
-- KnuthSkilling-external `FactorGraph`/`Valuation` in the `KSFactorGraph` bridge.
-- The three aggregators pull in the whole repaired Bayesian-network / belief-function /
-- hypercube-semantics subtrees transitively.
import Mettapedia.ProbabilityTheory.AssociativityTheorem
import Mettapedia.ProbabilityTheory.BayesianNetworks
import Mettapedia.ProbabilityTheory.BeliefFunctions
import Mettapedia.ProbabilityTheory.Hypercube
import Mettapedia.ProbabilityTheory.UnifiedProbabilityBridge

-- Measure Theory
import Mettapedia.MeasureTheory.FromSymmetry
import Mettapedia.MeasureTheory.Integration

-- Quantum Theory
import Mettapedia.QuantumTheory.FromSymmetry

-- Algebra
import Mettapedia.Algebra.PrimeDecomposition
import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.Algebra.TemporalQuantale

-- Category Theory (Hypercube/OSLF framework for quantales)
import Mettapedia.CategoryTheory.FuzzyFrame
import Mettapedia.CategoryTheory.LambdaTheory
import Mettapedia.CategoryTheory.PLNInstance
import Mettapedia.PLN.Bridges.CategoryTheory.EvidenceFibration
import Mettapedia.CategoryTheory.PLNTerms
import Mettapedia.CategoryTheory.ModalTypes
import Mettapedia.CategoryTheory.Hypercube
import Mettapedia.CategoryTheory.PLNSemiringQuantale
import Mettapedia.CategoryTheory.GeneralizedOpenMaps

-- Information theory (combinatorial bounds)
import Mettapedia.InformationTheory.BinomialEntropy

-- Machine learning
import Mettapedia.MachineLearning

-- Computability
import Mettapedia.Computability.KolmogorovComplexity.Basic
-- import Mettapedia.Computability.KolmogorovComplexity.Prefix  -- WIP (Phase 2)

-- Arithmetical Hierarchy (Grain of Truth - Phase 1)
import Mettapedia.Computability.ArithmeticalHierarchy.Basic
import Mettapedia.Computability.ArithmeticalHierarchy.Closure
import Mettapedia.Computability.ArithmeticalHierarchy.PolicyEncoding
import Mettapedia.Computability.ArithmeticalHierarchy.PolicyClasses

-- OSLF (Operational Semantics of Lambda-based Formalisms)
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PresentMoment
-- Derived replication/restriction operational layer.  Repaired for the Lean
-- 4.31 `simp`/`dsimp`-at-`.reducible` transparency change (`simpa using! h` for
-- defeq-but-not-reducibly-equal match/`congrFun` closers; the `CoreCanonical`
-- conservativity bridge — `CoreCanonical p := hasDerivedHead p = false` — closed
-- by `subst; exact` instead of relying on `simp` to unfold the plain `def`).
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

-- Taxonomy migration ledger
import Mettapedia.TaxonomyMigrationLedger

-- Knowledge representation
import Mettapedia.KR

-- Logic
import Mettapedia.Logic.Relation.Normalization
import Mettapedia.Logic.Relation.NormalizationExamples
import Mettapedia.Logic.Relation.PathConfluence
import Mettapedia.Logic.Relation.PathConfluenceExamples
import Mettapedia.Logic.Relation.DecodedPath
import Mettapedia.Logic.WorldModel
import Mettapedia.Logic.MarkovLogicIndividuationBridge
import Mettapedia.Logic.GunkyMereology
import Mettapedia.Logic.StoneGunkDuality
import Mettapedia.Logic.Metaphysics
import Mettapedia.Logic.LawsOfForm
import Mettapedia.UniversalAI.SolomonoffPrior
import Mettapedia.UniversalAI.UniversalMachineBoundary
import Mettapedia.UniversalAI.IncrementalCompressionBridge
import Mettapedia.UniversalAI.OpenEndedCompressionBridge
import Mettapedia.Computability.KolmogorovComplexity.KraftChaitinStream
import Mettapedia.Computability.KolmogorovComplexity.KraftChaitinEffective
import Mettapedia.Computability.KolmogorovComplexity.SaturatedKraftChaitin
import Mettapedia.Computability.KolmogorovComplexity.DyadicThresholdCoding
import Mettapedia.Computability.KolmogorovComplexity.DiscreteSemimeasureCoding
import Mettapedia.Computability.KolmogorovComplexity.ConditionalOutputSemimeasure
import Mettapedia.Computability.KolmogorovComplexity.ConditionalLowerChainRule
import Mettapedia.Computability.KolmogorovComplexity.EffectiveConditionalChainRule
import Mettapedia.Computability.KolmogorovComplexity.EffectiveContainmentRepair
import Mettapedia.UniversalAI.SolomonoffInduction
import Mettapedia.UniversalAI.SolomonoffMeasure
import Mettapedia.UniversalAI.UniversalPrediction
import Mettapedia.PLN.TruthValues.PLNDistributional
import Mettapedia.PLN.RuleFamilies.Temporal
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNFrechetBounds
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleConnection
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleDivergence
import Mettapedia.PLN.Bridges.CategoryTheory.PLNEnrichedCategory
import Mettapedia.PLN.Bridges.KR
import Mettapedia.PLN.Evidence.PLNEvidence
import Mettapedia.PLN.Evidence.PLN_KS_Bridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeductionComposition
import Mettapedia.CategoryTheory.GeneralizedOpenMaps.Weighted
import Mettapedia.OSLF.Bridges.CategoryTheory.OpenMap
import Mettapedia.OSLF.Bridges.CategoryTheory.OpenMapRegression
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOL
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLConsequence
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridge
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelSetTheoryBridgeRegression
import Mettapedia.PLN.Bridges.Languages.WorldModel.PLNWorldModelTwoSortBridge
import Mettapedia.PLN.WorldModel.PLNWorldModelInstitution
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhoodConsequence
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeCompleteness
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeNeighborhoodEmbedding
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeNeighborhoodCanonical
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeWeighted
import Mettapedia.KR.ConceptGeometry.AbstractInheritance
import Mettapedia.KR.ConceptGeometry.Bridges
import Mettapedia.NARS
import Mettapedia.Evidence
import Mettapedia.Cybernetics
import Mettapedia.Enactive
import Mettapedia.PLN.WorldModel.Experiment
-- PLN confidence/strength/ITV characterization tower (finite + infinite:
-- Ising/Gibbs/DLR and i.i.d. de Finetti).  `PLNTruthTheoryIndex` is the
-- proof-carrying crown index (headline package `plnTruthTheoryPackage`).
import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex

-- Universal AI (Hutter Chapters 2-7)
import Mettapedia.UniversalAI.SimplicityUncertainty
import Mettapedia.UniversalAI.BayesianAgents
import Mettapedia.UniversalAI.OptimalityBoundary
import Mettapedia.UniversalAI.ProblemClasses
import Mettapedia.UniversalAI.TimeBoundedAIXI
import Mettapedia.UniversalAI.Omega

-- Value Under Ignorance (Wyeth & Hutter 2025)
import Mettapedia.UniversalAI.ValueUnderIgnorance

-- Multi-Agent RL Framework (Grain of Truth - Phase 2)
import Mettapedia.UniversalAI.MultiAgent.JointActions
import Mettapedia.UniversalAI.MultiAgent.Environment
import Mettapedia.UniversalAI.MultiAgent.Policy
import Mettapedia.UniversalAI.MultiAgent.Value
import Mettapedia.UniversalAI.MultiAgent.BestResponse
import Mettapedia.UniversalAI.MultiAgent.Nash
import Mettapedia.UniversalAI.MultiAgent.Examples

-- Reflective Oracles (Grain of Truth - Core Infrastructure)
import Mettapedia.UniversalAI.ReflectiveOracles.Basic

-- Grain of Truth (Phase 4 - Infrastructure only)
import Mettapedia.UniversalAI.GrainOfTruth.Setup

-- Bridge (connects geometry to probability/logic)
import Mettapedia.Bridge.BitVectorEvidence

-- Languages
import Mettapedia.Languages.MeTTa
import Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
import Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
import Mettapedia.Languages.Megalodon.HenkinTypeFragment
import Mettapedia.Languages.Megalodon.MathdataProofFormation
import Mettapedia.Languages.Megalodon.TheoryAdmissionKernel
import Mettapedia.Languages.Megalodon.TheoryAdmissionSequence
import Mettapedia.Languages.Megalodon.MathdataMixedSubstitutionBoundary
import Mettapedia.Languages.Megalodon.HenkinTermInterpretation
import Mettapedia.Languages.Megalodon.HenkinTermSubstitution
import Mettapedia.Languages.Megalodon.MathdataTypeFormation
import Mettapedia.Languages.Megalodon.SourceTypeParameters
import Mettapedia.Languages.Megalodon.HenkinTermTypeSubstitution
import Mettapedia.Languages.Megalodon.HenkinEqualityInterpretation
import Mettapedia.Languages.Megalodon.NativeEqualitySpecialization
import Mettapedia.Languages.Megalodon.DefinitionEnvironmentBoundary
import Mettapedia.Languages.Megalodon.HenkinDeltaInterpretation
import Mettapedia.Languages.Megalodon.HenkinDeltaTyping
import Mettapedia.Languages.Megalodon.HenkinDeltaSemantics
import Mettapedia.Languages.Megalodon.NativeDefinitionModel
import Mettapedia.Languages.Megalodon.NativeSupport
import Mettapedia.Languages.Megalodon.EnvironmentDependency
import Mettapedia.Languages.Megalodon.EnvironmentDependencyCheck
import Mettapedia.Languages.Megalodon.NativeProofEnvironment
import Mettapedia.Languages.Megalodon.NativeEnvironmentExtensionExamples
import Mettapedia.Languages.Megalodon.HenkinErasureInversion
import Mettapedia.Languages.Megalodon.HenkinTermStrengthening
import Mettapedia.Languages.Megalodon.HenkinNormalizationSemantics
import Mettapedia.Languages.Megalodon.HenkinNormalizationExamples
import Mettapedia.Languages.Megalodon.HenkinTransitionInvariantProof
import Mettapedia.Languages.Megalodon.HenkinProofSoundness
import Mettapedia.Languages.Megalodon.HenkinProofSoundnessExamples
import Mettapedia.Languages.Megalodon.HenkinTransitionInvariantImport
import Mettapedia.Logic.HOL.Syntax.PartialConstSubstitution
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics
import Mettapedia.Logic.HOL.TypeSubstitutionDerivation
import Mettapedia.Logic.HOL.ProofSyntaxTypeSubstitution
import Mettapedia.Logic.HOL.ImpredicativeProofTranslation
import Mettapedia.Logic.HOL.TypeSubstitutionSemantics
import Mettapedia.Logic.HOL.TypeSubstitutionCompositionSemantics
import Mettapedia.Logic.HOL.TypeSubstitutionModelCoherence
import Mettapedia.Logic.HOL.FullDomainInstitution
import Mettapedia.Logic.HOL.Semantics.LogicalRelationModel
import Mettapedia.Logic.HOL.TypeDerivedSignatureExamples
import Mettapedia.GSLT.LanguageDef.HOLTypeDerivedConsequence
import Mettapedia.GSLT.LanguageDef.HOLFullDomainTheory
import Mettapedia.Languages.Megalodon.PreambleFragmentVertical
import Mettapedia.Languages.Megalodon.PreambleDependencyRestriction
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.TowerTheoryNode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.DeclarationFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.BetaPreservation
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.FormationSensitiveMIL
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.FormationSensitiveMILElimination
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.FormationSensitiveMILEliminationIota
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeListDeclarations
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeList
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeListElimination
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeListEliminationPreservation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Examples.FormationSensitiveNativeListEliminationExamples
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeIdentity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorElimination
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorEliminationPreservation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Examples.FormationSensitiveNativeRelatorEliminationExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicParallelSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DefinitionalExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.CheckedDefinitionalExpansion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.TransparentRelatorExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDelta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.DefinitionalExpansionExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SigmaConversionBoundary
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveProjection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSubjectReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationSensitivePreservationExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDeclarationSpine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTelescopeSpine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationSensitiveDeclarationSpineExamples
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.FormationSensitiveMILArgumentRecovery
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.FormationSensitiveMILIotaPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConversionConservativeExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ConservativeConversion
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILConversionCompletion
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILConversionParallel
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILConversionParallelSubstitution
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILConversionParallelSpine
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILConversionParallelCoherence
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILConversionDevelopment
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILConversionDevelopmentChain
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILConversionDevelopmentComplete
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.FormationSensitiveMILQualification
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationAdmissionReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCodeDependencies
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILRootConversionCode
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeIndexedRootConversionCode
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeConversionChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRelatorRootConversionCode
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRelatorConversionChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionCompletion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionParallel
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionParallelSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionParallelSpine
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionParallelCoherence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionDevelopment
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionDevelopmentRelator
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionDevelopmentComplete
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorQualification
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependentComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.DependentComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveThunkComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ThunkComputation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeConversionNeedConsumer
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputationTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputationSemantics
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputationPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ScopedComputationExamples
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationQualification
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationEffectTree
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLFragmentDenotation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeUniverseModelBoundary
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeMatchedTransportDenotation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedComputationTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NeedMachineAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineTypingLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineControlTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachinePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ScopedNeedMachinePreservationExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalSemantics
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineRunSegments
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalMachineLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalAdequacy
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NeedNaturalAdequacy
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedMachineStackBoundary
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedImmediateDemand
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NeedImmediateDemand
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedComputationFunction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.NeedComputationFunction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedSyntax
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedTypedSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.PolarizedNeedTypingExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachineExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedEmbedding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.PolarizedNeedDependentExecution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedRuntimeTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachineLocalTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachineHeapTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachinePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.PolarizedNeedPreservationExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalSemantics
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedMachineRunSegments
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalMachineLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalContinuation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalMeaning
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalLocalReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalActionReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalProtocolReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalAdequacy
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedNaturalEquations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedEvaluationEquivalence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedFunctionPassing
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedImmediateDemand
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedEquationBoundaries
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.PolarizedNeedNaturalExamples
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireData
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.RawInferenceService
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.RawInferenceMILWorkload
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedInferenceService
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedInferenceWorkload
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedInferenceFunction
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.MILNativeMaterialization
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.MILNativeMaterializationExamples
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedHigherOrderInference
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedProviderWorkload
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.PolarizedNeedDistinctionObserver
import Mettapedia.GSLT.LanguageDef.SortedABTRenaming
import Mettapedia.GSLT.LanguageDef.SortedABTSubstitution
import Mettapedia.GSLT.LanguageDef.SortedABTSubstitutionExamples
import Mettapedia.Machines.BranchLocalNeed.DependentService
import Mettapedia.Machines.BranchLocalNeed.AllocationBound
import Mettapedia.Machines.BranchLocalNeed.LocalSteps
import Mettapedia.Machines.BranchLocalNeed.LocalStepPaths
import Mettapedia.Machines.BranchLocalNeed.Representation
import Mettapedia.TypeTheory
import Mettapedia.TypeTheory.ContextualDependentSequencing
import Mettapedia.TypeTheory.ContextualKleisliAdjunction
import Mettapedia.TypeTheory.ContextualKleisliProductBoundary
import Mettapedia.TypeTheory.ContextualComputationAlgebra
import Mettapedia.TypeTheory.ContextualComputationAlgebraProducts
import Mettapedia.TypeTheory.ContextualAlgebraSequencing
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeConversionAlgebraService
import Mettapedia.TypeTheory.ContextualThunkStrategy
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveSimpleFragment
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveSimpleCwf
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitivePresheafSemantics
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedPresheafControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayTransport
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayCoherence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayFormation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedSubstitutionCategory
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.NativeCheckedJudgmentPresheaf
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedContextConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeIntroductionComputationReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativePrincipalComputationReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Examples.NativeConvertedIntroductionControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeDeclarationSpineReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeDeclarationSpineSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeBranchReturnComputation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeBranchReturnExecution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeBranchReturnControls
import Mettapedia.Data.Fin.OptionSequence
import Mettapedia.Data.List.FiniteLookup
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeStructuralCertificateProposal
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRecursiveSchemaCertificates
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRecoveredArguments
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativePayloadSchemaCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeRecursiveRootComputation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeDeclaredRootExecution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Examples.NativeDeclaredRootControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeDependentCongruence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeContextualComputationReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeContextualComputationCompleteness
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Examples.NativeContextualComputationControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedPathExecution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedPathControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionPaths
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptPaths
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptJoinControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionComponentsControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedBinderAlignment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependencies
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRestriction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationSensitiveRestrictionExamples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationSensitiveRestrictionPreservation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLInterface
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeRepresentation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLDefinitionAdmission
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeProofCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLDependentProofExecution
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLInvariant
import Mettapedia.Languages.GF.GFWMConnections
import Mettapedia.Languages.GF.GFWMConnectionsRegression
import Mettapedia.Languages.GF.GFWMObligationAdapter
import Mettapedia.Languages.GF.GFWMObligationAdapterRegression
import Mettapedia.Languages.GF.GFToFOLSetBridge
import Mettapedia.Languages.GF.GFToFOLSetBridgeRegression
import Mettapedia.Conformance.HECoreFiles
import Mettapedia.Conformance.SimpleHE
import Mettapedia.Conformance.SimplePeTTa

-- Examples
import Mettapedia.Examples.SymmetricMeasures
import Mettapedia.Examples.PLN
import Mettapedia.PLN.Bridges.GSLT.PeTTaTypedPLNNativeBridge

-- 100 Creative Proofs
import Mettapedia.HundredProofs

-- Hyperseed exploration/closure layer
import Mettapedia.Hyperseed

-- Cognitive architecture: MetaMo / OpenPsi / MicroPsi / Bridges / Values (axiom-free strands)
import Mettapedia.CognitiveArchitecture.Main

-- GodelClaw (Oruži cognitive architecture) is NOT imported here: its full
-- transitive closure pulls in `Logic.MarkovLogic*` modules that still have genuine
-- 4.31 proof-level breakage (a follow-up round fixes those in place and adds it).

-- AutoBooks / Henkin (1950): "Completeness in the Theory of Types"
import Mettapedia.AutoBooks.Codex.Henkin1950

-- Fluid Dynamics: Navier-Stokes finite-mode / Cole-Hopf approximation layer
import Mettapedia.FluidDynamics

-- Ethics: FOET / Gewirth PGC / value-attribution + DDLPlus governance bridges
import Mettapedia.Ethics

-- ============================================================================
-- Computability/  (arithmetical hierarchy · Kolmogorov complexity · Hutter
-- computability · Cantor space · oracle/probabilistic machines · the
-- non-cascading PNP obstruction modules)
-- ============================================================================
-- These build at Lean 4.31.  Some carry pre-existing in-place `sorry`s.
-- `PNP.SymmetrizationObstruction` formerly collided with
-- `PNP.PostSwitchInputObstruction` (both declared `abbrev …PNP.BitVec`); its local
-- abbrev is now renamed `MajBitVec`, so both co-import cleanly.
-- `LocalityObstruction`/`AsymmetryBudgetObstruction` are repaired for the Lean
-- 4.31 `.reducible`-transparency change (mass/benchmark wrapper `def`s marked
-- `@[reducible]`; one projection-defeq `simpa … using` → `using!`), and the
-- `ProbabilisticTM`/`OracleTMRefined`/`OracleTM` `zero_le _` → `bot_le` (the
-- ambient `zero_le` became a zero-argument term).
import Mettapedia.Computability.ArithmeticalHierarchy.Level3
import Mettapedia.Computability.CantorSpace
import Mettapedia.Computability.HutterComputability
import Mettapedia.Computability.HutterComputabilityClosure
import Mettapedia.Computability.HutterComputabilityENNReal
import Mettapedia.Computability.HutterComputabilityRational
import Mettapedia.Computability.PartialEvaluation
import Mettapedia.Computability.PartialEvaluationTransformation
import Mettapedia.Computability.InterpreterMediatedSpecialization
import Mettapedia.Computability.KolmogorovComplexity.Conditional
import Mettapedia.Computability.KolmogorovComplexity.ConditionalInterpreter
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainComplexity
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainPrefix
import Mettapedia.Computability.KolmogorovComplexity.CompressiveFeature
import Mettapedia.Computability.KolmogorovComplexity.ConditionalChainRule
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPrefixBridge
import Mettapedia.Computability.KolmogorovComplexity.ContainmentRepair
import Mettapedia.Computability.KolmogorovComplexity.DirectionalInformation
import Mettapedia.Computability.KolmogorovComplexity.Prefix
import Mettapedia.Computability.KolmogorovComplexity.PrefixComplexity
import Mettapedia.Computability.KolmogorovComplexity.SelfDelimitingCode
import Mettapedia.Computability.KolmogorovComplexity.Uncomputability
-- `OracleTM` is NOT imported: it is an older parallel variant of the oracle-machine
-- development whose declarations (`oracleOutputOneSet`, …) collide in a single
-- environment with the canonical `OracleTMReal` already imported below.  Its own
-- 4.31 `zero_le _` → `bot_le` fix is applied in place so it stays buildable, but it
-- stays outside the closure (nothing imports it; `OracleTMReal`/`OracleTMRefined`
-- supersede it).
import Mettapedia.Computability.OracleTMReal
import Mettapedia.Computability.OracleTMRefined
import Mettapedia.Computability.ProbabilisticTM
import Mettapedia.Computability.ProbabilisticTMRefined
import Mettapedia.Computability.PNP.ABVisibleState
import Mettapedia.Computability.PNP.AsymmetryBudgetObstruction
import Mettapedia.Computability.PNP.ConditioningObstruction
import Mettapedia.Computability.PNP.FiberNeutralityObstruction
import Mettapedia.Computability.PNP.FixedWidthIsolationObstruction
import Mettapedia.Computability.PNP.GlobalWeaknessObstruction
import Mettapedia.Computability.PNP.InfinitaryHMLObstruction
import Mettapedia.Computability.PNP.InvariantScoreObstruction
import Mettapedia.Computability.PNP.LocalityObstruction
import Mettapedia.Computability.PNP.OrbitNeutralityObstruction
import Mettapedia.Computability.PNP.PairwiseCandidateBridge
import Mettapedia.Computability.PNP.PairwiseColumnsObstruction
import Mettapedia.Computability.PNP.PairwiseSurvivorMoments
import Mettapedia.Computability.PNP.PostSwitchInputObstruction
import Mettapedia.Computability.PNP.PresentMomentShattering
import Mettapedia.Computability.PNP.ResidualSymmetryObstruction
import Mettapedia.Computability.PNP.RhsBiasIrrelevance
import Mettapedia.Computability.PNP.SymmetrizationObstruction
import Mettapedia.Computability.PNP.TwoUniversalRhsIrrelevance
import Mettapedia.Computability.PNP.VisiblePostSwitchData
import Mettapedia.Computability.PNP.WeightAsymmetryObstruction
import Mettapedia.Computability.PNP.WeightedFiberNeutralityObstruction

-- ============================================================================
-- GSLT/  (Graph-of-Synchronization-Trees: core · graph theory · logic · topos ·
-- causality/trace · weight-cost dynamics · the non-Interactive Meredith modules ·
-- assembly theory)
-- ============================================================================
-- These build at Lean 4.31.  `Causality/SyncTree`, `Dynamics/ExtendedHML`,
-- `Dynamics/PathIntegral`, and `Synthesis/MainConservation` are now repaired for the
-- 4.31 transparency / stricter-elaboration changes (dotted-name resolution via
-- `namespace GSLT`; `▸`-motive, `simp`-vs-defeq on the `VectorialAccount` synonym, and
-- anonymous-constructor unfolds done in term/`show`/`unfold` mode; phantom-`A`
-- instance and missing `[HasMinimalContexts S]` / `{k}` binders supplied; one genuine
-- bisimulation-symmetry proof completed) and imported below.
-- `Life/ReplicationFixedPoint` and the `Meredith/Interactive*` modules were held out
-- last round only because they depend on the `Languages/` cluster (`DerivedRepNu` /
-- `MultiStep` / `SemanticSubstitution`).  That dependency is now repaired for the 4.31
-- transparency change, so all four are folded in below.  `ReplicationFixedPoint`'s own
-- code needed no fix; `InteractiveGSLT` / `InteractiveCostBridge` each needed the
-- `simpa using! h` transparency churn-fix at the defeq-closing sites.
import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Core.MultiRewrite
import Mettapedia.GSLT.Core.MultiRewrite.Comm
import Mettapedia.GSLT.Core.WriterGSLT
import Mettapedia.GSLT.Core.ReservesSelfModel
import Mettapedia.GSLT.LanguageDef.MultiRewriteExtension
import Mettapedia.GSLT.LanguageDef.MultiRewriteJoin
import Mettapedia.GSLT.LanguageDef.MultiRewriteSchematic
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.LanguageDef.CertificateGSLTExponentialObstruction
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFunctionalHomPresheaf
import Mettapedia.GSLT.LanguageDef.CertificateGSLTSemanticFunctionObject
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFunctionPredicate
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedDerivations
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRepresentableProofs
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchMachine
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOccurrencePreservingInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchModalAdequacy
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchModalInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerPresheaf
import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily
import Mettapedia.GSLT.LanguageDef.CertificateGSLTIndexedComprehensionBridge
import Mettapedia.GSLT.LanguageDef.CertificateGSLTPiVarianceBoundary
import Mettapedia.GSLT.LanguageDef.CertificateGSLTPresheafPiSubstitution
import Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi
import Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPiBoundary
import Mettapedia.TypeTheory.CategoryOfElementsBaseChangeIndexedBridge
import Mettapedia.TypeTheory.PresheafPiIndexComparison
import Mettapedia.TypeTheory.PresheafPiLimitComparison
import Mettapedia.TypeTheory.PresheafPiEvaluationBaseChange
import Mettapedia.TypeTheory.PresheafPiIndexedCwfBridge
import Mettapedia.TypeTheory.DisplayedPresheafCwf
import Mettapedia.TypeTheory.CwfYoneda
import Mettapedia.TypeTheory.CwfYonedaCoherence
import Mettapedia.TypeTheory.DisplayedPresheafSupport
import Mettapedia.TypeTheory.DisplayedPresheafCwfIndexedComparison
import Mettapedia.TypeTheory.DisplayedPresheafSigma
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedPresheafSigmaRoute
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedPresheafCwfBridge
import Mettapedia.GSLT.LanguageDef.CertificateGSLTExactLedgerTheoryTranslation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTCanonicalRouteTrinity
import Mettapedia.GSLT.LanguageDef.CertificateGSLTIndependentSearch
import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerProofRelevanceCanary
import Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity
import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILCheckedNativeListOpenSearchTrinity
import Mettapedia.GSLT.LanguageDef.CertificateGSLTInterpretationCanary
import Mettapedia.GSLT.LanguageDef.MultiSortedCloneFiniteProducts
import Mettapedia.OSLF.Syntax.TermCloneCategoryComparison
import Mettapedia.OSLF.Framework.MultiRewriteRely
import Mettapedia.Languages.OpenTheory.OperationalGSLTAdequacy
import Mettapedia.Languages.OpenTheory.WorldModelInterpretation
import Mettapedia.Languages.OpenTheory.ReachabilitySemantics
import Mettapedia.Languages.OpenTheory.EtaCompletenessHeyting
import Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
import Mettapedia.Languages.OpenTheory.WorldModelObservationalQuotient
import Mettapedia.Languages.OpenTheory.WorldModelNativeEqualityBoundary
import Mettapedia.Languages.OpenTheory.WMFreeSemanticModelBoundary
import Mettapedia.Languages.OpenTheory.WMGeneratedFreeBoundary
import Mettapedia.GSLT.Logic.Conditions201202
import Mettapedia.GSLT.Core.SpendLiftInterchange
import Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
import Mettapedia.OSLF.Framework.WMCalculusZeroBoundary
import Mettapedia.OSLF.Framework.WMCalculusNativeOperationalSharing
import Mettapedia.OSLF.Framework.WMCalculusNativeObservation
import Mettapedia.OSLF.Framework.WMCalculusNativeObservationalEquality
import Mettapedia.OSLF.Framework.WMCalculusNativeContextExample
import Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
import Mettapedia.OSLF.Framework.WMCalculusNativeCapability
import Mettapedia.OSLF.Framework.WMCalculusDependentCapabilitySubjectReduction
import Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample
import Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityTransport
import Mettapedia.OSLF.Framework.WMCalculusCapabilityCategory
import Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
import Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
import Mettapedia.OSLF.Framework.WMCalculusReadingCategory
import Mettapedia.OSLF.Framework.WMCalculusAnswerFunctor
import Mettapedia.OSLF.Framework.WMCalculusFreeSemanticModel
import Mettapedia.OSLF.Framework.WMCalculusGeneratedFreeReading
import Mettapedia.OSLF.Framework.WMCalculusQuotientFunctor
import Mettapedia.OSLF.Framework.WMCalculusRewriteCompletenessBoundary
import Mettapedia.OSLF.Framework.WMCalculusEvidenceConversion
import Mettapedia.OSLF.Framework.WMCalculusEvidenceConversionSorted
import Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
import Mettapedia.OSLF.Framework.WMCalculusNativeAuthoredConversion
import Mettapedia.OSLF.Framework.WMCalculusBindingSignature
import Mettapedia.OSLF.Framework.WMCalculusIntrinsicPresheafObservation
import Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace
import Mettapedia.OSLF.Framework.WMCalculusExecutableOccurrence
import Mettapedia.OSLF.Framework.WMCalculusExecutableTrace
import Mettapedia.OSLF.Framework.WMCalculusRedexPosition
import Mettapedia.OSLF.Framework.WMCalculusGeneratedRely
import Mettapedia.OSLF.Framework.WMCalculusSortedBoundary
import Mettapedia.OSLF.Framework.WMCalculusOverlapSortedBoundary
import Mettapedia.OSLF.Framework.WMCalculusScopeSortedBoundary
import Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
import Mettapedia.OSLF.Framework.WMCalculusCombinedNativeObservation
import Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralPresentation
import Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralSemantics
import Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
import Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
import Mettapedia.OSLF.Framework.WMCalculusCombinedPresentationSignature
import Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralRelationalModel
import Mettapedia.OSLF.Framework.WMCalculusCombinedOpenReification
import Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider
import Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider
import Mettapedia.OSLF.Framework.WMCalculusCheckedScopeNativeCapability
import Mettapedia.OSLF.Framework.WMCalculusSortedEncoding
import Mettapedia.PLN.WorldModel.WMCalculusNativeSpace
import Mettapedia.PLN.WorldModel.WMCalculusNativeBindingSpace
import Mettapedia.PLN.WorldModel.WMCalculusIndexedBindingSpace
import Mettapedia.Logic.MarkovLogicClauseNativeObservation
import Mettapedia.Logic.Bridges.WMNativeGSLTIL
import Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
import Mettapedia.Logic.Bridges.WMCheckedScopeGSLTIL
import Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTILMorphism
import Mettapedia.Logic.Bridges.WMNativeCapabilityComputation
import Mettapedia.Logic.Bridges.WMNativeExecutionTraceGSLTIL
import Mettapedia.Logic.Bridges.WMExecutableTraceGSLTIL
import Mettapedia.Logic.Bridges.WMExecutableTraceGSLTILMorphism
import Mettapedia.Logic.Bridges.WMNativeGSLTILMorphism
import Mettapedia.Logic.Bridges.WMMeTTaSpaceAlgebra
import Mettapedia.Logic.Bridges.WMSpaceQueryCoherenceBoundary
import Mettapedia.Logic.Bridges.WMIndexedBindingSpaceAlgebra
import Mettapedia.Logic.Bridges.WMSpaceDependentEquality
import Mettapedia.Logic.BDD.WMPLNBDDWMCExact
import Mettapedia.PLN.WorldModel.WMCalculusJointEvidenceNative
import Mettapedia.PLN.WorldModel.WMJointEvidenceCapabilitySpace
import Mettapedia.PLN.WorldModel.WMStrengthRevisionBoundary
import Mettapedia.TypeTheory.Models.RevisionedFamilies.ObservationSpaceBoundary
import Mettapedia.TypeTheory.Models.RevisionedFamilies.SupportQuotient
import Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyDescent
import Mettapedia.TypeTheory.Models.RevisionedFamilies.ObservableIdentitySemantics
import Mettapedia.TypeTheory.Models.RevisionedFamilies.FamilyNaturality
import Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
import Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityPiRepresentability
import Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedScopeFamilyBridge
import Mettapedia.TypeTheory.Models.RevisionedFamilies.ComputedOpenAnswerFamily
import Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedOpenScopeExecution
import Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedOpenExecutionDisplayed
import Mettapedia.OSLF.Framework.PremiseAwareOccurrenceExtension
import Mettapedia.OSLF.Framework.EngineOccurrenceExtensionGSLT
import Mettapedia.OSLF.Framework.WMEngineOccurrenceCanary
import Mettapedia.PLN.WorldModel.WMJointEvidencePrimeFamily
import Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyNaturality
import Mettapedia.TypeTheory.Models.RevisionedFamilies.ExecutionFamilyBoundary
import Mettapedia.OSLF.Framework.ConstructorObservationBoundary
import Mettapedia.GSLT.Dynamics.ContextualStrategyQualification
import Mettapedia.GSLT.Dynamics.ServiceEffectProtocol
import Mettapedia.GSLT.Core.BranchingTemporal
import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mettapedia.GSLT.Core.Web
import Mettapedia.GSLT.Core.ChangeOfBase
import Mettapedia.GSLT.GraphTheory.Basic
import Mettapedia.GSLT.GraphTheory.Approximants
import Mettapedia.GSLT.GraphTheory.BohmTree
import Mettapedia.GSLT.GraphTheory.ParallelReduction
import Mettapedia.GSLT.GraphTheory.Substitution
import Mettapedia.GSLT.GraphTheory.WeakProduct
import Mettapedia.GSLT.Logic.ContextHML
import Mettapedia.GSLT.Logic.LogicalMetric
import Mettapedia.GSLT.Logic.MinimalContext
import Mettapedia.GSLT.Topos.Yoneda
import Mettapedia.GSLT.Topos.SubobjectClassifier
import Mettapedia.GSLT.Topos.PredicateFibration
import Mettapedia.GSLT.Causality.Trace
import Mettapedia.GSLT.Causality.OccurrenceHistory
import Mettapedia.GSLT.Causality.HistoryCover
import Mettapedia.GSLT.Causality.Mazurkiewicz
import Mettapedia.GSLT.LanguageDef.InteractiveSemantics
import Mettapedia.GSLT.Logic.PropositionalFormula
import Mettapedia.GSLT.Logic.PropositionalResolution
import Mettapedia.GSLT.Logic.PropositionalResolutionComplete
import Mettapedia.GSLT.Logic.PropositionalResolutionNIK
import Mettapedia.GSLT.Logic.PropositionalCut
import Mettapedia.GSLT.Logic.PropositionalMLL
import Mettapedia.GSLT.Logic.HenkinHOL
import Mettapedia.Logic.Bridges.PropositionalCutTait
import Mettapedia.Logic.Bridges.PropositionalFragment
import Mettapedia.Logic.Bridges.PropositionalResolutionNIK
import Mettapedia.Logic.Bridges.PropositionalResolutionTait
import Mettapedia.GSLT.Causality.SyncTree
import Mettapedia.GSLT.Dynamics.WeightCost
import Mettapedia.GSLT.Dynamics.ExtendedHML
import Mettapedia.GSLT.Dynamics.PathIntegral
import Mettapedia.GSLT.Dynamics.KnotDecomposition
import Mettapedia.GSLT.Dynamics.UnfoldingTraversal
import Mettapedia.GSLT.Dynamics.SemiringTraversal
import Mettapedia.GSLT.Dynamics.CollapseAlgebra
import Mettapedia.GSLT.Dynamics.CollapseObservationContract
import Mettapedia.GSLT.LanguageDef.GSLTILCollapseObservationContract
import Mettapedia.GSLT.Dynamics.ProvenanceInterpretation
import Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
import Mettapedia.GSLT.Dynamics.StoreReachability
import Mettapedia.GSLT.Dynamics.StoreCollectionAdvanced
import Mettapedia.GSLT.Dynamics.DialectTranslation
import Mettapedia.GSLT.Dynamics.DialectObstructions
import Mettapedia.GSLT.Dynamics.SpaceGuardedReflection
import Mettapedia.GSLT.LanguageDef.RuleMachineCompilation
import Mettapedia.GSLT.LanguageDef.ContextualEffectTreeLanguage
import Mettapedia.GSLT.LanguageDef.ContextualEffectTreeExactness
import Mettapedia.GSLT.LanguageDef.MatchDecisionContract
import Mettapedia.GSLT.LanguageDef.InferenceRuleSupport
import Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
import Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
import Mettapedia.GSLT.LanguageDef.ErrorObservationCoherence
import Mettapedia.GSLT.LanguageDef.EmptyDemandCoherence
import Mettapedia.GSLT.Dynamics.ProofDeterminedGeneralization
import Mettapedia.GSLT.Synthesis.MainConservation
import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.GSLT.Meredith.LambdaTheory
import Mettapedia.GSLT.Meredith.Bisimulation
import Mettapedia.GSLT.Meredith.Modal.Diamond
import Mettapedia.GSLT.Meredith.Modal.RewriteModality
import Mettapedia.GSLT.Meredith.RhoExample
import Mettapedia.GSLT.Meredith.RhoMinimalContext
import Mettapedia.GSLT.Meredith.WeaknessBridge
-- Interactive Meredith modules (cost/ReducesN bridges over the rho `Languages` layer),
-- unblocked now that the `Languages/` cluster compiles at 4.31.
import Mettapedia.GSLT.Meredith.InteractiveGSLT
import Mettapedia.GSLT.Meredith.InteractiveReducesNBridge
import Mettapedia.GSLT.Meredith.InteractiveCostBridge
import Mettapedia.GSLT.Life.AssemblyTheory
-- Replication fixed-point (depends on `RhoCalculus/DerivedRepNu`, repaired above).
import Mettapedia.GSLT.Life.ReplicationFixedPoint
import Mettapedia.GSLT.LanguageDef.HOLKernelProfiles
import Mettapedia.Algebra.FootprintQuantale
import Mettapedia.OSLF.Framework.GrammarDerives
import Mettapedia.Languages.Metamath.ExprDerive
import Mettapedia.Languages.Metamath.Flatten
