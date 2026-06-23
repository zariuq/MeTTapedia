/-
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

-- Graph Theory (whole basic layer; the classical Hamiltonicity / matching /
-- planarity declarations carry pre-existing in-place `sorry`s).
import Mettapedia.GraphTheory.Basic

-- Probability Theory
import Mettapedia.ProbabilityTheory.Basic
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
import Mettapedia.Algebra.QuantaleWeakness

-- Category Theory (Hypercube/OSLF framework for quantales)
import Mettapedia.CategoryTheory.FuzzyFrame
import Mettapedia.CategoryTheory.LambdaTheory
import Mettapedia.CategoryTheory.PLNInstance
import Mettapedia.CategoryTheory.NativeTypeTheory
import Mettapedia.CategoryTheory.PLNTerms
import Mettapedia.CategoryTheory.ModalTypes
import Mettapedia.CategoryTheory.Hypercube
import Mettapedia.CategoryTheory.PLNSemiringQuantale
import Mettapedia.CategoryTheory.GeneralizedOpenMaps

-- Information theory (combinatorial bounds)
import Mettapedia.InformationTheory.BinomialEntropy
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

-- Logic
import Mettapedia.Logic.GunkyMereology
import Mettapedia.Logic.StoneGunkDuality
import Mettapedia.Logic.Metaphysics
import Mettapedia.Logic.SolomonoffPrior
import Mettapedia.Logic.SolomonoffInduction
-- import Mettapedia.Logic.SolomonoffMeasure  -- WIP (outer measure construction is incomplete)
import Mettapedia.Logic.UniversalPrediction
import Mettapedia.Logic.PLNDistributional
import Mettapedia.Logic.PLNTemporal
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNFrechetBounds
import Mettapedia.Logic.PLNQuantaleConnection
import Mettapedia.Logic.PLNQuantaleDivergence
import Mettapedia.Logic.PLNEnrichedCategory
import Mettapedia.Logic.PLNEvidence
import Mettapedia.Logic.PLN_KS_Bridge
import Mettapedia.Logic.PLNDeductionComposition
import Mettapedia.Logic.TemporalQuantale
import Mettapedia.Logic.WeightedOpenMaps
import Mettapedia.Logic.OSLFOpenMapBridge
import Mettapedia.Logic.OpenMapBridgeRegression
import Mettapedia.Logic.PLNWorldModelHOL
import Mettapedia.Logic.PLNWorldModelFOL
import Mettapedia.Logic.PLNWorldModelHOLCompleteness
import Mettapedia.Logic.PLNWorldModelHOLConsequence
import Mettapedia.Logic.PLNWorldModelFOLCompleteness
import Mettapedia.Logic.PLNWorldModelSetTheoryBridge
import Mettapedia.Logic.PLNWorldModelSetTheoryBridgeRegression
import Mettapedia.Logic.PLNWorldModelPureKernelBridge
import Mettapedia.Logic.PLNWorldModelInstitution
import Mettapedia.Logic.PLNWorldModelHyperdoctrine
import Mettapedia.Logic.PLNWorldModelCategoricalBridge
import Mettapedia.Logic.PLNWorldModelNeighborhoodConsequence
import Mettapedia.Logic.PLNWorldModelKripkeCompleteness
import Mettapedia.Logic.PLNWorldModelKripkeNeighborhoodEmbedding
import Mettapedia.Logic.PLNWorldModelKripkeNeighborhoodCanonical
import Mettapedia.Logic.PLNWorldModelKripkeWeighted
import Mettapedia.Logic.ConceptOntology
import Mettapedia.Logic.AbstractInheritance
import Mettapedia.Logic.NARSInheritance
import Mettapedia.Logic.PLNWorldModelExperiment
import Mettapedia.Logic.PLNWorldModelExperimentRegression
import Mettapedia.Logic.PLNWorldModelExperimentStochastic
import Mettapedia.Logic.PLNWorldModelExperimentStochasticRegression
-- PLN confidence/strength/ITV characterization tower (finite + infinite:
-- Ising/Gibbs/DLR and i.i.d. de Finetti).  `PLNTruthTheoryIndex` is the
-- proof-carrying crown index (headline package `plnTruthTheoryPackage`).
import Mettapedia.Logic.PLNTruthTheoryIndex

-- Universal AI (Hutter Chapters 2-7)
import Mettapedia.UniversalAI.SimplicityUncertainty
import Mettapedia.UniversalAI.BayesianAgents
import Mettapedia.UniversalAI.ProblemClasses
import Mettapedia.UniversalAI.TimeBoundedAIXI

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
import Mettapedia.Computability.KolmogorovComplexity.Prefix
import Mettapedia.Computability.KolmogorovComplexity.PrefixComplexity
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
import Mettapedia.Computability.PNP.ABVisibleSurface
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
import Mettapedia.Computability.PNP.VisiblePostSwitchSurface
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
import Mettapedia.GSLT.Causality.SyncTree
import Mettapedia.GSLT.Dynamics.WeightCost
import Mettapedia.GSLT.Dynamics.ExtendedHML
import Mettapedia.GSLT.Dynamics.PathIntegral
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
