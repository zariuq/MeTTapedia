import Lake

open System Lake DSL

package Mettapedia where
  version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "0df444a360eaa60ab8c11dca51a86af692955474"

-- Editable local repos live in ../externals.
require TauCeti from "../externals/TauCeti"
require ordered_semigroups from "../externals/ordered_semigroups"

require Foundation from "../externals/Foundation"

-- Polynomial functors and lenses (Spivak–Niu Poly); its cslib dependency is ../externals/cslib.
require PolyFun from "../externals/PolyFun"

require exchangeability from "../externals/exchangeability"

require provenance from "../externals/provenance"

require borel_det from "Mettapedia/SetTheory/BorelDeterminacy"

require catLogic from "Mettapedia/CategoricalLogic"

require Metatheory from "../externals/Metatheory"

/- LeaTTa is an optional realization and comparison target.  The ordinary
MeTTapedia profile neither resolves nor builds it; pass `-Kleatta` together
with the recorded package override to opt in. -/
def leattaIntegrationEnabled : Bool := (get_config? leatta).isSome

meta if leattaIntegrationEnabled then
  require MettaHyperonFull from "../externals/LeaTTa"

require algorithms from "../algorithms"

require mettail_core from "../batteries/mettail-core"

require gf_core from "../batteries/gf-core"

require certifyingDatalog from "../externals/certifyingDatalog"

require «mm-lean4» from "../standalone/mm-lean4"

-- Editable declarative Lean-core source used by the GSLT environment-growth bridge.
require lean4lean from "../externals/lean4lean"

-- Standalone Knuth–Skilling external (canonical home; namespace `KnuthSkilling.*`).
-- Replaces the previously embedded copy at `Mettapedia/ProbabilityTheory/KnuthSkilling/`.
require «ks-foundations-of-inference-lean» from "../standalone/ks-foundations-of-inference"

/-- Authored MeTTa sources consumed by compile-time program quotation.  Making
the directory an explicit text input prevents stale quoted constructor data
when a curriculum file changes without a Lean source edit. -/
input_dir primeMotivationSources where
  path := "../../MettaKernel/Curriculum/PrimeMotivation"
  text := true
  filter := .extension "metta"

@[default_target] lean_lib Mettapedia

/-- Maintained logic-programming theory and executable graph-runtime modules. -/
lean_lib LogicProgrammingTheory where
  roots := #[`Mettapedia.Logic.LP, `Mettapedia.Logic.Prolog]
  globs := #[Glob.one `Mettapedia.Logic.LP, Glob.one `Mettapedia.Logic.Prolog,
    Glob.submodules `Mettapedia.Logic.LP,
    Glob.submodules `Mettapedia.Logic.Prolog]

/-- The versioned PeTTa model, its independent specifications and local proofs. -/
lean_lib PLeaTTaTheory where
  roots := #[`Mettapedia.Languages.MeTTa.PLeaTTa]
  globs := #[Glob.one `Mettapedia.Languages.MeTTa.PLeaTTa,
    Glob.submodules `Mettapedia.Languages.MeTTa.PLeaTTa]

/-- Generic predicate contracts and their runtime call-protocol instance. -/
lean_lib RuntimeTypingTheory where
  roots := #[`Mettapedia.Logic.ConstraintTypes.Audit,
    `Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.Audit]
  globs := #[Glob.one `Mettapedia.Logic.ConstraintTypes,
    Glob.submodules `Mettapedia.Logic.ConstraintTypes,
    Glob.one `Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping,
    Glob.submodules `Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping]

/-- The standalone attention-budget models use this package's existing cache. -/
lean_lib AttentionEconomyTheory where
  srcDir := "../pettaclaw"
  roots := #[`StiMass, `StiFloor, `StiFloorDecay]

/-- Generic coloring curriculum and compositional algebra in the companion source tree. -/
lean_lib FourColorCore where
  srcDir := "../fourcolor"
  roots := #[`FourColor, `FourColor.IntegrationCore]

/- The exact maintained roots of the compositional abstract-machine
qualification. This target is deliberately narrower than the aggregate library
and does not pull optional implementation studies into the AM proof boundary. -/
lean_lib AbstractMachines where
  roots := #[
    `Mettapedia.GSLT.Distinction.SpanTransportControls,
    `Mettapedia.Machines.ProductiveCoreAdapters,
    `Mettapedia.Machines.OccurrenceMachine,
    `Mettapedia.Machines.RefocusingControls,
    `Mettapedia.Machines.CategoricalAbstractMachineControls,
    `Mettapedia.Languages.C11.FixedCoreControls,
    `Mettapedia.Languages.C11.CestaFixedCoreControls,
    `Mettapedia.Languages.C11.StatementMachineRefinementControls,
    `Mettapedia.Languages.C11.FixedCoreServiceControls,
    `Mettapedia.Languages.MeTTa.HE.RecursiveControls,
    `Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy,
    `Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedRecursiveAdequacy,
    `Mettapedia.Languages.MeTTa.HE.RecursiveService,
    `Mettapedia.Languages.MeTTa.PeTTa.Resumption,
    `Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming,
    `Mettapedia.Languages.MeTTa.PeTTa.CettaOperationAdmission,
    `Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender,
    `Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance,
    `Mettapedia.Languages.MeTTa.HE.TypeGrounding.SimpleAgreement,
    `Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateOperationalBridge,
    `Mettapedia.Languages.MeTTa.Translation.HEPeTTaOpenRecursive,
    `Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslate,
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OrderedRealizations]

/- Maximal roots of the modules whose declared semantics or executable
comparison depends on LeaTTa.  Their local imports are built recursively. -/
meta if leattaIntegrationEnabled then
@[default_target] lean_lib LeaTTaIntegration where
  roots := #[
    `Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaArgumentExecution,
    `Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaBindingExecutionBoundary,
    `Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaFresheningCorrespondence,
    `Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaPatternExecution,
    `Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaProgramEnvironment,
    `Mettapedia.GSLT.LanguageDef.LFCheckerSim,
    `Mettapedia.GSLT.LanguageDef.LFEngineProbe,
    `Mettapedia.GSLT.LanguageDef.LFEngineReduce,
    `Mettapedia.GSLT.LanguageDef.MIEvalEncoding,
    `Mettapedia.GSLT.LanguageDef.MIEvalHostingEmitter,
    `Mettapedia.GSLT.LanguageDef.MIEvalHostingRevEmitter,
    `Mettapedia.GSLT.ReproducibleBuild.LeaTTaReplayInstance,
    `Mettapedia.Languages.MM0.Presentation.ScopedServiceCorrespondence,
    `Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.LeaTTaDIndGEvaluator,
    `Mettapedia.Languages.MeTTa.HE.CanonicalEquationBridge,
    `Mettapedia.Languages.MeTTa.HE.EquationScopeControls,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaApplicationTypeCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaArgumentTypeSelectionCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaBranchFresheningDiagnosticCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaCollapseBindingCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaConcreteConformance,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaContextSpaceCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorBindingPayloadCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorServiceAwareConformance,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedApplicationBindingRetentionCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedApplicationErrorChronologyCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingConflictCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedReturnSelectionCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaFuelObservability,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaGetTypeArityCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaGroundTypeCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaMalformedArrowCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaMettaBoundaryCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaMultipleActualTypeCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaMultipleSignatureCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaOperatorHeadCastConformance,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaOperatorHeadEvaluationCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaOperatorHeadFreshnessCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaSignatureExpectedCaptureCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaStateFreeConfigurationConformance,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaStateValueRefinement,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaTypeInferenceScopeCounterexample,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationMatchConformance,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaTypeRefinement,
    `Mettapedia.Languages.MeTTa.HE.LeaTTaTypeVariableEscapeCounterexample,
    `Mettapedia.Languages.MeTTa.HE.MatchAllChildNil,
    `Mettapedia.Languages.MeTTa.HE.NativeBindingsDataControls,
    `Mettapedia.Languages.MeTTa.HE.SpaceAlgebraLeaTTa,
    `Mettapedia.Languages.MeTTa.HE.StateComponentAlgebra,
    `Mettapedia.Languages.MeTTa.HE.UnificationCompleteness,
    `Mettapedia.Languages.MeTTa.LeaTTa]

-- Only this module quotes the curriculum files. Its importers inherit the
-- dependency through the normal module graph, without invalidating unrelated
-- libraries when an authored curriculum file changes.
lean_lib PrimeMotivationQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PrimeCandidates.Native.CandidateMotivationProgramPackages]
  needs := #[`@/primeMotivationSources]

input_dir holLightMeTTaSources where
  path := "../../metta/hol_light"
  text := true
  filter := .extension "metta"

lean_lib HOLLightMeTTaQuotation where
  roots := #[`Mettapedia.Languages.HOLLight.MeTTa.Program]
  needs := #[`@/holLightMeTTaSources]

input_file pettaBoundCallsSource where
  path := "../../metta/fixtures/petta_bound_calls.metta"
  text := false

lean_lib PeTTaBoundCallQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.BoundCallControls]
  needs := #[`@/pettaBoundCallsSource]

-- The GSLT execution library lives beside these proofs in `metta/gslt/lib`.
-- Every quoted file is an input of the module that quotes it.
input_file gsltMatchAutomataSource where
  path := "../../metta/gslt/lib/gslt_match_automata.metta"
  text := false

lean_lib GSLTMatchAutomataQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataProgram]
  needs := #[`@/gsltMatchAutomataSource]

input_file gsltRuleExecutionSource where
  path := "../../metta/gslt/lib/gslt_rule_execution.metta"
  text := false

input_file gsltPremiseOperationsSource where
  path := "../../metta/gslt/lib/gslt_premise_operations.metta"
  text := false

input_file gsltScopedExecutionSource where
  path := "../../metta/gslt/lib/gslt_scoped_execution.metta"
  text := false

input_file gsltCollectionSelectionSource where
  path := "../../metta/gslt/lib/gslt_collection_selection.metta"
  text := false

input_file gsltCollectionMachineSource where
  path := "../../metta/gslt/lib/gslt_collection_machine.metta"
  text := false

input_file gsltCollectionLoggedSearchSource where
  path := "../../metta/gslt/lib/gslt_collection_logged_search.metta"
  text := false

input_file gsltCollectionBackendSource where
  path := "../../metta/gslt/lib/gslt_collection_backend.metta"
  text := false

input_file gsltCollectionContextsSource where
  path := "../../metta/gslt/lib/gslt_collection_contexts.metta"
  text := false

input_file gsltRecursiveCollectionSource where
  path := "../../metta/gslt/lib/gslt_recursive_collection.metta"
  text := false

input_file gsltCollectionPresentationSource where
  path := "../../metta/gslt/lib/gslt_collection_presentation.metta"
  text := false

input_file gsltCollectionHandoffSource where
  path := "../../metta/gslt/lib/gslt_collection_handoff.metta"
  text := false

input_file gsltCollectionContinuationSource where
  path := "../../metta/gslt/lib/gslt_collection_continuation.metta"
  text := false

input_file gsltCollectionOccurrencesSource where
  path := "../../metta/gslt/lib/gslt_collection_occurrences.metta"
  text := false

input_file gsltCollectionInstallSource where
  path := "../../metta/gslt/lib/gslt_collection_install.metta"
  text := false

input_file gsltCollectionMatchLanesSource where
  path := "../../metta/gslt/lib/gslt_collection_match_lanes.metta"
  text := false

input_file gsltCollectionCollectorSource where
  path := "../../metta/gslt/lib/gslt_collection_collector.metta"
  text := false

input_file gsltCollectionOccurrenceMachineSource where
  path := "../../metta/gslt/lib/gslt_collection_occurrence_machine.metta"
  text := false

input_file gsltCollectionOccurrenceDiscoverySource where
  path := "../../metta/gslt/lib/gslt_collection_occurrence_discovery.metta"
  text := false

input_file gsltCollectionOccurrenceSearchSource where
  path := "../../metta/gslt/lib/gslt_collection_occurrence_search.metta"
  text := false

lean_lib GSLTRuleExecutionQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram]
  needs := #[
    `@/gsltRuleExecutionSource,
    `@/gsltPremiseOperationsSource,
    `@/gsltScopedExecutionSource,
    `@/gsltTypedSitesSource,
    `@/gsltDescentExecutionSource,
    `@/gsltCompleteSource,
    `@/gsltCollectionLawsSource,
    `@/gsltCanonicalSource,
    `@/gsltCollectionSelectionSource,
    `@/gsltCollectionMachineSource,
    `@/gsltCollectionLoggedSearchSource,
    `@/gsltCollectionBackendSource,
    `@/gsltCollectionContextsSource,
    `@/gsltRecursiveCollectionSource,
    `@/gsltCollectionPresentationSource,
    `@/gsltCollectionHandoffSource,
    `@/gsltCollectionContinuationSource,
    `@/gsltCollectionOccurrencesSource,
    `@/gsltCollectionInstallSource,
    `@/gsltCollectionMatchLanesSource,
    `@/gsltCollectionCollectorSource,
    `@/gsltCollectionOccurrenceMachineSource,
    `@/gsltCollectionOccurrenceDiscoverySource,
    `@/gsltCollectionOccurrenceSearchSource,
    `@/gsltRunnerSource]

input_file gsltMatchNormalizedSource where
  path := "../../metta/gslt/lib/gslt_match_normalized.metta"
  text := false

lean_lib GSLTMatchNormalizedQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataNormalizedExecution]
  needs := #[`@/gsltMatchNormalizedSource]

input_file gsltEquationExecutionSource where
  path := "../../metta/gslt/lib/gslt_equation_execution.metta"
  text := false

lean_lib GSLTEquationExecutionQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationExecutionProgram]
  needs := #[`@/gsltEquationExecutionSource]

input_file gsltEquationContextsSource where
  path := "../../metta/gslt/lib/gslt_equation_contexts.metta"
  text := false

lean_lib GSLTEquationContextsQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationContextExecutionProgram]
  needs := #[`@/gsltEquationContextsSource]

input_file gsltModuleSource where
  path := "../../metta/gslt/lib/gslt_module.metta"
  text := false

input_file gsltSouffleDatalogSyntaxSource where
  path := "../../metta/gslt/module/gold/SouffleDatalog/Syntax.module"
  text := false

input_file gsltDatalogIRSource where
  path := "../../metta/gslt/module/DatalogIR.module"
  text := false

lean_lib GSLTDatalogIRQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR]
  needs := #[`@/gsltDatalogIRSource]

input_file gsltDatalogIRLookupSource where
  path := "../../metta/gslt/module/DatalogIRLookup.module"
  text := false

lean_lib GSLTDatalogIRLookupQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRLookup]
  needs := #[`@/gsltDatalogIRSource, `@/gsltDatalogIRLookupSource]

input_file gsltDatalogIRJoinSource where
  path := "../../metta/gslt/module/DatalogIRJoin.module"
  text := false

lean_lib GSLTDatalogIRJoinQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoin]
  needs := #[`@/gsltDatalogIRSource, `@/gsltDatalogIRLookupSource, `@/gsltDatalogIRJoinSource]

input_file gsltDatalogIRQuerySource where
  path := "../../metta/gslt/module/DatalogIRQuery.module"
  text := false

lean_lib GSLTDatalogIRQueryQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQuery]
  needs := #[`@/gsltDatalogIRSource, `@/gsltDatalogIRQuerySource]

input_file gsltSnapshotClosureSource where
  path := "../../metta/gslt/lib/gslt_snapshot_closure.metta"
  text := false

lean_lib GSLTSnapshotClosureQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution]
  needs := #[`@/gsltSnapshotClosureSource]

input_file gsltSouffleDatalogCoreSource where
  path := "../../metta/gslt/module/gold/SouffleDatalog/Core.module"
  text := false

input_file gsltSouffleDatalogKernelSource where
  path := "../../metta/gslt/module/gold/SouffleDatalog/GroundKernel.module"
  text := false

input_file gsltSouffleDatalogLanguageSource where
  path := "../../metta/gslt/module/gold/SouffleDatalog/Language.module"
  text := false

input_file gsltSouffleDatalogScalarSource where
  path := "../../metta/gslt/module/gold/SouffleDatalog/ScalarRealization.module"
  text := false

input_file gsltSouffleDatalogProjectionSource where
  path := "../../metta/gslt/module/gold/SouffleDatalog/ProgramProjection.module"
  text := false

lean_lib GSLTSouffleDatalogQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog]
  needs := #[`@/gsltSouffleDatalogSyntaxSource, `@/gsltSouffleDatalogCoreSource,
    `@/gsltSouffleDatalogKernelSource, `@/gsltSouffleDatalogLanguageSource]

input_file gsltGoldSourceLexical where
  path := "../../metta/gslt/module/gold/SourceLexical.module"
  text := false

input_file gsltOCamlSyntaxSource where
  path := "../../metta/gslt/module/gold/OCaml/Syntax.module"
  text := false

input_file gsltMaudeSyntaxSource where
  path := "../../metta/gslt/module/gold/Maude/Syntax.module"
  text := false

input_file gsltErlangSyntaxSource where
  path := "../../metta/gslt/module/gold/Erlang/Syntax.module"
  text := false

lean_lib GSLTGoldCoreSyntaxQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax]
  needs := #[`@/gsltGoldSourceLexical, `@/gsltOCamlSyntaxSource,
    `@/gsltMaudeSyntaxSource, `@/gsltErlangSyntaxSource]

input_file gsltOCamlIRSource where
  path := "../../metta/gslt/module/OCamlIR.module"
  text := false

input_file gsltOCamlMachineSource where
  path := "../../metta/gslt/module/OCamlMachine.module"
  text := false

lean_lib GSLTOCamlMachineQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlMachine]
  needs := #[`@/gsltOCamlIRSource, `@/gsltOCamlMachineSource, `@/gsltRadix16ModuleSource]

input_file gsltErlangDataSource where
  path := "../../metta/gslt/module/ErlangData.module"
  text := false

input_file gsltErlangMailboxSource where
  path := "../../metta/gslt/module/ErlangMailbox.module"
  text := false

lean_lib GSLTErlangMailboxQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox]
  needs := #[`@/gsltErlangDataSource, `@/gsltErlangMailboxSource, `@/gsltRadix16ModuleSource]

input_file gsltRadix16ModuleSource where
  path := "../../metta/gslt/module/Radix16.module"
  text := false

lean_lib GSLTRadix16Quotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16,
    `Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Scalar]
  needs := #[`@/gsltRadix16ModuleSource]

input_file gsltCHRIRSource where
  path := "../../metta/gslt/module/CHRIR.module"
  text := false

input_file gsltCHRProgramSource where
  path := "../../metta/gslt/module/CHRProgram.module"
  text := false

input_file gsltCHRKernelSource where
  path := "../../metta/gslt/module/CHRGroundKernel.module"
  text := false

input_file gsltCHRMatchSource where
  path := "../../metta/gslt/module/CHRMatch.module"
  text := false

lean_lib GSLTCHRProgramQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgram]
  needs := #[`@/gsltCHRIRSource, `@/gsltCHRProgramSource]

lean_lib GSLTCHRKernelQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRGroundKernel]
  needs := #[`@/gsltCHRIRSource, `@/gsltCHRKernelSource]

lean_lib GSLTCHRMatchQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuleCompilation]
  needs := #[`@/gsltCHRIRSource, `@/gsltCHRProgramSource, `@/gsltCHRMatchSource, `@/gsltRadix16ModuleSource]

input_file gsltIntegerSource where
  path := "../../metta/gslt/lib/gslt_integer.metta"
  text := false

input_file gsltCHRControllerSource where
  path := "../../metta/gslt/lib/gslt_chr.metta"
  text := false

lean_lib GSLTCHRControllerQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRControllerSource]
  needs := #[`@/gsltIntegerSource, `@/gsltCHRControllerSource]

lean_lib GSLTSouffleDatalogScalarQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogScalars]
  needs := #[`@/gsltSouffleDatalogScalarSource, `@/gsltRadix16ModuleSource]

lean_lib GSLTSouffleDatalogProjectionQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProgramProjection]
  needs := #[`@/gsltSouffleDatalogProjectionSource]

lean_lib GSLTModuleQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ModuleAssemblyExecution]
  needs := #[`@/gsltModuleSource]

input_file gsltTypedSitesSource where
  path := "../../metta/gslt/lib/gslt_typed_sites.metta"
  text := false

lean_lib GSLTTypedSitesQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution.Program]
  needs := #[`@/gsltTypedSitesSource]

input_file gsltRuleReadoutCacheSource where
  path := "../../metta/gslt/lib/gslt_rule_readout_cache.metta"
  text := false

lean_lib GSLTRuleReadoutCacheQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleReadoutCache]
  needs := #[`@/gsltRuleReadoutCacheSource]

input_file gsltExecutionDriverSource where
  path := "../../metta/gslt/lib/gslt_execution_driver.metta"
  text := false

lean_lib GSLTExecutionDriverQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleDriverExecution.Program]
  needs := #[`@/gsltExecutionDriverSource]

input_file gsltProgramDriverSource where
  path := "../../metta/gslt/lib/gslt_program_driver.metta"
  text := false

lean_lib GSLTProgramDriverQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramDriverExecution]
  needs := #[`@/gsltProgramDriverSource]

input_file gsltProgramResumptionSource where
  path := "../../metta/gslt/lib/gslt_program_resumption.metta"
  text := false

lean_lib GSLTProgramResumptionQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramResumptionExecution]
  needs := #[`@/gsltProgramResumptionSource]

input_file gsltRhoLexCanonicalSource where
  path := "../../metta/gslt/lib/gslt_rho_lex_canonical.metta"
  text := false

lean_lib GSLTRhoLexCanonicalQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoLexCanonicalExecution]
  needs := #[`@/gsltRhoLexCanonicalSource]

input_file gsltRhoRunnerSource where
  path := "../../metta/gslt/lib/gslt_rho_runner.metta"
  text := false

lean_lib GSLTRhoRunnerQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoRunnerExecution]
  needs := #[`@/gsltRhoRunnerSource]

input_file gsltLiveRunnerSource where
  path := "../../metta/gslt/lib/gslt_live_runner.metta"
  text := false

lean_lib GSLTLiveRunnerQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerExecution]
  needs := #[`@/gsltLiveRunnerSource]

input_file gsltDescentExecutionSource where
  path := "../../metta/gslt/lib/gslt_descent_execution.metta"
  text := false

input_file gsltCompleteSource where
  path := "../../metta/gslt/lib/gslt_complete.metta"
  text := false

lean_lib GSLTCompleteQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source]
  needs := #[`@/gsltDescentExecutionSource, `@/gsltCompleteSource]

input_file gsltCollectionLawsSource where
  path := "../../metta/gslt/lib/gslt_collection_laws.metta"
  text := false

input_file gsltCanonicalSource where
  path := "../../metta/gslt/lib/gslt_canonical.metta"
  text := false

input_file gsltInductiveAppendSource where
  path := "../../metta/gslt/lib/gslt_inductive_append.metta"
  text := false

input_file gsltIndexedNatVecAppendModule where
  path := "../../metta/gslt/module/IndexedNatVecAppend.module"
  text := false

lean_lib GSLTIndexedAppendSourceQuotation where
  roots := #[`Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSource]
  needs := #[`@/gsltIndexedNatVecAppendModule]

lean_lib GSLTInductiveAppendQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppendControls]
  needs := #[`@/gsltInductiveAppendSource]

input_file stableTopKSource where
  path := "../../metta/math/stable_top_k.metta"
  text := false

lean_lib StableTopKQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.StableTopK]
  needs := #[`@/stableTopKSource]

input_file gsltRunnerSource where
  path := "../../metta/gslt/lib/gslt_runner.metta"
  text := false

lean_lib GSLTLawsQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.LawsSource]
  needs := #[`@/gsltCollectionLawsSource]

lean_lib GSLTCanonicalQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CanonicalSource]
  needs := #[`@/gsltCanonicalSource]

lean_lib GSLTRunnerQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RunnerSource]
  needs := #[`@/gsltRunnerSource]

input_file gsltRhoNativeQueriesSource where
  path := "../../metta/gslt/lib/gslt_rho_native_queries.metta"
  text := false

lean_lib GSLTRhoNativeQueriesQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntimeSource]
  needs := #[`@/gsltRhoNativeQueriesSource]

input_file gsltNativeSpatialSource where
  path := "../../metta/gslt/lib/gslt_native_spatial.metta"
  text := false

lean_lib GSLTNativeSpatialQuotation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SpatialSource]
  needs := #[`@/gsltNativeSpatialSource]

input_file gsltInductiveObservationsSource where
  path := "../../metta/gslt/lib/gslt_inductive_observations.metta"
  text := false

lean_lib GSLTInductiveAppendObservation where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppend,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendControls,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecutionControls]
  needs := #[`@/gsltInductiveAppendSource, `@/gsltNativeSpatialSource,
    `@/gsltIndexedNatVecAppendModule, `@/gsltInductiveObservationsSource]

lean_lib GSLTInductiveAppendPolicy where
  roots := #[`Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppendPolicy]
  needs := #[`@/gsltInductiveAppendSource, `@/gsltIndexedNatVecAppendModule]

input_file gsltNativeNaturalCounterModule where
  path := "../../metta/gslt/module/NativeNaturalCounter.module"
  text := false

input_file gsltNativeFixedPointsSource where
  path := "../../metta/gslt/lib/gslt_native_fixed_points.metta"
  text := false

lean_lib GSLTInductiveM1Qualification where
  roots := #[`Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode,
    `Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSelectedTypingControls,
    `Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppendControls,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppendPolicy,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppendAnnotated,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendControls,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecutionControls,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.FiniteMuCalculusSource,
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.NaturalCounterExecution,
    `Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalHOL,
    `Mettapedia.Languages.HOLLight.NaturalFacts,
    `Mettapedia.Languages.MM0.NaturalRecursion,
    `Mettapedia.Languages.MM0.HOLTypeDefinitionBoundary,
    `Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMM0,
    `Mettapedia.Languages.Megalodon.NaturalClosure,
    `Mettapedia.Languages.Megalodon.NaturalRecursion,
    `Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalMegalodonProfile,
    `Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorCheckingProfiles,
    `Mettapedia.Languages.Megalodon.NativeSyntaxWire,
    `Mettapedia.GSLT.LanguageDef.IntegerRepresentationPublicationControls,
    `Mettapedia.OSLF.NativeTypes.Instances.Natural.RetainedCounterControls]
  needs := #[`@/gsltInductiveAppendSource, `@/gsltIndexedNatVecAppendModule,
    `@/gsltNativeSpatialSource, `@/gsltNativeNaturalCounterModule,
    `@/gsltNativeFixedPointsSource, `@/gsltInductiveObservationsSource]

-- Concrete MM2 execution examples are an explicit proof audit, not a
-- dependency of the routine language umbrellas or the default library.
lean_lib MetamathProofRegression where
  roots := #[`Mettapedia.Languages.Metamath.MM2AssembledNormalExecution]

-- Each quotation depends on its own retained source files. Editing an
-- unquoted frontend module does not invalidate the kernel quotation.
input_file mm0MeTTaDataSource where
  path := "../../metta/mm0/data.metta"
  text := true

input_file mm0MeTTaKernelSource where
  path := "../../metta/mm0/kernel.generated.metta"
  text := true

input_file mm0MeTTaServiceSource where
  path := "../../metta/mm0/service.metta"
  text := true

input_file mm0MeTTaStreamSource where
  path := "../../metta/mm0/stream.metta"
  text := true

input_file mm0MeTTaTextualSource where
  path := "../../metta/mm0/textual.metta"
  text := true

input_file mm0MeTTaMMUSource where
  path := "../../metta/mm0/mmu.metta"
  text := true

input_file mm0MeTTaMMBSource where
  path := "../../metta/mm0/mmb.metta"
  text := true

lean_lib MM0MeTTaQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Program]
  needs := #[`@/mm0MeTTaDataSource, `@/mm0MeTTaKernelSource,
    `@/mm0MeTTaServiceSource, `@/mm0MeTTaStreamSource]

lean_lib MM0TextualQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualExecution]
  needs := #[`@/mm0MeTTaTextualSource]

lean_lib MM0MMUQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Formats.MMU.MMUResolution]
  needs := #[`@/mm0MeTTaMMUSource]

-- The authored frontend quotation owns these exact inputs. Its proof
-- importers inherit changes through the ordinary module graph.
input_file mm0AuthoredGroundSource where
  path := "../../metta/mm0/syntax/shared/ground_relations_v1.metta"
  text := true

input_file mm0AuthoredPeTTaGroundSource where
  path := "../../metta/mm0/syntax/shared/cetta_petta_ground_relations_v1.metta"
  text := true

input_file mm0AuthoredFoldSource where
  path := "../../metta/mm0/syntax/source_fold_v1.metta"
  text := true

input_file mm0AuthoredSortSource where
  path := "../../metta/mm0/syntax/sort_environment_v1.metta"
  text := true

input_file mm0AuthoredTermSource where
  path := "../../metta/mm0/syntax/term_environment_v1.metta"
  text := true

input_file mm0AuthoredLexerSource where
  path := "../../metta/mm0/syntax/secondary_lexer_v1.metta"
  text := true

input_file mm0AuthoredNotationSource where
  path := "../../metta/mm0/syntax/notation_environment_v1.metta"
  text := true

input_file mm0AuthoredPrattSource where
  path := "../../metta/mm0/syntax/common/dynamic_pratt_v1.metta"
  text := true

input_file mm0AuthoredMathSource where
  path := "../../metta/mm0/syntax/math_parser_v1.metta"
  text := true

input_file mm0AuthoredExpressionSource where
  path := "../../metta/mm0/syntax/expression_environment_v1.metta"
  text := true

input_file mm0AuthoredAssertionSource where
  path := "../../metta/mm0/syntax/assertion_environment_v1.metta"
  text := true

lean_lib MM0TextualAuthoredQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualAuthoredSource]
  needs := #[
    `@/mm0AuthoredGroundSource,
    `@/mm0AuthoredPeTTaGroundSource,
    `@/mm0AuthoredFoldSource,
    `@/mm0AuthoredSortSource,
    `@/mm0AuthoredTermSource,
    `@/mm0AuthoredLexerSource,
    `@/mm0AuthoredNotationSource,
    `@/mm0AuthoredPrattSource,
    `@/mm0AuthoredMathSource,
    `@/mm0AuthoredExpressionSource,
    `@/mm0AuthoredAssertionSource]

input_file mm0AuthoredSyntaxSource where
  path := "../../metta/mm0/syntax/syntax_v1.metta"
  text := true

input_file mm0AuthoredParserPackSource where
  path := "../../metta/mm0/syntax/generated/parser_pack_v1.abi"
  text := true

lean_lib MM0ParserLinkageQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualParserLinkage]
  needs := #[`@/mm0AuthoredSyntaxSource, `@/mm0AuthoredParserPackSource]

lean_lib MM0MMBQuotation where
  roots := #[`Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBExecution]
  needs := #[`@/mm0MeTTaMMBSource]

lean_exe mettapedia where root := `Main

lean_exe metamathCheckerAudit where
  root := `Mettapedia.Languages.Metamath.DatabaseCheckerAudit

lean_exe checkRFC8259NativeForestExact where
  root := `Mettapedia.GSLT.Tools.CheckRFC8259NativeForestExact

lean_exe sumoNativeSourceCheck where
  root := `Mettapedia.Languages.SUMO.Native.SourceElaborationCheck

lean_exe pettaRun where
  root := `Mettapedia.Languages.MeTTa.PeTTa.Main

lean_exe holLightExportReplay where
  root := `scripts.check_hol_light_export

lean_exe rhoNativeCheck where
  root := `Mettapedia.Languages.ProcessCalculi.RhoCalculus.CheckNativeEvidence

lean_exe gsltNativeCheck where
  root := `Mettapedia.GSLT.LanguageDef.CheckGSLTILNative

lean_exe gsltRewriteCheck where
  root := `Mettapedia.GSLT.Tools.CheckRewriteRecipe

lean_exe gsltResourceHistoryCheck where
  root := `scripts.check_resource_history

lean_exe nativeInferenceCheck where
  root := `Mettapedia.Logic.CheckNativeInference

lean_exe nativeIndexedMachineFormationCheck where
  root := `scripts.check_native_indexed_machine_formation

lean_exe nativeAuthoredCubeCheck where
  root := `scripts.check_native_authored_cubes

lean_exe guardedAtomRuleCheck where
  root := `Mettapedia.Languages.GuardedAtomRule.CheckEvidence

lean_exe rhoNativeServices where
  root := `Mettapedia.Languages.ProcessCalculi.RhoCalculus.CheckScopedNativeServices

lean_exe authoredBindingEquations where
  root := `Mettapedia.GSLT.LanguageDef.CheckAuthoredBindingEquations

lean_exe authoredPremises where
  root := `Mettapedia.OSLF.MeTTaIL.CheckAuthoredPremises

lean_exe candidateBindingEquations where
  root := `Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CheckCandidateBindingEquations

lean_exe rhoCandidateServices where
  root := `Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.CheckCandidateServices

lean_exe oslf where
  root := `Mettapedia.OSLF.NativeTypes.Product.Main
  supportInterpreter := true

lean_exe sourceSyntax where
  root := `Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxMain
  supportInterpreter := true
