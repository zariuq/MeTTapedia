import Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping
import Mettapedia.Languages.MeTTa.PeTTa.TableReuse
import Mettapedia.Languages.MeTTa.PeTTa.Answers
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.MeTTa.PeTTa.LibTransform
import Mettapedia.Languages.MeTTa.PeTTa.LibTransformControls
import Mettapedia.Languages.MeTTa.PeTTa.LibTransformQuery
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Answers
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Space
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Commands
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.OperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.FaultObservation
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef
import Mettapedia.Languages.MeTTa.PeTTa.UpstreamAgreement
import Mettapedia.Languages.MeTTa.PeTTa.PythonTextBoundary
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataNormalizedExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ModuleAssemblyExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationContextExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleDriverExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramDriverExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramResumptionExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerPartrec
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoCanonicalEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoLexCanonicalExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoRunnerExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes
import Mettapedia.Languages.MeTTa.PeTTa.DispatchCoverage
import Mettapedia.Languages.MeTTa.PeTTa.BodyClosureFusion
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.Languages.MeTTa.PeTTa.FunctionFreeLPBridge
import Mettapedia.Languages.MeTTa.PeTTa.Effects
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystem
import Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval
import Mettapedia.Languages.MeTTa.PeTTa.StdLib
import Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle
import Mettapedia.Languages.MeTTa.PeTTa.PrologBridge
import Mettapedia.Languages.MeTTa.PeTTa.TranslateExpr
import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences
import Mettapedia.Languages.MeTTa.PeTTa.BindingForms
import Mettapedia.Languages.MeTTa.PeTTa.ExplicitEvaluation
import Mettapedia.Languages.MeTTa.PeTTa.CallArityDispatch
import Mettapedia.Languages.MeTTa.PeTTa.MainlineGroundProvider
import Mettapedia.Languages.MeTTa.PeTTa.DispatchErrorScope
import Mettapedia.Languages.MeTTa.PeTTa.RaiseFree
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.SemanticForms
import Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge
import Mettapedia.Languages.MeTTa.PeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIR
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIRV2
import Mettapedia.Languages.MeTTa.PeTTa.CoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension

/-!
# PeTTa

Public import interface for the PeTTa formalization.

The maintained predicate-typing foundation is `RuntimeTyping`. Historical typing
profiles and static-checker/code-generation studies have the explicit umbrella
`PeTTa.TypingResearch`; the wider language catalogue imports them separately.

## Semantics of PeTTa programs

- `SpaceSemantics`, `Effects`, `StdLib`: reading, programs, ordered selection,
  named spaces, cells and primitives over `OSLFCore.Atom`.
- `Answers`: ordered Atom values, preserving duplicate occurrences.
- `LibTransform`: the laws of the PeTTa transform library (`lib_transform_specs`) over
  ordered stores, structural one-way matching and sequential search with a global store.
  A proposal is the guide of a kernel match, the atoms it matched; a branch fires its
  guided sources, so its absences, unique counts and collections are those of the store
  when it fires. Reads alone answer as `match` does, one firing takes exactly its
  footprint's takes, the branches are the fold of single firings, `once` fires the first
  proposal that holds, and `all`/`collect` takes consume every match in one firing.
  `absent`, `unique` and `collect` of a conjunction range over its joint matches: absent
  holds iff there is none, unique fires on the one tuple with its parts as footprint,
  and a take-mode collect keeps the tuples that fit their stored copies and takes every
  copy of each participating atom.
  `LibTransformQuery` states reads alone against `SpaceSemantics.query`;
  `LibTransformControls` has the positive and negative controls.
- `DeclarativeSpec`: independent transitions and finite whole-program judgments.
- `Eval`: the executable machine, its adequacy theorem and execution laws.
- `OperationalGSLT`: the judgment as an OSLF-generating GSLT, with executable
  correspondence and observation laws.
- `Bridges.MeTTaIL.MatchAutomataExecution`: both retained-source matcher entries
  compute the exact canonical first-order matches, including occurrence order,
  bindings and source inspection counters. Root rule execution, equations and
  contextual permissions remain separate from matching.
- `Bridges.MeTTaIL.MatchAutomataNormalizedExecution`: the optional source
  partitions and rebases derivative obligations, interns shared controls and
  expands them back into their original ordered occurrences. Its full matcher
  result agrees with canonical matching, with exact completed state and I/O.
- `Bridges.MeTTaIL.RuleInstantiationExecution`: the retained rule source
  constructs the full canonical Pattern RHS with exact substitution, retained
  binders, canonical explicit substitution and checked collection-rest splicing.
  Captured replacement values remain opaque. Local scoped capture, validated
  recovery and assignment operations retain dependency and ambient metadata;
  declaration-site admission and rewrite permission remain separate.
- `Bridges.MeTTaIL.RelationPremiseExecution`: actual queries and their ordered
  fold retain preceding bindings, canonical merge order and duplicate witnesses.
- `Bridges.MeTTaIL.RootRuleExecution`: actual ordered root execution reflects
  exactly to GSLT steps for admitted equation-free first-order rules with
  relation-query premises and a literal finite provider; a child match does
  not authorize a child rewrite. Both matcher strategies feed the actual
  guarded entry, retaining physical rule and premise-witness occurrences.
- `Bridges.MeTTaIL.RuleTraceExecution`: a receipt-driven source loop computes
  each complete ordered frontier, selects a physical occurrence, and re-enters
  the rules. Its whole-run characterization retains residuals, unread receipts,
  stopping, refusal and fuel exhaustion, with exact store and I/O observations.
- `Bridges.MeTTaIL.ContextualRuleExecution`: both retained matcher strategies
  implement canonical recursive congruence, relation-query and freshness premises, with
  exact completed frontiers and preservation/reflection to actual GSLT steps.
  Freshness uses the preceding branch's bindings and retains authored guard
  order. Scoped and quantified premise profiles remain separate extensions.
- `Bridges.MeTTaIL.ModuleAssemblyExecution`: the source assembles all four
  declaration families in order. Explicit coherent-origin and structural-view
  imports keep the first identical declaration and refuse conflicts. Body rule
  occurrences remain ordered, including duplicates. Checked imports compose
  with contextual execution and the actual assembled language's GSLT step.
- `Bridges.MeTTaIL.PremiseOperationsExecution`: canonical free-variable and
  freshness operations cover the full Pattern carrier, including binder
  metadata and collections. Name resolution retains the first binding and
  refuses non-name replacements. The freshness step has exact completed
  observations and is used by the shared contextual premise dispatcher.
- `Bridges.MeTTaIL.EquationExecution`: physical equation receipts retain
  direction, initial captures, ordered query occurrences, final captures and
  target. Validation reflects to the canonical equation relation. Equations
  remain distinct from rewrite permissions and normalization policy.
- `Bridges.MeTTaIL.EquationContextExecution`: exact physical positions select
  and replace canonical contexts. Retained-source receipt validation and path
  replay preserve equation witnesses and reflect to canonical equivalence;
  supplied reverse predecessors recheck the original forward equation and its
  current endpoint. Checked paths compose before and after the actual rule
  frontier, with exact witnessed observations and original-GSLT soundness.
  Neither receipt acceptance nor structural traversal grants rewrite authority.
- `Bridges.MeTTaIL.GeneralRuleJobExecution`: the complete original scoped
  matcher, conditional premise machine and authorized receipt readout for
  finite typed presentations. Actual bounded execution retains pending work,
  lexical quantifiers, finite providers, physical unordered choices, captured
  dependencies and ordered duplicate answers. Machine execution followed by
  receipt readout preserves and reflects the original authorized receipts;
  completeness uses the original declaration-stratification check.
- `Bridges.MeTTaIL.GeneralRuleDriverExecution`: actual MeTTa operations advance
  and resume the original job scheduler, retaining pending obligations,
  physical answer cursors, ordered receipts and the original work account.
- `Bridges.MeTTaIL.GeneralProgramDriverExecution`: native typed occurrence
  generation selects the original jobs from presentation data, then the
  authored driver runs and joins them in order. Saturated, stratified,
  equation-free execution preserves and reflects the original source GSLT
  successors. Independently observed target output families retain receipt
  ordinals and full evidence, supporting native membership and universal
  properties of returned successors. A proved pure readout cache reuses
  replacement checks while reconstructing each current receipt. Effectful
  providers, general equation profiles and broader modal transport remain
  separate integrations.
- `Bridges.MeTTaIL.GeneralProgramResumptionExecution`: a program run keeps
  every job's machine state. The authored resumption continues each retained
  machine, so resuming the driver's observation gives the driver's observation
  with the added budgets. The authored publication releases complete jobs in
  order and stops at the first job that is not complete; what it prints grows
  by prefix under every resumption. The shared publication cursor delivers
  only that prefix's new occurrences; splitting a budget preserves their
  complete ordered delivery and absolute ordinals.
- `Bridges.MeTTaIL.GeneralLiveRunnerExecution`: whole runs of any admitted
  plan. A machine keeps the retained run of its state; a tick adds work and
  resumes it, then commits the first released receipt and begins a search at
  its target, or stops. For an equation-free, stratified plan every reached
  machine's states form a reduction sequence of the plan's GSLT from the source,
  every receipt is kept whole, and a normal ending means the state has no step.
  Every state gets its own environment, so open terms run too. The theorems
  hold for every number of ticks; none assumes that the program terminates.
- `Bridges.MeTTaIL.GeneralLiveRunnerPartrec`: the live runner on the
  partial-recursive machine. Started at a code and an input, it ends normally
  at `Halt w` for some page exactly when `w` is Mathlib's evaluation of the
  code on the input, and it keeps running for every page when the code
  diverges.
- `Bridges.MeTTaIL.GeneralLiveRunnerEmission`: the emitter. An admitted,
  equation-free, stratified plan becomes a MeTTa module with `name:begin` and
  `name:run` entries, or a refusal with its reason. The PeTTa run of every
  emitted module's entries is the live runner's model, and the shared source
  reader reads the emitted text back as exactly that module
  (`ReadAfterRender`: lexer, token parser, token reader and scanner, each
  proved against the rendering).
- `Bridges.MeTTaIL.CompleteExecution`: the complete machine
  (`gslt_descent_execution.metta`, `gslt_complete.metta`) proved head by head
  against `OSLF/MeTTaIL/Complete`: scheduled descent, fair rule jobs, equation
  lanes, steps modulo equations, canonical forms (`gslt_canonical.metta`:
  comparison field by field with a name table, insertion sort), the runner
  over them and fair exploration of every run. Every reached search stays
  within the plan's declared footprint.
- `Bridges.MeTTaIL.CompleteEmissionExecution`: modules emitted for the complete
  machine run their language. For every footprinted plan the emitter accepts
  (every compiled plan it accepts is), the PeTTa runs of `name:run` and
  `name:explore` print the runner's trace and the explored states of the model.
  A module that commits canonical forms explores the presented GSLT wherever
  its canonical explorer is complete; the emitted rho module does
  (`RhoCanonicalEmission.rho_emitted_explores`).
- `Bridges.MeTTaIL.RhoLexCanonicalExecution`: the authored rho canonicalizer
  computes the lexicographic canonical form of every closed rho process: its
  serializer, comparator, insertion sort, bag splicing, unit removal, collapse
  and name equation each compute their Lean counterparts.
- `Bridges.MeTTaIL.RhoRunnerExecution`: the authored rho runner on the driver,
  its resumption and the canonicalizer. Its trace starts at the canonical form;
  each state reaches the next by a depth-one rho step followed by the
  canonical form; it reports quiescence only where no rho step is left at any
  depth. A retained `RhoSearch` continues one pending COMM search through
  `rho:run:resume-search`, keeping its canonical process and full program
  observation. This operation does not itself consume a receipt or enforce
  exclusive ownership of the search.

## Selected Pattern rewrite view

`PatternRewrite.Answers`, `PatternRewrite.Space`, `PatternRewrite.Commands` and
`PatternRewrite.OperationalGSLT`, together with `PatternRewrite.DeclarativeSpec`,
`MeTTaEval`, `TypedEval` and `MinimalInstructions`, state
one-step rewrite and query relations over `Pattern`. A selected right-hand
side is not a completed program answer. These relations remain for their
downstream users.

## Retired modules

The March 2026 stage-indexed OSLF and artifact-export route (`OSLFInstance`,
`GSLTVertex`, `StageIndex`, `OSLFPackage`, `StageFiber`, `SemanticBundle`,
`ArtifactBundle`, `ContractCatalog`, `ContractExport`, `BoundaryContract`,
`ExecutableBoundary`, `ExecutionContract`, `Artifacts`, `Unit`, `LookupPlan`),
with `Conformance.PeTTaArtifactBridge` and its export scripts, is in
`_archive/petta-retirement-2026-10-05`. Its OSLF was built from user rewrite
rules only. The rule-only OSLF is `langOSLF (pettaSpaceToLangDef s) "Expr"`
from the framework; its LP soundness theorem is `petta_safe_space_ruleApp_lp_sound`
in `LPSoundness`; its modal laws are the framework's generic ones; the lookup
plan is `Algorithms.MeTTa.LookupPlans`; the shared-variable `spaceMatch`
checks are examples in `PatternRewrite.Space`.
-/
