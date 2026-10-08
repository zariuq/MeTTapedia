import Mettapedia.Languages.MeTTa.PeTTa.Answers
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Answers
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Space
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Commands
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.OperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef
import Mettapedia.Languages.MeTTa.PeTTa.UpstreamAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.DispatchCoverage
import Mettapedia.Languages.MeTTa.PeTTa.BodyClosureFusion
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.Languages.MeTTa.PeTTa.FunctionFreeLPBridge
import Mettapedia.Languages.MeTTa.PeTTa.Effects
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystem
import Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
import Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTLayers
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDeterminism
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDecision
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTComposition
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTPlan
import Mettapedia.Languages.MeTTa.PeTTa.TypedOperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.TypedEval
import Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval
import Mettapedia.Languages.MeTTa.PeTTa.StdLib
import Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle
import Mettapedia.Languages.MeTTa.PeTTa.PrologBridge
import Mettapedia.Languages.MeTTa.PeTTa.TranslateExpr
import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences
import Mettapedia.Languages.MeTTa.PeTTa.BindingForms
import Mettapedia.Languages.MeTTa.PeTTa.ExplicitEvaluation
import Mettapedia.Languages.MeTTa.PeTTa.CallGuardOptimization
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
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardWire
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTyped
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTypedOperational
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileBindingCoverage
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileFormationSemantics
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileGuardedContextSemantics
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileOccurrenceInstantiation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSemanticComposite
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardResumableControl
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControlNTT
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredC
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredCSemantics
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardMatchMachinePass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCTotalRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHotStructuredCPass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteSourceDerivedStructuredC
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTransitionProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecutePatternMatrixCompilation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteRulePlanCompilation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteFusedDecisionProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteMatchMachinePass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCPass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedInvocationRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardConformanceCorpus
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport

/-!
# PeTTa

Public import interface for the PeTTa formalization.

## Semantics of PeTTa programs

- `SpaceSemantics`, `Effects`, `StdLib`: reading, programs, ordered selection,
  named spaces, cells and primitives over `OSLFCore.Atom`.
- `Answers`: ordered Atom values, preserving duplicate occurrences.
- `DeclarativeSpec`: independent transitions and finite whole-program judgments.
- `Eval`: the executable machine, its adequacy theorem and execution laws.
- `OperationalGSLT`: the judgment as an OSLF-generating GSLT, with executable
  correspondence and observation laws.

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
