import Mettapedia.Languages.MeTTa.PeTTa.Answers
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
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
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.ExecutableBoundary
import Mettapedia.Languages.MeTTa.PeTTa.SemanticForms
import Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge
import Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance
import Mettapedia.Languages.MeTTa.PeTTa.GSLTVertex
import Mettapedia.Languages.MeTTa.PeTTa.LookupPlan
import Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.PeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIR
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIRV2
import Mettapedia.Languages.MeTTa.PeTTa.Artifacts
import Mettapedia.Languages.MeTTa.PeTTa.CoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension
import Mettapedia.Languages.MeTTa.PeTTa.Unit
import Mettapedia.Languages.MeTTa.PeTTa.StageIndex
import Mettapedia.Languages.MeTTa.PeTTa.OSLFPackage
import Mettapedia.Languages.MeTTa.PeTTa.StageFiber
import Mettapedia.Languages.MeTTa.PeTTa.BoundaryContract
import Mettapedia.Languages.MeTTa.PeTTa.SemanticBundle
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

/-!
# PeTTa MeTTa Semantics

Public import interface for the PeTTa semantic stack.

## Semantic Layers

- `DeclarativeSpec` — readable declarative expression and command semantics
- `MinimalInstructions` — operational instruction semantics
- `ExecutableBoundary` — implementation-facing executable boundary artifacts
- `SemanticForms` — named public facade over the major semantic layers
- `SemanticBundle` — canonical stage-indexed semantic object for runtime/proof
                    alignment

Positive example:
- PeTTa now exposes a clear declarative layer and a separate executable
  boundary layer, instead of burying everything in contract internals.

Negative example:
- the executable boundary does not replace the declarative meaning of PeTTa
  programs; it refines how the live runtime is organized.
-/
