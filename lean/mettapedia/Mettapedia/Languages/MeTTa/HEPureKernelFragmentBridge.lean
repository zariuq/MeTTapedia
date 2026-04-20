import Mettapedia.Languages.MeTTa.AbstractMachineBoundary
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaSound

/-!
# HE -> PureKernel Fragment Bridge

This file records the current honest bridge between:

- HE/PeTTa-facing surface syntax and runtime lanes,
- the MeTTa abstract-machine boundary,
- the Pure checking/kernel waist.

It is intentionally **fragmentary** rather than universal.

Positive example:
- closed Pure terms route to the Pure checking waist.
- HE atoms in the current `PureTranslatable` fragment have a shared artifact
  witness via `atomToPattern`.

Negative example:
- HE runtime rules are not reclassified as kernel certificates.
- the current `mettaPure` rewrite surface is not the direct `R_exec₀` runtime
  fragment.
-/

namespace Mettapedia.Languages.MeTTa.HEPureKernelFragmentBridge

open Mettapedia.Languages.MeTTa.AbstractMachineBoundary
open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.Translation
open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Readiness gates for the current HE -> PureKernel fragment bridge. -/
inductive HEPureKernelGate where
  | artifactPatternWitness
  | abstractMachineBoundary
  | closedPureCheckingRoute
  | runtimeRuleRouting
  | directExecEquivalence
deriving DecidableEq, Repr

/-- Current gate status, pinned to the live repository state. -/
def hePureKernelGateStatus : HEPureKernelGate → Bool
  | .artifactPatternWitness => true
  | .abstractMachineBoundary => true
  | .closedPureCheckingRoute => true
  | .runtimeRuleRouting => true
  | .directExecEquivalence => false

theorem hePureKernel_artifactPatternWitness_open :
    hePureKernelGateStatus .artifactPatternWitness = true := rfl

theorem hePureKernel_abstractMachineBoundary_open :
    hePureKernelGateStatus .abstractMachineBoundary = true := rfl

theorem hePureKernel_closedPureCheckingRoute_open :
    hePureKernelGateStatus .closedPureCheckingRoute = true := rfl

theorem hePureKernel_runtimeRuleRouting_open :
    hePureKernelGateStatus .runtimeRuleRouting = true := rfl

theorem hePureKernel_directExecEquivalence_not_open :
    hePureKernelGateStatus .directExecEquivalence = false := rfl

/-- Phase order for growing the HE -> PureKernel bridge without collapsing the
runtime/pure distinction. -/
def hePureKernelPhaseOrder : List String :=
  [ "freeze the abstract-machine lane split as authoritative"
  , "treat PureTranslatable only as an artifact/pattern witness"
  , "route closed Pure surface terms through the Pure checking waist"
  , "keep HE runtime rules and queries on the runtime-exec lane"
  , "only after explicit typed translation should stronger HE->Pure claims open"
  , "only after that reconsider direct runtime equivalence claims" ]

/-- Explicit anti-drift prohibitions for this bridge. -/
def hePureKernelForbiddenMoves : List String :=
  [ "do not treat PureTranslatable as a typing theorem into PureKernel"
  , "do not reclassify HE runtime rules as kernel certificates"
  , "do not claim current mettaPure rewrites fit the direct R_exec₀ bridge"
  , "do not collapse query support and exec authority into one backend claim" ]

/-- Contract object for the current HE -> Pure fragment bridge. -/
structure HEPureKernelFragmentContract where
  gateStatus : HEPureKernelGate → Bool
  phaseOrder : List String
  forbiddenMoves : List String
  checkingRegion : ElaboratedRegion
  checkingOverlap : OverlapClass

noncomputable def hePureKernelFragmentContract : HEPureKernelFragmentContract :=
  { gateStatus := hePureKernelGateStatus
    phaseOrder := hePureKernelPhaseOrder
    forbiddenMoves := hePureKernelForbiddenMoves
    checkingRegion := mettaAbstractMachineBoundary.checkingBoundary.region
    checkingOverlap := mettaAbstractMachineBoundary.checkingBoundary.overlapClass }

theorem hePureKernelFragmentContract_region :
    hePureKernelFragmentContract.checkingRegion = ElaboratedRegion.pureKernelRegion := by
  simp [hePureKernelFragmentContract, checkingBoundary_region]

theorem hePureKernelFragmentContract_overlap :
    hePureKernelFragmentContract.checkingOverlap = OverlapClass.artifactOnly := by
  simp [hePureKernelFragmentContract, checkingBoundary_overlap]

theorem hePureKernelPhaseOrder_starts_with_lane_freeze :
    hePureKernelPhaseOrder.head? =
      some "freeze the abstract-machine lane split as authoritative" := rfl

theorem hePureKernel_forbids_runtime_reclassification :
    "do not reclassify HE runtime rules as kernel certificates" ∈
      hePureKernelForbiddenMoves := by
  simp [hePureKernelForbiddenMoves]

/-! ## Live fragment witnesses -/

theorem pureTranslatable_has_patternWitness
    (a : Atom) (h : PureTranslatable a) :
    ∃ p, atomToPattern a = some p := by
  exact translatable_witness a (PureTranslatable.toTranslatable h)

theorem surfacePureClosed_uses_kernelCertificateLane (term : SurfacePureTm 0) :
    SurfaceNode.abstractMachineLane (SurfaceNode.surfacePureClosed term) =
      AbstractMachineLane.kernelCertificateLane := by
  exact (surfacePureClosed_routes_to_checking_boundary term).1

theorem surfacePureClosed_region_is_pureKernel (term : SurfacePureTm 0) :
    ElaboratedNode.region (elaborate (SurfaceNode.surfacePureClosed term)) =
      ElaboratedRegion.pureKernelRegion := by
  exact elaborate_surfacePureClosed_region term

theorem heRuntimeRule_uses_runtimeRuleLane (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.heRuntimeRule pattern) =
      AbstractMachineLane.runtimeRuleLane := by
  exact (heRuntimeRule_routes_to_exec_backend pattern).1

theorem heRuntimeRule_region_is_runtimeExec (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SurfaceNode.heRuntimeRule pattern)) =
      ElaboratedRegion.runtimeExecRegion := by
  exact elaborate_heRuntimeRule_region pattern

theorem heRuntimeQuery_uses_runtimeQueryLane (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.heRuntimeQuery pattern) =
      AbstractMachineLane.runtimeQueryLane := by
  exact (heRuntimeQuery_routes_to_query_backend pattern).1

theorem heRuntimeRule_not_kernelCertificateLane (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.heRuntimeRule pattern) ≠
      AbstractMachineLane.kernelCertificateLane := by
  simp [SurfaceNode.abstractMachineLane]

theorem pettaRuntimeRule_not_kernelCertificateLane (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.pettaRuntimeRule pattern) ≠
      AbstractMachineLane.kernelCertificateLane := by
  simp [SurfaceNode.abstractMachineLane]

theorem pettaRuntimeQuery_uses_runtimeQueryLane (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.pettaRuntimeQuery pattern) =
      AbstractMachineLane.runtimeQueryLane := by
  exact (pettaRuntimeQuery_routes_to_query_backend pattern).1

theorem heRuntimeQuery_not_runtimeRuleLane (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.heRuntimeQuery pattern) ≠
      AbstractMachineLane.runtimeRuleLane := by
  simp [SurfaceNode.abstractMachineLane]

theorem pettaRuntimeQuery_not_runtimeRuleLane (pattern : Pattern) :
    SurfaceNode.abstractMachineLane (SurfaceNode.pettaRuntimeQuery pattern) ≠
      AbstractMachineLane.runtimeRuleLane := by
  simp [SurfaceNode.abstractMachineLane]

theorem mettaPure_current_frontier_not_directExec0
    (r : RewriteRule)
    (hr : r ∈ Mettapedia.Languages.MeTTa.Pure.Core.mettaPure.rewrites) :
    ¬ ∃ x, r.left = .fvar x ∧
      Mettapedia.Languages.ProcessCalculi.MORK.morkTranslatable r.right = true := by
  exact kernel_lane_not_direct_runtimeExec0 r hr

end Mettapedia.Languages.MeTTa.HEPureKernelFragmentBridge
