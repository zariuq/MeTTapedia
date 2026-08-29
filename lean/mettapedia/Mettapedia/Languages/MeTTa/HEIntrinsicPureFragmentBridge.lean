import Mettapedia.Languages.MeTTa.AbstractMachineBoundary
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaSound

/-!
# HE -> IntrinsicPure Fragment Bridge

This file records the current honest bridge between:

- HE/PeTTa-facing concrete syntax and runtime lanes,
- the MeTTa abstract-machine boundary,
- the Pure checking/kernel waist.

It is intentionally **fragmentary** rather than universal.

Positive example:
- closed Pure terms route to the Pure checking waist.
- HE atoms in the current `PureTranslatable` fragment have a shared artifact
  witness via `atomToPattern`.

Negative example:
- HE runtime rules are not reclassified as kernel certificates.
- the current `mettaPure` rewrite interface is not the direct `R_exec₀` runtime
  fragment.
-/

namespace Mettapedia.Languages.MeTTa.HEIntrinsicPureFragmentBridge

open Mettapedia.Languages.MeTTa.AbstractMachineBoundary
open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.Translation
open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Readiness gates for the current HE -> IntrinsicPure fragment bridge. -/
inductive HEIntrinsicPureGate where
  | artifactPatternWitness
  | abstractMachineBoundary
  | closedPureCheckingRoute
  | runtimeRuleRouting
  | directExecEquivalence
deriving DecidableEq, Repr

/-- Current gate status, pinned to the live repository state. -/
def heIntrinsicPureGateStatus : HEIntrinsicPureGate → Bool
  | .artifactPatternWitness => true
  | .abstractMachineBoundary => true
  | .closedPureCheckingRoute => true
  | .runtimeRuleRouting => true
  | .directExecEquivalence => false

theorem heIntrinsicPure_artifactPatternWitness_open :
    heIntrinsicPureGateStatus .artifactPatternWitness = true := rfl

theorem heIntrinsicPure_abstractMachineBoundary_open :
    heIntrinsicPureGateStatus .abstractMachineBoundary = true := rfl

theorem heIntrinsicPure_closedPureCheckingRoute_open :
    heIntrinsicPureGateStatus .closedPureCheckingRoute = true := rfl

theorem heIntrinsicPure_runtimeRuleRouting_open :
    heIntrinsicPureGateStatus .runtimeRuleRouting = true := rfl

theorem heIntrinsicPure_directExecEquivalence_not_open :
    heIntrinsicPureGateStatus .directExecEquivalence = false := rfl

/-- Phase order for growing the HE -> IntrinsicPure bridge without collapsing the
runtime/pure distinction. -/
def heIntrinsicPurePhaseOrder : List String :=
  [ "freeze the abstract-machine lane split as authoritative"
  , "treat PureTranslatable only as an artifact/pattern witness"
  , "route closed Pure source terms through the Pure checking waist"
  , "keep HE runtime rules and queries on the runtime-exec lane"
  , "only after explicit typed translation should stronger HE->Pure claims open"
  , "only after that reconsider direct runtime equivalence claims" ]

/-- Explicit anti-drift prohibitions for this bridge. -/
def heIntrinsicPureForbiddenMoves : List String :=
  [ "do not treat PureTranslatable as a typing theorem into IntrinsicPure"
  , "do not reclassify HE runtime rules as kernel certificates"
  , "do not claim current mettaPure rewrites fit the direct R_exec₀ bridge"
  , "do not collapse query support and exec authority into one backend claim" ]

/-- Contract object for the current HE -> Pure fragment bridge. -/
structure HEIntrinsicPureFragmentContract where
  gateStatus : HEIntrinsicPureGate → Bool
  phaseOrder : List String
  forbiddenMoves : List String
  checkingRegion : ElaboratedRegion
  checkingOverlap : OverlapClass

noncomputable def heIntrinsicPureFragmentContract : HEIntrinsicPureFragmentContract :=
  { gateStatus := heIntrinsicPureGateStatus
    phaseOrder := heIntrinsicPurePhaseOrder
    forbiddenMoves := heIntrinsicPureForbiddenMoves
    checkingRegion := mettaAbstractMachineBoundary.checkingBoundary.region
    checkingOverlap := mettaAbstractMachineBoundary.checkingBoundary.overlapClass }

theorem heIntrinsicPureFragmentContract_region :
    heIntrinsicPureFragmentContract.checkingRegion = ElaboratedRegion.pureKernelRegion := by
  simp [heIntrinsicPureFragmentContract, checkingBoundary_region]

theorem heIntrinsicPureFragmentContract_overlap :
    heIntrinsicPureFragmentContract.checkingOverlap = OverlapClass.artifactOnly := by
  simp [heIntrinsicPureFragmentContract, checkingBoundary_overlap]

theorem heIntrinsicPurePhaseOrder_starts_with_lane_freeze :
    heIntrinsicPurePhaseOrder.head? =
      some "freeze the abstract-machine lane split as authoritative" := rfl

theorem heIntrinsicPure_forbids_runtime_reclassification :
    "do not reclassify HE runtime rules as kernel certificates" ∈
      heIntrinsicPureForbiddenMoves := by
  simp [heIntrinsicPureForbiddenMoves]

/-! ## Live fragment witnesses -/

theorem pureTranslatable_has_patternWitness
    (a : Atom) (h : PureTranslatable a) :
    ∃ p, atomToPattern a = some p := by
  exact translatable_witness a (PureTranslatable.toTranslatable h)

theorem pureClosedSyntax_uses_kernelCertificateLane (term : PureSyntaxTerm 0) :
    SyntaxNode.abstractMachineLane (SyntaxNode.pureClosedSyntax term) =
      AbstractMachineLane.kernelCertificateLane := by
  exact (pureClosedSyntax_routes_to_checking_boundary term).1

theorem pureClosedSyntax_region_is_pureKernel (term : PureSyntaxTerm 0) :
    ElaboratedNode.region (elaborate (SyntaxNode.pureClosedSyntax term)) =
      ElaboratedRegion.pureKernelRegion := by
  exact elaborate_pureClosedSyntax_region term

theorem heRuntimeRule_uses_runtimeRuleLane (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.heRuntimeRule pattern) =
      AbstractMachineLane.runtimeRuleLane := by
  exact (heRuntimeRule_routes_to_exec_backend pattern).1

theorem heRuntimeRule_region_is_runtimeExec (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SyntaxNode.heRuntimeRule pattern)) =
      ElaboratedRegion.runtimeExecRegion := by
  exact elaborate_heRuntimeRule_region pattern

theorem heRuntimeQuery_uses_runtimeQueryLane (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.heRuntimeQuery pattern) =
      AbstractMachineLane.runtimeQueryLane := by
  exact (heRuntimeQuery_routes_to_query_backend pattern).1

theorem heRuntimeRule_not_kernelCertificateLane (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.heRuntimeRule pattern) ≠
      AbstractMachineLane.kernelCertificateLane := by
  simp [SyntaxNode.abstractMachineLane]

theorem pettaRuntimeRule_not_kernelCertificateLane (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.pettaRuntimeRule pattern) ≠
      AbstractMachineLane.kernelCertificateLane := by
  simp [SyntaxNode.abstractMachineLane]

theorem pettaRuntimeQuery_uses_runtimeQueryLane (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.pettaRuntimeQuery pattern) =
      AbstractMachineLane.runtimeQueryLane := by
  exact (pettaRuntimeQuery_routes_to_query_backend pattern).1

theorem heRuntimeQuery_not_runtimeRuleLane (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.heRuntimeQuery pattern) ≠
      AbstractMachineLane.runtimeRuleLane := by
  simp [SyntaxNode.abstractMachineLane]

theorem pettaRuntimeQuery_not_runtimeRuleLane (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.pettaRuntimeQuery pattern) ≠
      AbstractMachineLane.runtimeRuleLane := by
  simp [SyntaxNode.abstractMachineLane]

theorem mettaPure_current_frontier_not_directExec0
    (r : RewriteRule)
    (hr : r ∈ Mettapedia.Languages.MeTTa.Pure.Core.mettaPure.rewrites) :
    ¬ ∃ x, r.left = .fvar x ∧
      Mettapedia.Languages.ProcessCalculi.MORK.morkTranslatable r.right = true := by
  exact kernel_lane_not_direct_runtimeExec0 r hr

end Mettapedia.Languages.MeTTa.HEIntrinsicPureFragmentBridge
