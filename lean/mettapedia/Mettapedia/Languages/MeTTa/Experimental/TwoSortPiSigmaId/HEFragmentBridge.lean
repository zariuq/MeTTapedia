import Mettapedia.Languages.MeTTa.AbstractMachineBoundary
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaSound

/-!
# HE -> TwoSortPiSigmaId Fragment Bridge

This file records the current honest bridge between:

- HE/PeTTa-facing concrete syntax and runtime lanes,
- the MeTTa abstract-machine boundary,
- the two-sort checking/kernel waist.

It is intentionally **fragmentary** rather than universal.

Positive example:
- closed two-sort terms route to the two-sort checking waist.
- HE atoms in the current `TwoSortTranslatable` fragment have a shared artifact
  witness via `atomToPattern`.

Negative example:
- HE runtime rules are not reclassified as kernel certificates.
- the current `twoSortDependent` rewrite interface is not the direct `R_exec₀` runtime
  fragment.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.HEFragmentBridge

open Mettapedia.Languages.MeTTa.AbstractMachineBoundary
open Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services
open Mettapedia.Languages.MeTTa.Translation
open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Readiness gates for the current HE -> TwoSortPiSigmaId fragment bridge. -/
inductive HETwoSortPiSigmaIdGate where
  | artifactPatternWitness
  | abstractMachineBoundary
  | closedTwoSortCheckingRoute
  | runtimeRuleRouting
  | directExecEquivalence
deriving DecidableEq, Repr

/-- Current gate status, pinned to the live repository state. -/
def heTwoSortPiSigmaIdGateStatus : HETwoSortPiSigmaIdGate → Bool
  | .artifactPatternWitness => true
  | .abstractMachineBoundary => true
  | .closedTwoSortCheckingRoute => true
  | .runtimeRuleRouting => true
  | .directExecEquivalence => false

theorem heTwoSortPiSigmaId_artifactPatternWitness_open :
    heTwoSortPiSigmaIdGateStatus .artifactPatternWitness = true := rfl

theorem heTwoSortPiSigmaId_abstractMachineBoundary_open :
    heTwoSortPiSigmaIdGateStatus .abstractMachineBoundary = true := rfl

theorem heTwoSortPiSigmaId_closedTwoSortCheckingRoute_open :
    heTwoSortPiSigmaIdGateStatus .closedTwoSortCheckingRoute = true := rfl

theorem heTwoSortPiSigmaId_runtimeRuleRouting_open :
    heTwoSortPiSigmaIdGateStatus .runtimeRuleRouting = true := rfl

theorem heTwoSortPiSigmaId_directExecEquivalence_not_open :
    heTwoSortPiSigmaIdGateStatus .directExecEquivalence = false := rfl

/-- Phase order for growing the HE -> TwoSortPiSigmaId bridge without collapsing the
runtime/two-sort-fragment distinction. -/
def heTwoSortPiSigmaIdPhaseOrder : List String :=
  [ "freeze the abstract-machine lane split as authoritative"
  , "treat TwoSortTranslatable only as an artifact/pattern witness"
  , "route closed two-sort source terms through the two-sort checking waist"
  , "keep HE runtime rules and queries on the runtime-exec lane"
  , "only after explicit typed translation should stronger HE->two-sort claims open"
  , "only after that reconsider direct runtime equivalence claims" ]

/-- Explicit anti-drift prohibitions for this bridge. -/
def heTwoSortPiSigmaIdForbiddenMoves : List String :=
  [ "do not treat TwoSortTranslatable as a typing theorem into TwoSortPiSigmaId"
  , "do not reclassify HE runtime rules as kernel certificates"
  , "do not claim current twoSortDependent rewrites fit the direct R_exec₀ bridge"
  , "do not collapse query support and exec authority into one backend claim" ]

/-- Contract object for the current HE -> two-sort fragment bridge. -/
structure HETwoSortPiSigmaIdFragmentContract where
  gateStatus : HETwoSortPiSigmaIdGate → Bool
  phaseOrder : List String
  forbiddenMoves : List String
  checkingRegion : ElaboratedRegion
  checkingOverlap : OverlapClass

noncomputable def heTwoSortPiSigmaIdFragmentContract : HETwoSortPiSigmaIdFragmentContract :=
  { gateStatus := heTwoSortPiSigmaIdGateStatus
    phaseOrder := heTwoSortPiSigmaIdPhaseOrder
    forbiddenMoves := heTwoSortPiSigmaIdForbiddenMoves
    checkingRegion := mettaAbstractMachineBoundary.checkingBoundary.region
    checkingOverlap := mettaAbstractMachineBoundary.checkingBoundary.overlapClass }

theorem heTwoSortPiSigmaIdFragmentContract_region :
    heTwoSortPiSigmaIdFragmentContract.checkingRegion = ElaboratedRegion.twoSortKernelRegion := by
  simp [heTwoSortPiSigmaIdFragmentContract, checkingBoundary_region]

theorem heTwoSortPiSigmaIdFragmentContract_overlap :
    heTwoSortPiSigmaIdFragmentContract.checkingOverlap = OverlapClass.artifactOnly := by
  simp [heTwoSortPiSigmaIdFragmentContract, checkingBoundary_overlap]

theorem heTwoSortPiSigmaIdPhaseOrder_starts_with_lane_freeze :
    heTwoSortPiSigmaIdPhaseOrder.head? =
      some "freeze the abstract-machine lane split as authoritative" := rfl

theorem heTwoSortPiSigmaId_forbids_runtime_reclassification :
    "do not reclassify HE runtime rules as kernel certificates" ∈
      heTwoSortPiSigmaIdForbiddenMoves := by
  simp [heTwoSortPiSigmaIdForbiddenMoves]

/-! ## Live fragment witnesses -/

theorem twoSortTranslatable_has_patternWitness
    (a : Atom) (h : TwoSortTranslatable a) :
    ∃ p, atomToPattern a = some p := by
  exact translatable_witness a (TwoSortTranslatable.toTranslatable h)

theorem twoSortClosedSyntax_uses_kernelCertificateLane (term : TwoSortSyntaxTerm 0) :
    SyntaxNode.abstractMachineLane (SyntaxNode.twoSortClosedSyntax term) =
      AbstractMachineLane.kernelCertificateLane := by
  exact (twoSortClosedSyntax_routes_to_checking_boundary term).1

theorem twoSortClosedSyntax_region_is_twoSortKernel (term : TwoSortSyntaxTerm 0) :
    ElaboratedNode.region (elaborate (SyntaxNode.twoSortClosedSyntax term)) =
      ElaboratedRegion.twoSortKernelRegion := by
  exact elaborate_twoSortClosedSyntax_region term

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

theorem twoSortDependent_current_frontier_not_directExec0
    (r : RewriteRule)
    (hr : r ∈ Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.twoSortDependent.rewrites) :
    ¬ ∃ x, r.left = .fvar x ∧
      Mettapedia.Languages.ProcessCalculi.MORK.morkTranslatable r.right = true := by
  exact kernel_lane_not_direct_runtimeExec0 r hr

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.HEFragmentBridge
