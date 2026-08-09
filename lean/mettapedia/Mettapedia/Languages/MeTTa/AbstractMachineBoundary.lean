import Mettapedia.Languages.MeTTa.ElaboratedCore
import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.MeTTa.SpaceEngineBoundary
import Mettapedia.Languages.MeTTa.SuiteBase.RuntimeKernelPackage

/-!
# MeTTa Abstract Machine Boundary

Packages the current authoritative integration waist for MeTTa:

- the elaboration boundary (`ElaboratedCore`)
- the DTT kernel checking/conversion waist (`PureCheckingService`)
- the runtime execution/query waist (`RuntimeExec`)
- the backend-neutral runtime kernel package
- the native / PathMap / MORK engine capability boundary

This file does **not** introduce a new evaluator. It makes explicit which lane
is authoritative for which kind of syntax node.

Positive example:
- closed Pure terms route to the Pure checking waist.

Negative example:
- ordinary HE runtime rules are not secretly reclassified as Pure kernel terms.
-/

namespace Mettapedia.Languages.MeTTa.AbstractMachineBoundary

open Mettapedia.Languages.MeTTa.DialectProfile
open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.MeTTa.RuntimeKernel
open Mettapedia.Languages.MeTTa.SpaceEngineBoundary
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## §1. Canonical boundary package -/

/-- The current authoritative MeTTa abstract-machine waist. -/
structure MeTTaAbstractMachineBoundary where
  checkingBoundary : PureCheckingBoundary
  execInterface : MeTTaRuntimeExecExtendedInterface
  queryInterface : MeTTaRuntimeQueryInterface
  runtimeKernel : RuntimeKernelPackage

/-- The live MeTTa abstract-machine waist in this repository. -/
noncomputable def mettaAbstractMachineBoundary : MeTTaAbstractMachineBoundary where
  checkingBoundary := pureCheckingBoundary
  execInterface := morkRuntimeExec0Ext
  queryInterface := morkRuntimeQueryExec0
  runtimeKernel := morkRuntimeKernelPackage

theorem checkingBoundary_region :
    mettaAbstractMachineBoundary.checkingBoundary.region =
      ElaboratedRegion.pureKernelRegion := by
  rfl

theorem checkingBoundary_overlap :
    mettaAbstractMachineBoundary.checkingBoundary.overlapClass =
      OverlapClass.artifactOnly := by
  rfl

theorem execInterface_backend :
    mettaAbstractMachineBoundary.execInterface.backendName = "MORK/MM2" := by
  rfl

theorem queryInterface_backend :
    mettaAbstractMachineBoundary.queryInterface.backendName = "MORK/MM2" := by
  rfl

theorem runtimeKernel_exec_backend :
    mettaAbstractMachineBoundary.runtimeKernel.execClass.backendName = "MORK/MM2" := by
  rfl

/-! ## §2. Authority lanes -/

/-- Which authoritative lane a syntax node is routed to. -/
inductive AbstractMachineLane where
  /-- Closed Pure terms whose authority is the DTT kernel checking waist. -/
  | kernelCertificateLane
  /-- Typed Core atoms that already have a shared artifact view. -/
  | kernelTypedArtifactLane
  /-- Runtime rule firing through the theoremic runtime-execution interface. -/
  | runtimeRuleLane
  /-- Runtime query evaluation through the theoremic runtime-query interface. -/
  | runtimeQueryLane
  /-- Legacy runtime artifact lane with no claimed execution backend. -/
  | runtimeAuditLane
  /-- Grounded / FFI / oracle boundary. -/
  | oracleLane
  /-- Elaboration-time / reflective boundary. -/
  | metaLane
deriving DecidableEq, Repr

/-- The elaboration region controlled by each authority lane. -/
def AbstractMachineLane.region : AbstractMachineLane → ElaboratedRegion
  | AbstractMachineLane.kernelCertificateLane => ElaboratedRegion.pureKernelRegion
  | AbstractMachineLane.kernelTypedArtifactLane => ElaboratedRegion.pureKernelRegion
  | AbstractMachineLane.runtimeRuleLane => ElaboratedRegion.runtimeExecRegion
  | AbstractMachineLane.runtimeQueryLane => ElaboratedRegion.runtimeExecRegion
  | AbstractMachineLane.runtimeAuditLane => ElaboratedRegion.runtimeExecRegion
  | AbstractMachineLane.oracleLane => ElaboratedRegion.oracleRegion
  | AbstractMachineLane.metaLane => ElaboratedRegion.metaRegion

/-- Whether the lane fundamentally relies on the Pure checking waist. -/
def AbstractMachineLane.needsPureChecking : AbstractMachineLane → Bool
  | AbstractMachineLane.kernelCertificateLane => true
  | _ => false

/-- Whether the lane fundamentally relies on the runtime kernel package. -/
def AbstractMachineLane.needsRuntimeKernel : AbstractMachineLane → Bool
  | AbstractMachineLane.runtimeRuleLane => true
  | AbstractMachineLane.runtimeQueryLane => true
  | _ => false

/-- Which authority lane a syntax node belongs to. -/
def SyntaxNode.abstractMachineLane : SyntaxNode → AbstractMachineLane
  | SyntaxNode.pureClosedSyntax _ => AbstractMachineLane.kernelCertificateLane
  | SyntaxNode.coreTypedAtom _ => AbstractMachineLane.kernelTypedArtifactLane
  | SyntaxNode.heRuntimeRule _ => AbstractMachineLane.runtimeRuleLane
  | SyntaxNode.pettaRuntimeRule _ => AbstractMachineLane.runtimeRuleLane
  | SyntaxNode.heRuntimeQuery _ => AbstractMachineLane.runtimeQueryLane
  | SyntaxNode.pettaRuntimeQuery _ => AbstractMachineLane.runtimeQueryLane
  | SyntaxNode.fullLegacyRuntime _ => AbstractMachineLane.runtimeAuditLane
  | SyntaxNode.oracleCall _ _ _ _ => AbstractMachineLane.oracleLane
  | SyntaxNode.metaQuoted _ _ => AbstractMachineLane.metaLane

theorem syntaxNode_region_agrees_with_lane (s : SyntaxNode) :
    (elaborate s).region = (SyntaxNode.abstractMachineLane s).region := by
  cases s <;> rfl

theorem kernelCertificateLane_needsPureChecking :
    AbstractMachineLane.needsPureChecking AbstractMachineLane.kernelCertificateLane = true := by
  rfl

theorem runtimeRuleLane_needsRuntimeKernel :
    AbstractMachineLane.needsRuntimeKernel AbstractMachineLane.runtimeRuleLane = true := by
  rfl

theorem runtimeQueryLane_needsRuntimeKernel :
    AbstractMachineLane.needsRuntimeKernel AbstractMachineLane.runtimeQueryLane = true := by
  rfl

theorem kernelTypedArtifactLane_not_runtimeKernel :
    AbstractMachineLane.needsRuntimeKernel AbstractMachineLane.kernelTypedArtifactLane = false := by
  rfl

/-! ## §3. Syntax-node routing facts -/

theorem pureClosedSyntax_routes_to_checking_boundary (term : PureSyntaxTerm 0) :
    SyntaxNode.abstractMachineLane (SyntaxNode.pureClosedSyntax term) =
      AbstractMachineLane.kernelCertificateLane ∧
    mettaAbstractMachineBoundary.checkingBoundary.supportsImportedCertificates = true ∧
    mettaAbstractMachineBoundary.checkingBoundary.supportsConversion = true := by
  simp [SyntaxNode.abstractMachineLane, mettaAbstractMachineBoundary, pureCheckingBoundary]

theorem coreTypedAtom_routes_to_artifact_lane (sourceAtom : CoreTypedSyntaxAtom) :
    SyntaxNode.abstractMachineLane (SyntaxNode.coreTypedAtom sourceAtom) =
      AbstractMachineLane.kernelTypedArtifactLane ∧
    (certifyCoreTypedSyntaxAtom sourceAtom).overlapClass = OverlapClass.artifactOnly := by
  exact ⟨rfl, certifyCoreTypedSyntaxAtom_overlapClass sourceAtom⟩

theorem heRuntimeRule_routes_to_exec_backend (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.heRuntimeRule pattern) =
      AbstractMachineLane.runtimeRuleLane ∧
    match elaborate (SyntaxNode.heRuntimeRule pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering =
          mettaAbstractMachineBoundary.execInterface.backendName
    | _ => False := by
  constructor
  · rfl
  · exact elaborate_heRuntimeRule_backend pattern

theorem heRuntimeQuery_routes_to_query_backend (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.heRuntimeQuery pattern) =
      AbstractMachineLane.runtimeQueryLane ∧
    match elaborate (SyntaxNode.heRuntimeQuery pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering =
          mettaAbstractMachineBoundary.queryInterface.backendName
    | _ => False := by
  constructor
  · rfl
  · simp [elaborate, RuntimeLowering.backendName, mettaAbstractMachineBoundary,
      morkRuntimeQueryExec0_backendName]

theorem pettaRuntimeQuery_routes_to_query_backend (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.pettaRuntimeQuery pattern) =
      AbstractMachineLane.runtimeQueryLane ∧
    match elaborate (SyntaxNode.pettaRuntimeQuery pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering =
          mettaAbstractMachineBoundary.queryInterface.backendName
    | _ => False := by
  constructor
  · rfl
  · simp [elaborate, RuntimeLowering.backendName, mettaAbstractMachineBoundary,
      morkRuntimeQueryExec0_backendName]

theorem pettaRuntimeRule_shares_exec_backend (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.pettaRuntimeRule pattern) =
      AbstractMachineLane.runtimeRuleLane ∧
    match elaborate (SyntaxNode.pettaRuntimeRule pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering =
          mettaAbstractMachineBoundary.execInterface.backendName
    | _ => False := by
  constructor
  · rfl
  · exact elaborate_pettaRuntimeRule_backend pattern

theorem fullLegacyRuntime_is_audit_lane (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.fullLegacyRuntime pattern) =
      AbstractMachineLane.runtimeAuditLane ∧
    match elaborate (SyntaxNode.fullLegacyRuntime pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "audit-only"
    | _ => False := by
  exact ⟨rfl, elaborate_fullLegacyRuntime_auditOnly pattern⟩

theorem oracleCall_routes_to_oracle_lane
    (dialect : MeTTaDialectProfile) (opName resultDescriptor : String)
    (args : List Pattern) :
    SyntaxNode.abstractMachineLane
        (SyntaxNode.oracleCall dialect opName resultDescriptor args) =
      AbstractMachineLane.oracleLane ∧
    ElaboratedNode.region
      (elaborate (SyntaxNode.oracleCall dialect opName resultDescriptor args)) =
        ElaboratedRegion.oracleRegion := by
  exact ⟨rfl, elaborate_oracleCall_region dialect opName resultDescriptor args⟩

theorem metaQuoted_routes_to_meta_lane
    (description : String) (pattern : Pattern) :
    SyntaxNode.abstractMachineLane (SyntaxNode.metaQuoted description pattern) =
      AbstractMachineLane.metaLane ∧
    ElaboratedNode.region (elaborate (SyntaxNode.metaQuoted description pattern)) =
      ElaboratedRegion.metaRegion := by
  exact ⟨rfl, elaborate_metaQuoted_region description pattern⟩

/-! ## §4. Engine support boundary -/

/-- Which concrete engine lanes can host the operational part of a given
authority lane. Kernel/oracle/meta lanes are engine-independent here. -/
def AbstractMachineLane.supportedByEngine : AbstractMachineLane → SpaceEngine → Bool
  | AbstractMachineLane.runtimeRuleLane, e =>
      EngineCapability.execStep ∈ SpaceEngine.capabilities e
  | AbstractMachineLane.runtimeQueryLane, e =>
      EngineCapability.equationQuery ∈ SpaceEngine.capabilities e
  | AbstractMachineLane.runtimeAuditLane, _ => true
  | _, _ => true

theorem runtimeRule_supported_only_by_mork (engine : SpaceEngine) :
    AbstractMachineLane.supportedByEngine AbstractMachineLane.runtimeRuleLane engine = true ↔
      engine = SpaceEngine.mork := by
  cases engine <;> decide

theorem runtimeQuery_supported_by_native :
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane SpaceEngine.native = true := by
  decide

theorem runtimeQuery_supported_by_pathmap :
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane SpaceEngine.pathmap = true := by
  decide

theorem runtimeQuery_supported_by_mork :
    AbstractMachineLane.supportedByEngine
      AbstractMachineLane.runtimeQueryLane SpaceEngine.mork = true := by
  decide

theorem runtimeRule_requires_exec_capability
    (engine : SpaceEngine)
    (h : AbstractMachineLane.supportedByEngine AbstractMachineLane.runtimeRuleLane engine = true) :
    engine = SpaceEngine.mork := by
  exact (runtimeRule_supported_only_by_mork engine).mp h

/-! ## §5. Honest frontier theorem -/

/-- The Pure kernel lane is authoritative through the Pure checking waist, not
through the current direct `R_exec₀` source-rule bridge. -/
theorem kernel_lane_not_direct_runtimeExec0
    (r : RewriteRule)
    (hr : r ∈ Mettapedia.Languages.MeTTa.Pure.Core.mettaPure.rewrites) :
    ¬ ∃ x, r.left = .fvar x ∧
      Mettapedia.Languages.ProcessCalculi.MORK.morkTranslatable r.right = true := by
  exact mettaPure_language_frontier_is_not_directExec0 r hr

/-- HE and PeTTa runtime rules already meet at the same runtime-exec backend
waist even though they remain distinct dialects. -/
theorem he_and_petta_runtime_rules_share_backend (hePattern pettaPattern : Pattern) :
    match elaborate (SyntaxNode.heRuntimeRule hePattern),
          elaborate (SyntaxNode.pettaRuntimeRule pettaPattern) with
    | ElaboratedNode.runtimeNode heCert, ElaboratedNode.runtimeNode pettaCert =>
        RuntimeLowering.backendName heCert.lowering =
          RuntimeLowering.backendName pettaCert.lowering
    | _, _ => False := by
  exact runtimeBackendAgreement hePattern pettaPattern

end Mettapedia.Languages.MeTTa.AbstractMachineBoundary
