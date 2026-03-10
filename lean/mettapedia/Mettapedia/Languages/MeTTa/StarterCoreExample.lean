import Mettapedia.Languages.MeTTa.PureCheckingExtensions
import Mettapedia.Languages.MeTTa.InductiveCertificateInterface
import Mettapedia.Languages.MeTTa.FixpointCertificateInterface
import Mettapedia.Languages.MeTTa.InductiveRecursorContract
import Mettapedia.Languages.MeTTa.ElaboratedCore

/-!
# Starter MeTTaPure/Core Example

This file packages the first concrete implementation-facing MeTTaPure/Core
example built from the current staged architecture:

- checked ordinary families for `Unit`, `Bool`, `Nat`
- checked structural fixpoints for `Nat.isZero`, `Nat.pred`
- runtime-queryable constructor/fixpoint artifacts
- elaborated-core objects exposing the same artifacts in the shared middle layer

It remains honest:
- proof-side overlap is still `artifactOnly`
- runtime-side strengthening is currently `queryCompatible`
- no direct proof/runtime execution agreement is claimed
- no inductive or fixpoint implementation in `MeTTa-Pure` is claimed
-/

namespace Mettapedia.Languages.MeTTa

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeExec

/-- First serious implementation-facing `MeTTaPure/Core` example object. -/
structure StarterCoreExample where
  checkedUnitFamily : CheckedOrdinaryFamily
  checkedBoolFamily : CheckedOrdinaryFamily
  checkedNatFamily : CheckedOrdinaryFamily
  checkedNatIsZeroFixpoint : CheckedStructuralFixpoint
  checkedNatPredFixpoint : CheckedStructuralFixpoint
  unitInductiveNode : ElaboratedNode
  boolTrueInductiveNode : ElaboratedNode
  natZeroInductiveNode : ElaboratedNode
  natIsZeroFixpointNode : ElaboratedNode
  natPredFixpointNode : ElaboratedNode

def starterCoreExample : StarterCoreExample :=
  { checkedUnitFamily := checkedUnitFamily
    checkedBoolFamily := checkedBoolFamily
    checkedNatFamily := checkedNatFamily
    checkedNatIsZeroFixpoint := checkedNatIsZeroFixpoint
    checkedNatPredFixpoint := checkedNatPredFixpoint
    unitInductiveNode := ElaboratedNode.inductiveNode (certifyInductiveOverlap unitOverlapBridge)
    boolTrueInductiveNode := ElaboratedNode.inductiveNode (certifyInductiveOverlap boolTrueOverlapBridge)
    natZeroInductiveNode := ElaboratedNode.inductiveNode (certifyInductiveOverlap natZeroOverlapBridge)
    natIsZeroFixpointNode := ElaboratedNode.fixpointNode (certifyFixpointOverlap natIsZeroFixpointOverlapBridge)
    natPredFixpointNode := ElaboratedNode.fixpointNode (certifyFixpointOverlap natPredFixpointOverlapBridge) }

theorem starterCoreExample_unitFamilyName :
    starterCoreExample.checkedUnitFamily.extension.declaration.familyName = "Unit" := by
  exact checkedUnitFamily_familyName

theorem starterCoreExample_boolFamilyName :
    starterCoreExample.checkedBoolFamily.extension.declaration.familyName = "Bool" := by
  exact checkedBoolFamily_familyName

theorem starterCoreExample_natFamilyName :
    starterCoreExample.checkedNatFamily.extension.declaration.familyName = "Nat" := by
  exact checkedNatFamily_familyName

theorem starterCoreExample_unitRecursor :
    starterCoreExample.checkedUnitFamily.recursorContract = unitRecursorContract := by
  rfl

theorem starterCoreExample_boolRecursor :
    starterCoreExample.checkedBoolFamily.recursorContract = boolRecursorContract := by
  rfl

theorem starterCoreExample_natRecursor :
    starterCoreExample.checkedNatFamily.recursorContract = natRecursorContract := by
  rfl

theorem starterCoreExample_natIsZeroName :
    starterCoreExample.checkedNatIsZeroFixpoint.iface.hook.functionName = "Nat.isZero" := by
  exact checkedNatIsZeroFixpoint_functionName

theorem starterCoreExample_natPredName :
    starterCoreExample.checkedNatPredFixpoint.iface.hook.functionName = "Nat.pred" := by
  exact checkedNatPredFixpoint_functionName

theorem starterCoreExample_natIsZeroRecursor :
    starterCoreExample.checkedNatIsZeroFixpoint.recursorContract = natIsZeroRecursorContract := by
  rfl

theorem starterCoreExample_natPredRecursor :
    starterCoreExample.checkedNatPredFixpoint.recursorContract = natPredRecursorContract := by
  rfl

theorem starterCoreExample_natIsZeroEquation :
    starterCoreExample.checkedNatIsZeroFixpoint.recursorContract.equationTheoremName =
      "Nat.isZero.eqns" := by
  rfl

theorem starterCoreExample_natPredEquation :
    starterCoreExample.checkedNatPredFixpoint.recursorContract.equationTheoremName =
      "Nat.pred.eqns" := by
  rfl

theorem starterCoreExample_proofSide_still_artifactOnly :
    starterCoreExample.checkedUnitFamily.service.overlapClass = .artifactOnly ∧
      starterCoreExample.checkedBoolFamily.service.overlapClass = .artifactOnly ∧
      starterCoreExample.checkedNatFamily.service.overlapClass = .artifactOnly ∧
      starterCoreExample.checkedNatIsZeroFixpoint.overlapClass = .artifactOnly ∧
      starterCoreExample.checkedNatPredFixpoint.overlapClass = .artifactOnly := by
  exact implementationFacingFamiliesAndFixpoints_still_artifactOnly

theorem starterCoreExample_unitCtor_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      starterCoreExample.unitInductiveNode.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [starterCoreExample] using unitDualTargetCandidate_queryCompatible

theorem starterCoreExample_boolTrueCtor_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      starterCoreExample.boolTrueInductiveNode.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [starterCoreExample] using boolTrueDualTargetCandidate_queryCompatible

theorem starterCoreExample_natZeroCtor_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      starterCoreExample.natZeroInductiveNode.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [starterCoreExample] using natZeroDualTargetCandidate_queryCompatible

theorem starterCoreExample_natIsZero_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      starterCoreExample.natIsZeroFixpointNode.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [starterCoreExample] using natIsZeroFixpoint_queryCompatible

theorem starterCoreExample_natPred_queryCompatible :
    let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
      starterCoreExample.natPredFixpointNode.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [starterCoreExample] using natPredFixpoint_queryCompatible

theorem starterCoreExample_nodes_live_in_pureKernelRegion :
    starterCoreExample.unitInductiveNode.region = .pureKernelRegion ∧
      starterCoreExample.boolTrueInductiveNode.region = .pureKernelRegion ∧
      starterCoreExample.natZeroInductiveNode.region = .pureKernelRegion ∧
      starterCoreExample.natIsZeroFixpointNode.region = .pureKernelRegion ∧
      starterCoreExample.natPredFixpointNode.region = .pureKernelRegion := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

theorem starterCoreExample_current_overlap_summary :
    starterCoreExample.checkedUnitFamily.service.overlapClass = .artifactOnly ∧
      starterCoreExample.checkedBoolFamily.service.overlapClass = .artifactOnly ∧
      starterCoreExample.checkedNatFamily.service.overlapClass = .artifactOnly ∧
      starterCoreExample.checkedNatIsZeroFixpoint.overlapClass = .artifactOnly ∧
      starterCoreExample.checkedNatPredFixpoint.overlapClass = .artifactOnly ∧
      (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
        starterCoreExample.unitInductiveNode.artifact.pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) ∧
      (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
        starterCoreExample.boolTrueInductiveNode.artifact.pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) ∧
      (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
        starterCoreExample.natZeroInductiveNode.artifact.pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) ∧
      (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
        starterCoreExample.natIsZeroFixpointNode.artifact.pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) ∧
      (let a := Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom
        starterCoreExample.natPredFixpointNode.artifact.pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact starterCoreExample_proofSide_still_artifactOnly.1
  · exact starterCoreExample_proofSide_still_artifactOnly.2.1
  · exact starterCoreExample_proofSide_still_artifactOnly.2.2.1
  · exact starterCoreExample_proofSide_still_artifactOnly.2.2.2.1
  · exact starterCoreExample_proofSide_still_artifactOnly.2.2.2.2
  · exact starterCoreExample_unitCtor_queryCompatible
  · exact starterCoreExample_boolTrueCtor_queryCompatible
  · exact starterCoreExample_natZeroCtor_queryCompatible
  · exact starterCoreExample_natIsZero_queryCompatible
  · exact starterCoreExample_natPred_queryCompatible

end Mettapedia.Languages.MeTTa
