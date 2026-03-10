import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.InductiveKernelExtension
import Mettapedia.Languages.MeTTa.FixpointKernelSpec

/-!
# Implementation-Facing Extensions of the Pure Checking Boundary

This file keeps `PureCheckingService` fixed and adds the first implementation-
facing wrappers above it for:

- ordinary strictly-positive family declarations, and
- the first structural fixpoint interfaces staged above those families.

It does **not** implement inductives or fixpoints in `MeTTa-Pure`.
It packages the current next-step contract through the existing checking
boundary.
-/

namespace Mettapedia.Languages.MeTTa

open Mettapedia.Languages.MeTTa.ElaboratedCore

/-- A checked ordinary-family declaration as seen through the current Pure
checking boundary. -/
structure CheckedOrdinaryFamily where
  service : PureCheckingBoundary
  extension : OrdinaryFamilyKernelExtension
  regionAgrees : service.region = extension.checkingBoundary.region
  overlapAgrees : service.overlapClass = extension.checkingBoundary.overlapClass
  supportsClosedTyping :
    PureJudgmentKind.closedTyping ∈ service.supportedJudgments
  supportsArtifactAgreement :
    PureJudgmentKind.quotedArtifactAgreement ∈ service.supportedJudgments
  supportsFamilyDeclaration :
    InductiveKernelJudgmentKind.familyDeclaration ∈
      extension.kernelBoundary.supportedJudgments
  supportsGeneratedRecursor :
    InductiveKernelJudgmentKind.generatedRecursor ∈
      extension.kernelBoundary.supportedJudgments
  supportsStructuralRecursion :
    InductiveKernelJudgmentKind.structuralRecursion ∈
      extension.kernelBoundary.supportedJudgments

def PureCheckingBoundary.checkOrdinaryFamily
    (svc : PureCheckingBoundary) (ext : OrdinaryFamilyKernelExtension)
    (hregion : svc.region = ext.checkingBoundary.region)
    (hoverlap : svc.overlapClass = ext.checkingBoundary.overlapClass)
    (hclosed : PureJudgmentKind.closedTyping ∈ svc.supportedJudgments)
    (hart : PureJudgmentKind.quotedArtifactAgreement ∈ svc.supportedJudgments)
    (hfamily :
      InductiveKernelJudgmentKind.familyDeclaration ∈ ext.kernelBoundary.supportedJudgments)
    (hrec :
      InductiveKernelJudgmentKind.generatedRecursor ∈ ext.kernelBoundary.supportedJudgments)
    (hstruct :
      InductiveKernelJudgmentKind.structuralRecursion ∈ ext.kernelBoundary.supportedJudgments) :
    CheckedOrdinaryFamily :=
  { service := svc
    extension := ext
    regionAgrees := hregion
    overlapAgrees := hoverlap
    supportsClosedTyping := hclosed
    supportsArtifactAgreement := hart
    supportsFamilyDeclaration := hfamily
    supportsGeneratedRecursor := hrec
    supportsStructuralRecursion := hstruct }

def checkOrdinaryFamilyCanonical
    (iface : PureInductiveKernelInterface) : CheckedOrdinaryFamily :=
  PureCheckingBoundary.checkOrdinaryFamily
    pureCheckingBoundary
    iface.toKernelExtension
    iface.toKernelExtension.region_eq.symm
    iface.toKernelExtension.overlap_eq.symm
    pureCheckingBoundary_supports_closedTyping
    pureCheckingBoundary_supports_quotedArtifactAgreement
    iface.toKernelBoundary_supports_familyDeclaration
    iface.toKernelBoundary_supports_generatedRecursor
    iface.toKernelBoundary_supports_structuralRecursion

theorem checkOrdinaryFamilyCanonical_region
    (iface : PureInductiveKernelInterface) :
    (checkOrdinaryFamilyCanonical iface).service.region = .pureKernelRegion := by
  simp [checkOrdinaryFamilyCanonical, PureCheckingBoundary.checkOrdinaryFamily,
    pureCheckingBoundary]

theorem checkOrdinaryFamilyCanonical_overlap
    (iface : PureInductiveKernelInterface) :
    (checkOrdinaryFamilyCanonical iface).service.overlapClass = .artifactOnly := by
  simp [checkOrdinaryFamilyCanonical, PureCheckingBoundary.checkOrdinaryFamily,
    pureCheckingBoundary]

theorem checkOrdinaryFamilyCanonical_familyName
    (iface : PureInductiveKernelInterface) :
    (checkOrdinaryFamilyCanonical iface).extension.declaration.familyName =
      iface.family.name := by
  simpa [checkOrdinaryFamilyCanonical, PureCheckingBoundary.checkOrdinaryFamily]
    using iface.toKernelExtension.familyName_eq

theorem checkOrdinaryFamilyCanonical_recursorName
    (iface : PureInductiveKernelInterface) :
    (checkOrdinaryFamilyCanonical iface).extension.declaration.recursorName =
      iface.recursorContractStub := by
  simpa [checkOrdinaryFamilyCanonical, PureCheckingBoundary.checkOrdinaryFamily]
    using iface.toKernelExtension.recursorName_eq

def checkedUnitFamily : CheckedOrdinaryFamily :=
  checkOrdinaryFamilyCanonical unitPureKernelInterface

def checkedBoolFamily : CheckedOrdinaryFamily :=
  checkOrdinaryFamilyCanonical boolPureKernelInterface

def checkedNatFamily : CheckedOrdinaryFamily :=
  checkOrdinaryFamilyCanonical natPureKernelInterface

theorem checkedUnitFamily_familyName :
    checkedUnitFamily.extension.declaration.familyName = "Unit" := by
  simpa [checkedUnitFamily, checkOrdinaryFamilyCanonical,
    PureCheckingBoundary.checkOrdinaryFamily] using
    unitPureKernelInterface.toKernelExtension.familyName_eq

theorem checkedBoolFamily_familyName :
    checkedBoolFamily.extension.declaration.familyName = "Bool" := by
  simpa [checkedBoolFamily, checkOrdinaryFamilyCanonical,
    PureCheckingBoundary.checkOrdinaryFamily] using
    boolPureKernelInterface.toKernelExtension.familyName_eq

theorem checkedNatFamily_familyName :
    checkedNatFamily.extension.declaration.familyName = "Nat" := by
  simpa [checkedNatFamily, checkOrdinaryFamilyCanonical,
    PureCheckingBoundary.checkOrdinaryFamily] using
    natPureKernelInterface.toKernelExtension.familyName_eq

/-- A checked structural fixpoint interface, still staged above the ordinary-
family implementation boundary. -/
structure CheckedStructuralFixpoint where
  service : PureCheckingBoundary
  iface : StructuralFixpointKernelInterface
  region : ElaboratedRegion
  overlapClass : OverlapClass
  supportsClosedTyping :
    PureJudgmentKind.closedTyping ∈ service.supportedJudgments
  supportsArtifactAgreement :
    PureJudgmentKind.quotedArtifactAgreement ∈ service.supportedJudgments
  recursionIsStructural : iface.hook.recursionKind = .structural

def PureCheckingBoundary.checkStructuralFixpoint
    (svc : PureCheckingBoundary)
    (iface : StructuralFixpointKernelInterface)
    (hclosed : PureJudgmentKind.closedTyping ∈ svc.supportedJudgments)
    (hart :
      PureJudgmentKind.quotedArtifactAgreement ∈ svc.supportedJudgments) :
    CheckedStructuralFixpoint :=
  { service := svc
    iface := iface
    region := svc.region
    overlapClass := svc.overlapClass
    supportsClosedTyping := hclosed
    supportsArtifactAgreement := hart
    recursionIsStructural := iface.structural_only }

def checkStructuralFixpointCanonical
    (iface : StructuralFixpointKernelInterface) : CheckedStructuralFixpoint :=
  PureCheckingBoundary.checkStructuralFixpoint
    pureCheckingBoundary
    iface
    pureCheckingBoundary_supports_closedTyping
    pureCheckingBoundary_supports_quotedArtifactAgreement

def checkedNatIsZeroFixpoint : CheckedStructuralFixpoint :=
  checkStructuralFixpointCanonical natIsZeroFixpointInterface

def checkedNatPredFixpoint : CheckedStructuralFixpoint :=
  checkStructuralFixpointCanonical natPredFixpointInterface

theorem checkedNatIsZeroFixpoint_functionName :
    checkedNatIsZeroFixpoint.iface.hook.functionName = "Nat.isZero" := by
  rfl

theorem checkedNatPredFixpoint_functionName :
    checkedNatPredFixpoint.iface.hook.functionName = "Nat.pred" := by
  rfl

theorem checkedNatIsZeroFixpoint_recursor :
    checkedNatIsZeroFixpoint.iface.hook.recursorContractStub = "Nat.rec" := by
  exact natIsZeroFixpoint_recursor

theorem checkedNatPredFixpoint_recursor :
    checkedNatPredFixpoint.iface.hook.recursorContractStub = "Nat.rec" := by
  exact natPredFixpoint_recursor

/-- Current honest summary:
ordinary-family declarations and starter structural fixpoints refine the same
Pure checking boundary, but remain proof-side `artifactOnly` objects. -/
theorem implementationFacingFamiliesAndFixpoints_still_artifactOnly :
    checkedUnitFamily.service.overlapClass = .artifactOnly ∧
      checkedBoolFamily.service.overlapClass = .artifactOnly ∧
      checkedNatFamily.service.overlapClass = .artifactOnly ∧
      checkedNatIsZeroFixpoint.overlapClass = .artifactOnly ∧
      checkedNatPredFixpoint.overlapClass = .artifactOnly := by
  simp [checkedUnitFamily, checkedBoolFamily, checkedNatFamily,
    checkOrdinaryFamilyCanonical, PureCheckingBoundary.checkOrdinaryFamily,
    checkedNatIsZeroFixpoint, checkedNatPredFixpoint,
    checkStructuralFixpointCanonical,
    PureCheckingBoundary.checkStructuralFixpoint, pureCheckingBoundary]

end Mettapedia.Languages.MeTTa
