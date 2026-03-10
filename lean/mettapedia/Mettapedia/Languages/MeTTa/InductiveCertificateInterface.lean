import Mettapedia.Languages.MeTTa.InductiveKernelExtension
import Mettapedia.Languages.MeTTa.PureCertificateFragment
import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge
import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# Inductive-Family Interface to the Current Pure Certificate Lane

This file records the first theoremic interface from the minimal inductive
family kernel specification to the currently implemented restricted
`MeTTa-Pure` certificate lane.

It does **not** claim that inductive families are already implemented in the
kernel. Instead, it records two honest facts:

1. The current starter inductive families belong on the proof side as
   `artifactOnly` extensions of the restricted Pure certificate lane.
2. Some constructor artifacts already look runtime-friendly on the current
   MM2/MORK side; they are packaged here only as *candidates*, not as proved
   direct proof/runtime overlap.
-/

namespace Mettapedia.Languages.MeTTa

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The current honest proof-lane interface for one inductive family spec. -/
structure InductiveCertificateInterface where
  family : InductiveFamilySpec
  supportedJudgments : List PureJudgmentKind
  region : ElaboratedRegion
  overlapClass : OverlapClass

/-- Explicit bridge from the current proof-lane inductive interface to the
future Pure-kernel ordinary-family interface. -/
structure InductiveProofKernelBridge where
  proofInterface : InductiveCertificateInterface
  kernelInterface : PureInductiveKernelInterface
  sameFamily : kernelInterface.family = proofInterface.family

def InductiveProofKernelBridge.familyName
    (bridge : InductiveProofKernelBridge) : String :=
  bridge.kernelInterface.hook.familyName

def InductiveProofKernelBridge.recursorContractStub
    (bridge : InductiveProofKernelBridge) : String :=
  bridge.kernelInterface.recursorContractStub

def InductiveProofKernelBridge.kernelBoundary
    (bridge : InductiveProofKernelBridge) : InductiveKernelBoundary :=
  bridge.kernelInterface.toKernelBoundary

def InductiveProofKernelBridge.kernelExtension
    (bridge : InductiveProofKernelBridge) : OrdinaryFamilyKernelExtension :=
  bridge.kernelInterface.toKernelExtension

theorem InductiveProofKernelBridge.familyName_eq
    (bridge : InductiveProofKernelBridge) :
    bridge.familyName = bridge.proofInterface.family.name := by
  have hKernel :
      bridge.kernelInterface.hook.familyName =
        bridge.kernelInterface.family.name :=
    bridge.kernelInterface.familyName_eq
  have hName :
      bridge.familyName = bridge.kernelInterface.family.name := by
    simpa [InductiveProofKernelBridge.familyName] using hKernel
  have hFamily :
      bridge.kernelInterface.family.name =
        bridge.proofInterface.family.name := by
    simpa using congrArg InductiveFamilySpec.name bridge.sameFamily
  exact hName.trans hFamily

theorem InductiveProofKernelBridge.kernelBoundary_region
    (bridge : InductiveProofKernelBridge) :
    bridge.kernelBoundary.region = ElaboratedRegion.pureKernelRegion := by
  exact bridge.kernelInterface.toKernelBoundary_region

theorem InductiveProofKernelBridge.kernelBoundary_overlap
    (bridge : InductiveProofKernelBridge) :
    bridge.kernelBoundary.overlapClass = OverlapClass.artifactOnly := by
  exact bridge.kernelInterface.toKernelBoundary_overlap

theorem InductiveProofKernelBridge.kernelBoundary_supports_familyDeclaration
    (bridge : InductiveProofKernelBridge) :
    InductiveKernelJudgmentKind.familyDeclaration ∈
      bridge.kernelBoundary.supportedJudgments := by
  exact bridge.kernelInterface.toKernelBoundary_supports_familyDeclaration

theorem InductiveProofKernelBridge.kernelBoundary_supports_generatedRecursor
    (bridge : InductiveProofKernelBridge) :
    InductiveKernelJudgmentKind.generatedRecursor ∈
      bridge.kernelBoundary.supportedJudgments := by
  exact bridge.kernelInterface.toKernelBoundary_supports_generatedRecursor

theorem InductiveProofKernelBridge.kernelBoundary_supports_structuralRecursion
    (bridge : InductiveProofKernelBridge) :
    InductiveKernelJudgmentKind.structuralRecursion ∈
      bridge.kernelBoundary.supportedJudgments := by
  exact bridge.kernelInterface.toKernelBoundary_supports_structuralRecursion

theorem InductiveProofKernelBridge.kernelBoundary_positivity_holds
    (bridge : InductiveProofKernelBridge) :
    bridge.kernelInterface.hookInterface.family.strictlyPositive = true := by
  exact bridge.kernelInterface.toKernelBoundary_positivity_holds

theorem InductiveProofKernelBridge.kernelExtension_refines_pureCheckingBoundary
    (bridge : InductiveProofKernelBridge) :
    bridge.kernelExtension.checkingBoundary.region = pureCheckingBoundary.region ∧
      bridge.kernelExtension.checkingBoundary.overlapClass =
        pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem InductiveProofKernelBridge.kernelExtension_familyName
    (bridge : InductiveProofKernelBridge) :
    bridge.kernelExtension.declaration.familyName =
      bridge.proofInterface.family.name := by
  exact bridge.familyName_eq

theorem InductiveProofKernelBridge.kernelExtension_recursorName
    (bridge : InductiveProofKernelBridge) :
    bridge.kernelExtension.declaration.recursorName =
      bridge.kernelInterface.recursorContractStub := by
  exact bridge.kernelExtension.recursorName_eq

/-- Current starter inductives are proof-lane extensions first, not direct
runtime overlap. -/
def starterFamilyInterface (family : InductiveFamilySpec) : InductiveCertificateInterface :=
  { family := family
    supportedJudgments := [.closedTyping, .quotedArtifactAgreement]
    region := .pureKernelRegion
    overlapClass := .artifactOnly }

theorem starterFamilyInterface_region (family : InductiveFamilySpec) :
    (starterFamilyInterface family).region = ElaboratedRegion.pureKernelRegion := rfl

theorem starterFamilyInterface_overlap (family : InductiveFamilySpec) :
    (starterFamilyInterface family).overlapClass = OverlapClass.artifactOnly := rfl

theorem starterFamilyInterface_supports_closedTyping (family : InductiveFamilySpec) :
    PureJudgmentKind.closedTyping ∈ (starterFamilyInterface family).supportedJudgments := by
  simp [starterFamilyInterface]

theorem starterFamilyInterface_supports_artifactAgreement (family : InductiveFamilySpec) :
    PureJudgmentKind.quotedArtifactAgreement ∈ (starterFamilyInterface family).supportedJudgments := by
  simp [starterFamilyInterface]

theorem starterFamilyInterface_refines_pureCheckingBoundary_region
    (family : InductiveFamilySpec) :
    (starterFamilyInterface family).region = pureCheckingBoundary.region := by
  rfl

theorem starterFamilyInterface_refines_pureCheckingBoundary_overlap
    (family : InductiveFamilySpec) :
    (starterFamilyInterface family).overlapClass = pureCheckingBoundary.overlapClass := by
  rfl

theorem starterFamilyInterface_refines_pureCheckingBoundary_closedTyping :
    PureJudgmentKind.closedTyping ∈ pureCheckingBoundary.supportedJudgments := by
  exact pureCheckingBoundary_supports_closedTyping

theorem starterFamilyInterface_refines_pureCheckingBoundary_artifactAgreement :
    PureJudgmentKind.quotedArtifactAgreement ∈ pureCheckingBoundary.supportedJudgments := by
  exact pureCheckingBoundary_supports_quotedArtifactAgreement

def unitProofKernelBridge : InductiveProofKernelBridge :=
  { proofInterface := starterFamilyInterface unitFamilySpec
    kernelInterface := unitPureKernelInterface
    sameFamily := rfl }

def boolProofKernelBridge : InductiveProofKernelBridge :=
  { proofInterface := starterFamilyInterface boolFamilySpec
    kernelInterface := boolPureKernelInterface
    sameFamily := rfl }

def natProofKernelBridge : InductiveProofKernelBridge :=
  { proofInterface := starterFamilyInterface natFamilySpec
    kernelInterface := natPureKernelInterface
    sameFamily := rfl }

theorem unitProofKernelBridge_region :
    unitProofKernelBridge.proofInterface.region = ElaboratedRegion.pureKernelRegion := rfl

theorem boolProofKernelBridge_region :
    boolProofKernelBridge.proofInterface.region = ElaboratedRegion.pureKernelRegion := rfl

theorem natProofKernelBridge_region :
    natProofKernelBridge.proofInterface.region = ElaboratedRegion.pureKernelRegion := rfl

theorem unitProofKernelBridge_overlap :
    unitProofKernelBridge.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem boolProofKernelBridge_overlap :
    boolProofKernelBridge.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem natProofKernelBridge_overlap :
    natProofKernelBridge.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem unitProofKernelBridge_refines_pureCheckingBoundary :
    unitProofKernelBridge.proofInterface.region = pureCheckingBoundary.region ∧
      unitProofKernelBridge.proofInterface.overlapClass = pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem boolProofKernelBridge_refines_pureCheckingBoundary :
    boolProofKernelBridge.proofInterface.region = pureCheckingBoundary.region ∧
      boolProofKernelBridge.proofInterface.overlapClass = pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem natProofKernelBridge_refines_pureCheckingBoundary :
    natProofKernelBridge.proofInterface.region = pureCheckingBoundary.region ∧
      natProofKernelBridge.proofInterface.overlapClass = pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem unitProofKernelBridge_recursorStub :
    unitProofKernelBridge.kernelInterface.recursorContractStub = "Unit.rec" := rfl

theorem boolProofKernelBridge_recursorStub :
    boolProofKernelBridge.kernelInterface.recursorContractStub = "Bool.rec" := rfl

theorem natProofKernelBridge_recursorStub :
    natProofKernelBridge.kernelInterface.recursorContractStub = "Nat.rec" := rfl

theorem unitProofKernelBridge_kernelBoundary_familyDeclaration :
    InductiveKernelJudgmentKind.familyDeclaration ∈
      unitProofKernelBridge.kernelBoundary.supportedJudgments := by
  exact unitProofKernelBridge.kernelBoundary_supports_familyDeclaration

theorem boolProofKernelBridge_kernelBoundary_familyDeclaration :
    InductiveKernelJudgmentKind.familyDeclaration ∈
      boolProofKernelBridge.kernelBoundary.supportedJudgments := by
  exact boolProofKernelBridge.kernelBoundary_supports_familyDeclaration

theorem natProofKernelBridge_kernelBoundary_familyDeclaration :
    InductiveKernelJudgmentKind.familyDeclaration ∈
      natProofKernelBridge.kernelBoundary.supportedJudgments := by
  exact natProofKernelBridge.kernelBoundary_supports_familyDeclaration

theorem unitProofKernelBridge_kernelBoundary_generatedRecursor :
    InductiveKernelJudgmentKind.generatedRecursor ∈
      unitProofKernelBridge.kernelBoundary.supportedJudgments := by
  exact unitProofKernelBridge.kernelBoundary_supports_generatedRecursor

theorem boolProofKernelBridge_kernelBoundary_generatedRecursor :
    InductiveKernelJudgmentKind.generatedRecursor ∈
      boolProofKernelBridge.kernelBoundary.supportedJudgments := by
  exact boolProofKernelBridge.kernelBoundary_supports_generatedRecursor

theorem natProofKernelBridge_kernelBoundary_generatedRecursor :
    InductiveKernelJudgmentKind.generatedRecursor ∈
      natProofKernelBridge.kernelBoundary.supportedJudgments := by
  exact natProofKernelBridge.kernelBoundary_supports_generatedRecursor

/-- Runtime-compatible artifact candidate for a constructor of a future
inductive family.

This is intentionally weaker than a direct overlap theorem: it only says that
the constructor artifact already falls inside the current runtime translation
fragment. -/
structure InductiveRuntimeCandidate where
  family : InductiveFamilySpec
  ctorName : String
  artifact : SharedArtifact
  runtimeTranslatable : morkTranslatable artifact.pattern = true

def unitCtorCandidate : InductiveRuntimeCandidate :=
  { family := unitFamilySpec
    ctorName := "unit"
    artifact := ⟨.apply "unit" []⟩
    runtimeTranslatable := by simp [morkTranslatable, morkTranslatableList] }

def boolFalseCtorCandidate : InductiveRuntimeCandidate :=
  { family := boolFamilySpec
    ctorName := "false"
    artifact := ⟨.apply "false" []⟩
    runtimeTranslatable := by simp [morkTranslatable, morkTranslatableList] }

def boolTrueCtorCandidate : InductiveRuntimeCandidate :=
  { family := boolFamilySpec
    ctorName := "true"
    artifact := ⟨.apply "true" []⟩
    runtimeTranslatable := by simp [morkTranslatable, morkTranslatableList] }

def natZeroCtorCandidate : InductiveRuntimeCandidate :=
  { family := natFamilySpec
    ctorName := "zero"
    artifact := ⟨.apply "zero" []⟩
    runtimeTranslatable := by simp [morkTranslatable, morkTranslatableList] }

/-- Bridge object that also records a current runtime-friendly artifact
candidate for the same family when one exists.

This is the first explicit place where the three views of starter inductives
meet:
- proof-side interface
- future Pure-kernel hook/interface
- runtime-friendly constructor artifact candidate

The overlap remains honest: the proof-side classification can still be only
`artifactOnly`. -/
structure InductiveOverlapBridge where
  proofKernel : InductiveProofKernelBridge
  runtimeCandidate : InductiveRuntimeCandidate
  sameRuntimeFamily : runtimeCandidate.family = proofKernel.proofInterface.family

def InductiveOverlapBridge.familyName
    (bridge : InductiveOverlapBridge) : String :=
  bridge.proofKernel.familyName

theorem InductiveOverlapBridge.familyName_eq
    (bridge : InductiveOverlapBridge) :
    bridge.familyName = bridge.runtimeCandidate.family.name := by
  have hProof :
      bridge.familyName = bridge.proofKernel.proofInterface.family.name := by
    exact bridge.proofKernel.familyName_eq
  have hRuntime :
      bridge.proofKernel.proofInterface.family.name =
        bridge.runtimeCandidate.family.name := by
    simpa using congrArg InductiveFamilySpec.name bridge.sameRuntimeFamily.symm
  exact hProof.trans hRuntime

/-- First honest dual-target *candidate* package.

It packages:
- the proof-lane classification of a starter inductive family
- a runtime-friendly constructor artifact candidate

It does **not** claim actual inductive implementation in the kernel or a proved
direct overlap theorem. -/
structure InductiveDualTargetCandidate where
  proofInterface : InductiveCertificateInterface
  runtimeCandidate : InductiveRuntimeCandidate
  sameFamily : runtimeCandidate.family = proofInterface.family

def unitDualTargetCandidate : InductiveDualTargetCandidate :=
  { proofInterface := starterFamilyInterface unitFamilySpec
    runtimeCandidate := unitCtorCandidate
    sameFamily := rfl }

def boolTrueDualTargetCandidate : InductiveDualTargetCandidate :=
  { proofInterface := starterFamilyInterface boolFamilySpec
    runtimeCandidate := boolTrueCtorCandidate
    sameFamily := rfl }

def natZeroDualTargetCandidate : InductiveDualTargetCandidate :=
  { proofInterface := starterFamilyInterface natFamilySpec
    runtimeCandidate := natZeroCtorCandidate
    sameFamily := rfl }

def unitOverlapBridge : InductiveOverlapBridge :=
  { proofKernel := unitProofKernelBridge
    runtimeCandidate := unitCtorCandidate
    sameRuntimeFamily := rfl }

def boolTrueOverlapBridge : InductiveOverlapBridge :=
  { proofKernel := boolProofKernelBridge
    runtimeCandidate := boolTrueCtorCandidate
    sameRuntimeFamily := rfl }

def natZeroOverlapBridge : InductiveOverlapBridge :=
  { proofKernel := natProofKernelBridge
    runtimeCandidate := natZeroCtorCandidate
    sameRuntimeFamily := rfl }

theorem unitDualTargetCandidate_is_artifactOnly :
    unitDualTargetCandidate.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem boolTrueDualTargetCandidate_is_artifactOnly :
    boolTrueDualTargetCandidate.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem natZeroDualTargetCandidate_is_artifactOnly :
    natZeroDualTargetCandidate.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem unitDualTargetCandidate_runtimeTranslatable :
    morkTranslatable unitDualTargetCandidate.runtimeCandidate.artifact.pattern = true :=
  unitDualTargetCandidate.runtimeCandidate.runtimeTranslatable

theorem boolTrueDualTargetCandidate_runtimeTranslatable :
    morkTranslatable boolTrueDualTargetCandidate.runtimeCandidate.artifact.pattern = true :=
  boolTrueDualTargetCandidate.runtimeCandidate.runtimeTranslatable

theorem natZeroDualTargetCandidate_runtimeTranslatable :
    morkTranslatable natZeroDualTargetCandidate.runtimeCandidate.artifact.pattern = true :=
  natZeroDualTargetCandidate.runtimeCandidate.runtimeTranslatable

theorem unitKernelExtension_has_queryCompatibleCtor :
    ∃ ctor, ctor ∈ unitKernelExtension.declaration.ctors ∧
      ctor.name = "unit" ∧ ctor.argCount = 0 ∧
      (let a := morkPatternToAtom unitDualTargetCandidate.runtimeCandidate.artifact.pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  refine ⟨{ name := "unit", argCount := 0 }, ?_, rfl, rfl, ?_⟩
  · decide
  · change
      (let a := morkPatternToAtom (.apply "unit" [])
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a))
    simp [morkRuntimeQueryExec0, Mettapedia.Languages.ProcessCalculi.MORK.matchSourceFactor]
    apply Mettapedia.Languages.ProcessCalculi.MORK.matchOneInSpace_mem
    · simp
    · change
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom []
          (morkPatternToAtom (.apply "unit" []))
          (morkPatternToAtom (.apply "unit" [])) = some []
      simp [Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom]
      simp [Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom.morkPatternToAtomList,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom.matchAtomList]

theorem boolKernelExtension_has_queryCompatibleCtor :
    ∃ ctor, ctor ∈ boolKernelExtension.declaration.ctors ∧
      ctor.name = "true" ∧ ctor.argCount = 0 ∧
      (let a := morkPatternToAtom boolTrueDualTargetCandidate.runtimeCandidate.artifact.pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  refine ⟨{ name := "true", argCount := 0 }, ?_, rfl, rfl, ?_⟩
  · decide
  · change
      (let a := morkPatternToAtom (.apply "true" [])
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a))
    simp [morkRuntimeQueryExec0, Mettapedia.Languages.ProcessCalculi.MORK.matchSourceFactor]
    apply Mettapedia.Languages.ProcessCalculi.MORK.matchOneInSpace_mem
    · simp
    · change
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom []
          (morkPatternToAtom (.apply "true" []))
          (morkPatternToAtom (.apply "true" [])) = some []
      simp [Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom]
      simp [Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom.morkPatternToAtomList,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom.matchAtomList]

theorem natKernelExtension_has_queryCompatibleCtor :
    ∃ ctor, ctor ∈ natKernelExtension.declaration.ctors ∧
      ctor.name = "zero" ∧ ctor.argCount = 0 ∧
      (let a := morkPatternToAtom natZeroDualTargetCandidate.runtimeCandidate.artifact.pattern
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a)) := by
  refine ⟨{ name := "zero", argCount := 0 }, ?_, rfl, rfl, ?_⟩
  · decide
  · change
      (let a := morkPatternToAtom (.apply "zero" [])
       ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a))
    simp [morkRuntimeQueryExec0, Mettapedia.Languages.ProcessCalculi.MORK.matchSourceFactor]
    apply Mettapedia.Languages.ProcessCalculi.MORK.matchOneInSpace_mem
    · simp
    · change
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom []
          (morkPatternToAtom (.apply "zero" []))
          (morkPatternToAtom (.apply "zero" [])) = some []
      simp [Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom]
      simp [Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom.morkPatternToAtomList,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom.matchAtomList]

/-- Nullary constructor artifacts already fit the current query seam on the
default atomspace: if the translated constructor atom is present in the
workspace, querying for that exact atom succeeds with the empty substitution.

This is stronger than bare artifact agreement, but still weaker than a direct
rewrite/execution overlap. -/
theorem nullaryCtorPattern_queryCompatible (ctorName : String) :
    let pat : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern := .apply ctorName []
    let a := morkPatternToAtom pat
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  dsimp [morkRuntimeQueryExec0]
  simp [Mettapedia.Languages.ProcessCalculi.MORK.matchSourceFactor]
  apply Mettapedia.Languages.ProcessCalculi.MORK.matchOneInSpace_mem
  · simp
  · change
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom []
        (morkPatternToAtom (.apply ctorName []))
        (morkPatternToAtom (.apply ctorName [])) = some []
    simp [Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom]
    simp [Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
      Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom.morkPatternToAtomList,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom.matchAtomList]

theorem unitDualTargetCandidate_queryCompatible :
    let a := morkPatternToAtom unitDualTargetCandidate.runtimeCandidate.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [unitDualTargetCandidate, unitCtorCandidate] using
    nullaryCtorPattern_queryCompatible "unit"

theorem boolTrueDualTargetCandidate_queryCompatible :
    let a := morkPatternToAtom boolTrueDualTargetCandidate.runtimeCandidate.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [boolTrueDualTargetCandidate, boolTrueCtorCandidate] using
    nullaryCtorPattern_queryCompatible "true"

theorem natZeroDualTargetCandidate_queryCompatible :
    let a := morkPatternToAtom natZeroDualTargetCandidate.runtimeCandidate.artifact.pattern
    ([], a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] ({a}) (.btm a) := by
  simpa [natZeroDualTargetCandidate, natZeroCtorCandidate] using
    nullaryCtorPattern_queryCompatible "zero"

theorem unitOverlapBridge_artifactOnly :
    unitOverlapBridge.proofKernel.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem boolTrueOverlapBridge_artifactOnly :
    boolTrueOverlapBridge.proofKernel.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem natZeroOverlapBridge_artifactOnly :
    natZeroOverlapBridge.proofKernel.proofInterface.overlapClass = OverlapClass.artifactOnly := rfl

theorem unitOverlapBridge_runtimeTranslatable :
    morkTranslatable unitOverlapBridge.runtimeCandidate.artifact.pattern = true :=
  unitOverlapBridge.runtimeCandidate.runtimeTranslatable

theorem boolTrueOverlapBridge_runtimeTranslatable :
    morkTranslatable boolTrueOverlapBridge.runtimeCandidate.artifact.pattern = true :=
  boolTrueOverlapBridge.runtimeCandidate.runtimeTranslatable

theorem natZeroOverlapBridge_runtimeTranslatable :
    morkTranslatable natZeroOverlapBridge.runtimeCandidate.artifact.pattern = true :=
  natZeroOverlapBridge.runtimeCandidate.runtimeTranslatable

theorem starterInductives_haveProofKernelBridge :
    ∀ family ∈ [unitFamilySpec, boolFamilySpec, natFamilySpec],
      ∃ bridge : InductiveProofKernelBridge, bridge.proofInterface.family = family := by
  intro family hfamily
  simp at hfamily
  rcases hfamily with rfl | rfl | rfl
  · exact ⟨unitProofKernelBridge, rfl⟩
  · exact ⟨boolProofKernelBridge, rfl⟩
  · exact ⟨natProofKernelBridge, rfl⟩

/-- Current theoremic conclusion:
starter inductives already have a clean proof-lane interface, and some nullary
constructors already admit runtime-friendly artifact candidates, but no direct
proof/runtime overlap theorem is claimed yet. -/
theorem starterInductives_currently_artifactOnly :
    ∀ family ∈ starterInductiveFamilies,
      (starterFamilyInterface family).overlapClass = OverlapClass.artifactOnly := by
  intro family _hmem
  rfl

theorem starterInductives_refine_pureCheckingBoundary :
    ∀ family ∈ starterInductiveFamilies,
      (starterFamilyInterface family).region = pureCheckingBoundary.region ∧
      (starterFamilyInterface family).overlapClass = pureCheckingBoundary.overlapClass := by
  intro family _hmem
  constructor <;> rfl

end Mettapedia.Languages.MeTTa
