import Mettapedia.Languages.MeTTa.InductiveKernelBoundary
import Mettapedia.Languages.MeTTa.PureCheckingService

/-!
# Ordinary-Family Kernel Extension Point

This file packages the first future-facing ordinary-family declaration object
above the current hook/boundary stack.

It does **not** implement inductive families in `MeTTa-Pure`. It makes the
next implementation-facing contract explicit:

- what declaration data the future kernel extension should accept,
- how that declaration refines the current ordinary-family boundary,
- how it plugs into the current proof-side checking boundary.
-/

namespace Mettapedia.Languages.MeTTa

open Mettapedia.Languages.MeTTa.ElaboratedCore

/-- Minimal declaration object for the first ordinary-family kernel extension. -/
structure OrdinaryFamilyDeclaration where
  familyName : String
  shape : InductiveShape
  parameterCount : Nat
  indexCount : Nat
  ctors : List KernelCtorHook
  recursorName : String
deriving DecidableEq, Repr

/-- Extract the first implementation-facing declaration object from a
future-facing Pure inductive kernel interface. -/
def PureInductiveKernelInterface.toFamilyDeclaration
    (iface : PureInductiveKernelInterface) : OrdinaryFamilyDeclaration :=
  { familyName := iface.hook.familyName
    shape := iface.hook.shape
    parameterCount := iface.hook.parameterCount
    indexCount := iface.hook.indexCount
    ctors := iface.hook.ctors
    recursorName := iface.recursorContractStub }

theorem PureInductiveKernelInterface.toFamilyDeclaration_familyName
    (iface : PureInductiveKernelInterface) :
    iface.toFamilyDeclaration.familyName = iface.family.name := by
  simpa [PureInductiveKernelInterface.toFamilyDeclaration] using iface.familyName_eq

theorem PureInductiveKernelInterface.toFamilyDeclaration_shape
    (iface : PureInductiveKernelInterface) :
    iface.toFamilyDeclaration.shape = iface.family.shape := by
  rcases iface with ⟨hookIface, _, _, _, _⟩
  rcases hookIface with ⟨family, hook, hadm, hhook⟩
  unfold PureInductiveKernelInterface.toFamilyDeclaration
  unfold InductiveFamilySpec.toKernelHook? at hhook
  simp [hadm] at hhook
  have hshape := congrArg InductiveKernelHook.shape hhook
  simpa using hshape.symm

theorem PureInductiveKernelInterface.toFamilyDeclaration_parameterCount
    (iface : PureInductiveKernelInterface) :
    iface.toFamilyDeclaration.parameterCount = iface.family.parameterCount := by
  rcases iface with ⟨hookIface, _, _, _, _⟩
  rcases hookIface with ⟨family, hook, hadm, hhook⟩
  unfold PureInductiveKernelInterface.toFamilyDeclaration
  unfold InductiveFamilySpec.toKernelHook? at hhook
  simp [hadm] at hhook
  have hparam := congrArg InductiveKernelHook.parameterCount hhook
  simpa using hparam.symm

theorem PureInductiveKernelInterface.toFamilyDeclaration_indexCount
    (iface : PureInductiveKernelInterface) :
    iface.toFamilyDeclaration.indexCount = iface.family.indexCount := by
  rcases iface with ⟨hookIface, _, _, _, _⟩
  rcases hookIface with ⟨family, hook, hadm, hhook⟩
  unfold PureInductiveKernelInterface.toFamilyDeclaration
  unfold InductiveFamilySpec.toKernelHook? at hhook
  simp [hadm] at hhook
  have hidx := congrArg InductiveKernelHook.indexCount hhook
  simpa using hidx.symm

theorem PureInductiveKernelInterface.toFamilyDeclaration_ctors
    (iface : PureInductiveKernelInterface) :
    iface.toFamilyDeclaration.ctors =
      iface.family.ctors.map (fun ctor => { name := ctor.name, argCount := ctor.argCount }) := by
  rcases iface with ⟨hookIface, _, _, _, _⟩
  rcases hookIface with ⟨family, hook, hadm, hhook⟩
  unfold PureInductiveKernelInterface.toFamilyDeclaration
  unfold InductiveFamilySpec.toKernelHook? at hhook
  simp [hadm] at hhook
  have hctors := congrArg InductiveKernelHook.ctors hhook
  simpa using hctors.symm

theorem PureInductiveKernelInterface.toFamilyDeclaration_recursorName
    (iface : PureInductiveKernelInterface) :
    iface.toFamilyDeclaration.recursorName = iface.recursorContractStub := by
  rfl

/-- First implementation-facing extension point for ordinary families.

This sits above the current kernel boundary and below a future actual
inductive-family kernel implementation.
-/
structure OrdinaryFamilyKernelExtension where
  declaration : OrdinaryFamilyDeclaration
  kernelBoundary : InductiveKernelBoundary
  checkingBoundary : PureCheckingBoundary
  familyName_eq :
    declaration.familyName = kernelBoundary.kernelInterface.family.name
  recursorName_eq :
    declaration.recursorName = kernelBoundary.kernelInterface.recursorContractStub
  region_eq :
    checkingBoundary.region = kernelBoundary.region
  overlap_eq :
    checkingBoundary.overlapClass = kernelBoundary.overlapClass

/-- Build the current extension point from the future-facing Pure inductive
kernel interface and the canonical Pure checking boundary. -/
def PureInductiveKernelInterface.toKernelExtension
    (iface : PureInductiveKernelInterface) : OrdinaryFamilyKernelExtension :=
  { declaration := iface.toFamilyDeclaration
    kernelBoundary := iface.toKernelBoundary
    checkingBoundary := pureCheckingBoundary
    familyName_eq := iface.toFamilyDeclaration_familyName
    recursorName_eq := by
      rfl
    region_eq := by rfl
    overlap_eq := by rfl }

theorem PureInductiveKernelInterface.toKernelExtension_region
    (iface : PureInductiveKernelInterface) :
    iface.toKernelExtension.checkingBoundary.region = .pureKernelRegion := by
  rfl

theorem PureInductiveKernelInterface.toKernelExtension_overlap
    (iface : PureInductiveKernelInterface) :
    iface.toKernelExtension.checkingBoundary.overlapClass = .artifactOnly := by
  rfl

theorem PureInductiveKernelInterface.toKernelExtension_supports_closedTyping
    (iface : PureInductiveKernelInterface) :
    PureJudgmentKind.closedTyping ∈
      iface.toKernelExtension.checkingBoundary.supportedJudgments := by
  exact pureCheckingBoundary_supports_closedTyping

theorem PureInductiveKernelInterface.toKernelExtension_supports_artifactAgreement
    (iface : PureInductiveKernelInterface) :
    PureJudgmentKind.quotedArtifactAgreement ∈
      iface.toKernelExtension.checkingBoundary.supportedJudgments := by
  exact pureCheckingBoundary_supports_quotedArtifactAgreement

def unitKernelExtension : OrdinaryFamilyKernelExtension :=
  unitPureKernelInterface.toKernelExtension

def boolKernelExtension : OrdinaryFamilyKernelExtension :=
  boolPureKernelInterface.toKernelExtension

def natKernelExtension : OrdinaryFamilyKernelExtension :=
  natPureKernelInterface.toKernelExtension

theorem unitKernelExtension_familyName :
    unitKernelExtension.declaration.familyName = "Unit" := by
  exact unitPureKernelInterface.toFamilyDeclaration_familyName

theorem boolKernelExtension_familyName :
    boolKernelExtension.declaration.familyName = "Bool" := by
  exact boolPureKernelInterface.toFamilyDeclaration_familyName

theorem natKernelExtension_familyName :
    natKernelExtension.declaration.familyName = "Nat" := by
  exact natPureKernelInterface.toFamilyDeclaration_familyName

theorem unitKernelExtension_recursorName :
    unitKernelExtension.declaration.recursorName = "Unit.rec" := by
  rfl

theorem boolKernelExtension_recursorName :
    boolKernelExtension.declaration.recursorName = "Bool.rec" := by
  rfl

theorem natKernelExtension_recursorName :
    natKernelExtension.declaration.recursorName = "Nat.rec" := by
  rfl

theorem unitKernelExtension_ctorCount :
    unitKernelExtension.declaration.ctors.length = 1 := by
  rfl

theorem boolKernelExtension_ctorCount :
    boolKernelExtension.declaration.ctors.length = 2 := by
  rfl

theorem natKernelExtension_ctorCount :
    natKernelExtension.declaration.ctors.length = 2 := by
  rfl

theorem unitKernelExtension_refines_pureCheckingBoundary :
    unitKernelExtension.checkingBoundary.region = pureCheckingBoundary.region ∧
      unitKernelExtension.checkingBoundary.overlapClass =
        pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem boolKernelExtension_refines_pureCheckingBoundary :
    boolKernelExtension.checkingBoundary.region = pureCheckingBoundary.region ∧
      boolKernelExtension.checkingBoundary.overlapClass =
        pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

theorem natKernelExtension_refines_pureCheckingBoundary :
    natKernelExtension.checkingBoundary.region = pureCheckingBoundary.region ∧
      natKernelExtension.checkingBoundary.overlapClass =
        pureCheckingBoundary.overlapClass := by
  constructor <;> rfl

end Mettapedia.Languages.MeTTa
