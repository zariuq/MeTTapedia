import Mettapedia.Languages.MeTTa.InductiveKernelBoundary
import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationPilotScaffold
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationRecursorPilot

/-!
# Ordinary-Family Kernel Extension Point

This file packages the first future-facing ordinary-family declaration object
above the current hook/boundary stack.

The live trusted `PureKernel` remains the small Pi/Sigma/Id/universe core.
This file does **not** implement inductive families in that kernel. It makes
the next implementation-facing contract explicit:

- what declaration data the future kernel extension should accept,
- how that declaration refines the current ordinary-family boundary,
- how it plugs into the current proof-side checking boundary.
-/

namespace Mettapedia.Languages.MeTTa

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationPilotScaffold
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationUnitPilot
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationBoolPilot
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationNatPilot
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationRecursorPilot

/-- Minimal declaration object for the first ordinary-family kernel extension. -/
structure OrdinaryFamilyDeclaration where
  familyName : String
  shape : InductiveShape
  parameterCount : Nat
  indexCount : Nat
  ctors : List KernelCtorHook
  recursorName : String
deriving DecidableEq, Repr

/-- Typed constructor declaration for the implementation-facing ordinary-family
extension path. This is the typed replacement target for arity-only constructor
hooks. -/
structure TypedCtorDeclaration where
  name : DeclName
  type : PureTm 0
  argumentTelescope : List (PureTm 0)
deriving DecidableEq, Repr

def TypedCtorDeclaration.argumentCount (ctor : TypedCtorDeclaration) : Nat :=
  ctor.argumentTelescope.length

/-- Typed recursor schema for a declared ordinary family. -/
structure TypedRecursorSchema where
  name : DeclName
  type : PureTm 0
  equationSchemaNames : List String
  equationCoverageComplete : Bool
deriving DecidableEq, Repr

/-- Typed ordinary-family declaration object.

This is the intended replacement target for the arity-only declaration shell:
constructor and recursor types are explicit `PureTm 0` objects. -/
structure OrdinaryFamilyTypedDeclaration where
  familyName : DeclName
  familyType : PureTm 0
  shape : InductiveShape
  parameterCount : Nat
  indexCount : Nat
  constructors : List TypedCtorDeclaration
  recursor : TypedRecursorSchema
deriving DecidableEq, Repr

/-- Coherence relation between the legacy arity shell and the typed declaration
object. -/
structure OrdinaryFamilyTypedCoherence where
  legacy : OrdinaryFamilyDeclaration
  typed : OrdinaryFamilyTypedDeclaration
  familyName_agrees : typed.familyName.toString = legacy.familyName
  ctorCount_agrees : typed.constructors.length = legacy.ctors.length
  recursorName_agrees : typed.recursor.name.toString = legacy.recursorName
deriving Repr

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

/-- Typed Unit declaration pilot (constructor/recursor types explicit). -/
def unitTypedDeclaration : OrdinaryFamilyTypedDeclaration :=
  { familyName := unitTyName
    familyType := .u0
    shape := .recordLike
    parameterCount := 0
    indexCount := 0
    constructors :=
      [ { name := unitCtorName
          type := .const unitTyName
          argumentTelescope := [] } ]
    recursor :=
      { name := unitRecName
        type := unitRecType
        equationSchemaNames := ["Unit.rec.beta_unit"]
        equationCoverageComplete := true } }

/-- Typed Bool declaration pilot (constructor/recursor types explicit). -/
def boolTypedDeclaration : OrdinaryFamilyTypedDeclaration :=
  { familyName := boolTyName
    familyType := .u0
    shape := .ordinary
    parameterCount := 0
    indexCount := 0
    constructors :=
      [ { name := boolFalseName
          type := .const boolTyName
          argumentTelescope := [] }
      , { name := boolTrueName
          type := .const boolTyName
          argumentTelescope := [] } ]
    recursor :=
      { name := boolRecName
        type := boolRecType
        equationSchemaNames := ["Bool.rec.beta_false", "Bool.rec.beta_true"]
        equationCoverageComplete := false } }

/-- Typed Nat declaration pilot (constructor/recursor types explicit). -/
def natTypedDeclaration : OrdinaryFamilyTypedDeclaration :=
  { familyName := natTyName
    familyType := .u0
    shape := .ordinary
    parameterCount := 0
    indexCount := 0
    constructors :=
      [ { name := natZeroName
          type := .const natTyName
          argumentTelescope := [] }
      , { name := natSuccName
          type := .pi (.const natTyName) (.const natTyName)
          argumentTelescope := [.const natTyName] } ]
    recursor :=
      { name := natRecName
        type := natRecType
        equationSchemaNames := ["Nat.rec.beta_zero", "Nat.rec.beta_succ"]
        equationCoverageComplete := false } }

/-- Family constant declaration generated from a typed ordinary-family declaration. -/
def OrdinaryFamilyTypedDeclaration.familySpec
    (decl : OrdinaryFamilyTypedDeclaration) : DeclSpec :=
  { name := decl.familyName
    type := decl.familyType
    value? := none }

/-- Constructor declarations generated from a typed ordinary-family declaration. -/
def OrdinaryFamilyTypedDeclaration.constructorSpecs
    (decl : OrdinaryFamilyTypedDeclaration) : List DeclSpec :=
  decl.constructors.map (fun ctor =>
    { name := ctor.name
      type := ctor.type
      value? := none })

/-- Recursor declaration generated from a typed ordinary-family declaration. -/
def OrdinaryFamilyTypedDeclaration.recursorSpec
    (decl : OrdinaryFamilyTypedDeclaration) : DeclSpec :=
  { name := decl.recursor.name
    type := decl.recursor.type
    value? := none }

/-- Declaration specs induced by a typed ordinary-family declaration.
This is the single lowering boundary from typed family metadata to kernel
declaration entries. -/
def OrdinaryFamilyTypedDeclaration.toDeclSpecs
    (decl : OrdinaryFamilyTypedDeclaration) : List DeclSpec :=
  decl.familySpec :: (decl.constructorSpecs ++ [decl.recursorSpec])

/-- Declaration environment induced by a typed ordinary-family declaration. -/
def OrdinaryFamilyTypedDeclaration.toDeclEnv
    (decl : OrdinaryFamilyTypedDeclaration) : DeclEnv :=
  envOfSpecs decl.toDeclSpecs

theorem OrdinaryFamilyTypedDeclaration.toDeclSpecs_valuesNone
    (decl : OrdinaryFamilyTypedDeclaration) :
    ∀ s ∈ decl.toDeclSpecs, s.value? = none := by
  intro s hs
  have hs' :
      s = decl.familySpec ∨ s ∈ (decl.constructorSpecs ++ [decl.recursorSpec]) := by
    simpa [OrdinaryFamilyTypedDeclaration.toDeclSpecs] using hs
  rcases hs' with rfl | hsRest
  · simp [OrdinaryFamilyTypedDeclaration.familySpec]
  · rcases List.mem_append.mp hsRest with hsCtor | hsRec
    · unfold OrdinaryFamilyTypedDeclaration.constructorSpecs at hsCtor
      rcases List.mem_map.mp hsCtor with ⟨ctor, _, rfl⟩
      simp
    · simp [OrdinaryFamilyTypedDeclaration.recursorSpec] at hsRec
      rcases hsRec with rfl
      simp

@[simp] theorem OrdinaryFamilyTypedDeclaration.valueOf_toDeclEnv_none
    (decl : OrdinaryFamilyTypedDeclaration) (c : DeclName) :
    valueOf? decl.toDeclEnv c = none := by
  exact valueOf_envOfSpecs_eq_none_of_all_none
    decl.toDeclSpecs
    (OrdinaryFamilyTypedDeclaration.toDeclSpecs_valuesNone decl)
    c

theorem OrdinaryFamilyTypedDeclaration.toDeclEnv_wellFormed
    (decl : OrdinaryFamilyTypedDeclaration) :
    DeclEnvWellFormed decl.toDeclEnv := by
  exact envOfSpecs_wellFormed_of_all_none
    decl.toDeclSpecs
    (OrdinaryFamilyTypedDeclaration.toDeclSpecs_valuesNone decl)

def unitTypedDeclEnv : DeclEnv := unitTypedDeclaration.toDeclEnv
def boolTypedDeclEnv : DeclEnv := boolTypedDeclaration.toDeclEnv
def natTypedDeclEnv : DeclEnv := natTypedDeclaration.toDeclEnv

@[simp] theorem typeOf_unitTypedDeclEnv_unitTy :
    typeOf? unitTypedDeclEnv unitTyName = some .u0 := by
  native_decide

@[simp] theorem typeOf_unitTypedDeclEnv_unitCtor :
    typeOf? unitTypedDeclEnv unitCtorName = some (.const unitTyName) := by
  native_decide

@[simp] theorem typeOf_unitTypedDeclEnv_unitRec :
    typeOf? unitTypedDeclEnv unitRecName = some unitRecType := by
  native_decide

theorem hasType_unitTypedDeclEnv_unitTy :
    HasTypeDecl unitTypedDeclEnv .nil (.const unitTyName) .u0 := by
  have hLookup : typeOf? unitTypedDeclEnv unitTyName = some .u0 := by
    simp
  simpa using hasType_const_from_lookup
    (E := unitTypedDeclEnv) (Γ := .nil) (c := unitTyName) (A0 := .u0)
    hLookup

theorem hasType_unitTypedDeclEnv_unitCtor :
    HasTypeDecl unitTypedDeclEnv .nil (.const unitCtorName) (.const unitTyName) := by
  have hLookup : typeOf? unitTypedDeclEnv unitCtorName = some (.const unitTyName) := by
    simp
  simpa using hasType_const_from_lookup
    (E := unitTypedDeclEnv) (Γ := .nil) (c := unitCtorName) (A0 := .const unitTyName)
    hLookup

theorem hasType_unitTypedDeclEnv_unitRec :
    HasTypeDecl unitTypedDeclEnv .nil (.const unitRecName) unitRecType := by
  have hLookup : typeOf? unitTypedDeclEnv unitRecName = some unitRecType := by
    simp
  simpa using hasType_const_from_lookup
    (E := unitTypedDeclEnv) (Γ := .nil) (c := unitRecName) (A0 := unitRecType)
    hLookup

@[simp] theorem valueOf_unitTypedDeclEnv_none (c : DeclName) :
    valueOf? unitTypedDeclEnv c = none := by
  simp [unitTypedDeclEnv]

@[simp] theorem valueOf_boolTypedDeclEnv_none (c : DeclName) :
    valueOf? boolTypedDeclEnv c = none := by
  simp [boolTypedDeclEnv]

@[simp] theorem valueOf_natTypedDeclEnv_none (c : DeclName) :
    valueOf? natTypedDeclEnv c = none := by
  simp [natTypedDeclEnv]

theorem unitTypedDeclEnv_wellFormed : DeclEnvWellFormed unitTypedDeclEnv := by
  simpa [unitTypedDeclEnv] using
    OrdinaryFamilyTypedDeclaration.toDeclEnv_wellFormed unitTypedDeclaration

theorem boolTypedDeclEnv_wellFormed : DeclEnvWellFormed boolTypedDeclEnv := by
  simpa [boolTypedDeclEnv] using
    OrdinaryFamilyTypedDeclaration.toDeclEnv_wellFormed boolTypedDeclaration

theorem natTypedDeclEnv_wellFormed : DeclEnvWellFormed natTypedDeclEnv := by
  simpa [natTypedDeclEnv] using
    OrdinaryFamilyTypedDeclaration.toDeclEnv_wellFormed natTypedDeclaration

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

def unitTypedCoherence : OrdinaryFamilyTypedCoherence :=
  { legacy := unitKernelExtension.declaration
    typed := unitTypedDeclaration
    familyName_agrees := by native_decide
    ctorCount_agrees := rfl
    recursorName_agrees := by native_decide }

def boolTypedCoherence : OrdinaryFamilyTypedCoherence :=
  { legacy := boolKernelExtension.declaration
    typed := boolTypedDeclaration
    familyName_agrees := by native_decide
    ctorCount_agrees := rfl
    recursorName_agrees := by native_decide }

def natTypedCoherence : OrdinaryFamilyTypedCoherence :=
  { legacy := natKernelExtension.declaration
    typed := natTypedDeclaration
    familyName_agrees := by native_decide
    ctorCount_agrees := rfl
    recursorName_agrees := by native_decide }

theorem unitTypedDeclaration_eqnCoverageComplete :
    unitTypedDeclaration.recursor.equationCoverageComplete = true := rfl

theorem boolTypedDeclaration_eqnCoverageComplete :
    boolTypedDeclaration.recursor.equationCoverageComplete = false := rfl

theorem natTypedDeclaration_eqnCoverageComplete :
    natTypedDeclaration.recursor.equationCoverageComplete = false := rfl

theorem natSuccTypedConstructor_argCount :
    (natTypedDeclaration.constructors.get ⟨1, by decide⟩).argumentCount = 1 := by
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
