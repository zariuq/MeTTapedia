import Mettapedia.Languages.MeTTa.PureCheckingExtensions

/-!
# Ordinary-Family and Structural-Fixpoint Recursor Contracts

This file replaces the bare "recursor name stub" story with the first explicit,
implementation-facing recursor contracts for the starter ordinary families and
their staged structural fixpoints.

It still does **not** implement inductives or fixpoints in `MeTTa-Pure`.
It makes the next kernel-facing contract more precise.
-/

namespace Mettapedia.Languages.MeTTa

/-- Minimal implementation-facing contract for an ordinary-family recursor. -/
structure FamilyRecursorContract where
  recursorName : String
  familyName : String
  motiveArity : Nat
  minorPremiseCount : Nat
  majorPremiseIndex : Nat
  constructorNames : List String
  allowsDependentMotive : Bool
  derivesEquationTheorems : Bool
deriving DecidableEq, Repr

/-- Extract the first explicit recursor contract from a Pure inductive kernel
interface. -/
def PureInductiveKernelInterface.toRecursorContract
    (iface : PureInductiveKernelInterface) : FamilyRecursorContract :=
  { recursorName := iface.recursorContractStub
    familyName := iface.family.name
    motiveArity := 1
    minorPremiseCount := iface.family.ctors.length
    majorPremiseIndex := 0
    constructorNames := iface.family.ctors.map InductiveCtorSpec.name
    allowsDependentMotive := true
    derivesEquationTheorems := true }

theorem PureInductiveKernelInterface.toRecursorContract_name
    (iface : PureInductiveKernelInterface) :
    iface.toRecursorContract.recursorName = iface.recursorContractStub := rfl

theorem PureInductiveKernelInterface.toRecursorContract_family
    (iface : PureInductiveKernelInterface) :
    iface.toRecursorContract.familyName = iface.family.name := rfl

theorem PureInductiveKernelInterface.toRecursorContract_minorPremises
    (iface : PureInductiveKernelInterface) :
    iface.toRecursorContract.minorPremiseCount = iface.family.ctors.length := rfl

theorem PureInductiveKernelInterface.toRecursorContract_constructors
    (iface : PureInductiveKernelInterface) :
    iface.toRecursorContract.constructorNames = iface.family.ctors.map InductiveCtorSpec.name := rfl

/-- The current implementation-facing family extension refines an explicit
recursor contract. -/
def OrdinaryFamilyKernelExtension.recursorContract
    (ext : OrdinaryFamilyKernelExtension) : FamilyRecursorContract :=
  ext.kernelBoundary.kernelInterface.toRecursorContract

theorem OrdinaryFamilyKernelExtension.recursorContract_name
    (ext : OrdinaryFamilyKernelExtension) :
    ext.recursorContract.recursorName = ext.declaration.recursorName := by
  simpa [OrdinaryFamilyKernelExtension.recursorContract,
    PureInductiveKernelInterface.toRecursorContract_name] using ext.recursorName_eq.symm

theorem OrdinaryFamilyKernelExtension.recursorContract_family
    (ext : OrdinaryFamilyKernelExtension) :
    ext.recursorContract.familyName = ext.declaration.familyName := by
  simpa [OrdinaryFamilyKernelExtension.recursorContract,
    PureInductiveKernelInterface.toRecursorContract_family] using ext.familyName_eq.symm

def unitRecursorContract : FamilyRecursorContract :=
  unitPureKernelInterface.toRecursorContract

def boolRecursorContract : FamilyRecursorContract :=
  boolPureKernelInterface.toRecursorContract

def natRecursorContract : FamilyRecursorContract :=
  natPureKernelInterface.toRecursorContract

theorem unitRecursorContract_name :
    unitRecursorContract.recursorName = "Unit.rec" := rfl

theorem boolRecursorContract_name :
    boolRecursorContract.recursorName = "Bool.rec" := rfl

theorem natRecursorContract_name :
    natRecursorContract.recursorName = "Nat.rec" := rfl

theorem unitRecursorContract_minorPremiseCount :
    unitRecursorContract.minorPremiseCount = 1 := rfl

theorem boolRecursorContract_minorPremiseCount :
    boolRecursorContract.minorPremiseCount = 2 := rfl

theorem natRecursorContract_minorPremiseCount :
    natRecursorContract.minorPremiseCount = 2 := rfl

theorem unitRecursorContract_constructorNames :
    unitRecursorContract.constructorNames = ["unit"] := rfl

theorem boolRecursorContract_constructorNames :
    boolRecursorContract.constructorNames = ["false", "true"] := rfl

theorem natRecursorContract_constructorNames :
    natRecursorContract.constructorNames = ["zero", "succ"] := rfl

theorem unitKernelExtension_refines_recursorContract :
    unitKernelExtension.recursorContract = unitRecursorContract := rfl

theorem boolKernelExtension_refines_recursorContract :
    boolKernelExtension.recursorContract = boolRecursorContract := rfl

theorem natKernelExtension_refines_recursorContract :
    natKernelExtension.recursorContract = natRecursorContract := rfl

/-- Minimal implementation-facing contract for the first structural fixpoints. -/
structure StructuralFixpointRecursorContract where
  functionName : String
  domainFamilyName : String
  codomainFamilyName : String
  familyRecursor : FamilyRecursorContract
  majorArgumentIndex : Nat
  equationTheoremName : String
  recursionKind : FixpointRecursionKind
  erasureKind : FixpointErasureKind
deriving DecidableEq, Repr

def StructuralFixpointKernelInterface.toRecursorContract
    (iface : StructuralFixpointKernelInterface) : StructuralFixpointRecursorContract :=
  { functionName := iface.hook.functionName
    domainFamilyName := iface.domain.family.name
    codomainFamilyName := iface.hook.codomainFamilyName
    familyRecursor := iface.domain.toRecursorContract
    majorArgumentIndex := iface.hook.majorArgumentIndex
    equationTheoremName := iface.hook.equationTheoremStub
    recursionKind := iface.hook.recursionKind
    erasureKind := iface.hook.erasureKind }

theorem StructuralFixpointKernelInterface.toRecursorContract_functionName
    (iface : StructuralFixpointKernelInterface) :
    iface.toRecursorContract.functionName = iface.hook.functionName := rfl

theorem StructuralFixpointKernelInterface.toRecursorContract_familyRecursor
    (iface : StructuralFixpointKernelInterface) :
    iface.toRecursorContract.familyRecursor = iface.domain.toRecursorContract := rfl

def natIsZeroRecursorContract : StructuralFixpointRecursorContract :=
  natIsZeroFixpointInterface.toRecursorContract

def natPredRecursorContract : StructuralFixpointRecursorContract :=
  natPredFixpointInterface.toRecursorContract

theorem natIsZeroRecursorContract_name :
    natIsZeroRecursorContract.functionName = "Nat.isZero" := rfl

theorem natPredRecursorContract_name :
    natPredRecursorContract.functionName = "Nat.pred" := rfl

theorem natIsZeroRecursorContract_recursor :
    natIsZeroRecursorContract.familyRecursor = natRecursorContract := rfl

theorem natPredRecursorContract_recursor :
    natPredRecursorContract.familyRecursor = natRecursorContract := rfl

theorem natIsZeroRecursorContract_equation :
    natIsZeroRecursorContract.equationTheoremName = "Nat.isZero.eqns" := rfl

theorem natPredRecursorContract_equation :
    natPredRecursorContract.equationTheoremName = "Nat.pred.eqns" := rfl

theorem natIsZeroRecursorContract_structural :
    natIsZeroRecursorContract.recursionKind = .structural := rfl

theorem natPredRecursorContract_structural :
    natPredRecursorContract.recursionKind = .structural := rfl

/-- Checked ordinary families now expose explicit recursor contracts through the
implementation-facing checking lane. -/
def CheckedOrdinaryFamily.recursorContract
    (fam : CheckedOrdinaryFamily) : FamilyRecursorContract :=
  fam.extension.recursorContract

theorem checkedUnitFamily_recursorContract :
    checkedUnitFamily.recursorContract = unitRecursorContract := rfl

theorem checkedBoolFamily_recursorContract :
    checkedBoolFamily.recursorContract = boolRecursorContract := rfl

theorem checkedNatFamily_recursorContract :
    checkedNatFamily.recursorContract = natRecursorContract := rfl

/-- Checked structural fixpoints expose the first explicit recursor/equation
contract. -/
def CheckedStructuralFixpoint.recursorContract
    (fp : CheckedStructuralFixpoint) : StructuralFixpointRecursorContract :=
  fp.iface.toRecursorContract

theorem checkedNatIsZeroFixpoint_recursorContract :
    checkedNatIsZeroFixpoint.recursorContract = natIsZeroRecursorContract := rfl

theorem checkedNatPredFixpoint_recursorContract :
    checkedNatPredFixpoint.recursorContract = natPredRecursorContract := rfl

end Mettapedia.Languages.MeTTa
