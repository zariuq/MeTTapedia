import Mettapedia.Languages.MeTTa.InductiveKernelSpec

/-!
# First Kernel-Facing Hook for Ordinary Strictly Positive Families

This file is the first implementation-oriented interface between the current
inductive-family specification layer and a future `MeTTa-Pure` kernel
extension.

It does **not** implement inductives in the kernel. It only packages the
minimal declaration shape we would want the future kernel to accept for the
ordinary strictly-positive family fragment.
-/

namespace Mettapedia.Languages.MeTTa

/-- Minimal constructor data that a future kernel hook should receive. -/
structure KernelCtorHook where
  name : String
  argCount : Nat
deriving DecidableEq, Repr

/-- Minimal family declaration shape for the first inductive-family kernel hook.

This is intentionally smaller than a full inductive declaration language:
- only ordinary, indexed, and record-like families
- only constructor arities, not full argument telescope syntax
- strict positivity is required at the spec boundary
- generated recursor support is assumed
- structural recursion is assumed
-/
structure InductiveKernelHook where
  familyName : String
  shape : InductiveShape
  parameterCount : Nat
  indexCount : Nat
  ctors : List KernelCtorHook
  generatesRecursor : Bool
  allowsStructuralRecursion : Bool
deriving DecidableEq, Repr

/-- A family spec is admissible for the first kernel hook exactly when it lives
inside the intended ordinary strictly-positive fragment. -/
def InductiveFamilySpec.admitsKernelHook (spec : InductiveFamilySpec) : Prop :=
  spec.strictlyPositive = true ∧
    spec.hasGeneratedRecursor = true ∧
    spec.allowsStructuralRecursion = true

instance (spec : InductiveFamilySpec) : Decidable spec.admitsKernelHook := by
  unfold InductiveFamilySpec.admitsKernelHook
  infer_instance

/-- Extract the first kernel-facing hook from an admissible family spec. -/
def InductiveFamilySpec.toKernelHook? (spec : InductiveFamilySpec) : Option InductiveKernelHook :=
  if _h : spec.admitsKernelHook then
    some
      { familyName := spec.name
        shape := spec.shape
        parameterCount := spec.parameterCount
        indexCount := spec.indexCount
        ctors := spec.ctors.map fun ctor => { name := ctor.name, argCount := ctor.argCount }
        generatesRecursor := true
        allowsStructuralRecursion := true }
  else
    none

/-- The first theoremic interface from the spec layer to the kernel-facing hook.

This packages the exact witness that the current family spec belongs to the
ordinary strictly-positive starter fragment. -/
structure InductiveKernelHookInterface where
  family : InductiveFamilySpec
  hook : InductiveKernelHook
  admissible : family.admitsKernelHook
  hook_eq : family.toKernelHook? = some hook

/-- First future-facing Pure-kernel interface object for ordinary strictly
positive families.

This sits one step above the raw kernel hook. It still does not implement
inductives in `MeTTa-Pure`, but it packages the precise commitments that a
future ordinary-family kernel extension would make:

- the family already admits the minimal kernel hook
- the hook generates a recursor
- structural recursion is permitted
- the family carries a named recursor contract stub for later implementation
-/
structure PureInductiveKernelInterface where
  hookInterface : InductiveKernelHookInterface
  recursorContractStub : String
  positivity_checked :
    hookInterface.family.strictlyPositive = true
  recursor_generated :
    hookInterface.hook.generatesRecursor = true
  structuralRecursion_enabled :
    hookInterface.hook.allowsStructuralRecursion = true

def PureInductiveKernelInterface.family
    (iface : PureInductiveKernelInterface) : InductiveFamilySpec :=
  iface.hookInterface.family

def PureInductiveKernelInterface.hook
    (iface : PureInductiveKernelInterface) : InductiveKernelHook :=
  iface.hookInterface.hook

theorem PureInductiveKernelInterface.familyName_eq
    (iface : PureInductiveKernelInterface) :
    iface.hook.familyName = iface.family.name := by
  rcases iface with ⟨hookIface, _, _, _, _⟩
  rcases hookIface with ⟨family, hook, hadm, hhook⟩
  unfold InductiveFamilySpec.toKernelHook? at hhook
  simp [hadm] at hhook
  have hname := congrArg InductiveKernelHook.familyName hhook
  simpa using hname.symm

theorem InductiveFamilySpec.toKernelHook?_eq_some
    {spec : InductiveFamilySpec} (h : spec.admitsKernelHook) :
    spec.toKernelHook? =
      some
        { familyName := spec.name
          shape := spec.shape
          parameterCount := spec.parameterCount
          indexCount := spec.indexCount
          ctors := spec.ctors.map fun ctor => { name := ctor.name, argCount := ctor.argCount }
          generatesRecursor := true
          allowsStructuralRecursion := true } := by
  unfold InductiveFamilySpec.toKernelHook?
  simp [h]

/-- Build the first kernel-hook interface from an admissible family spec. -/
def mkInductiveKernelHookInterface
    (spec : InductiveFamilySpec) (h : spec.admitsKernelHook) :
    InductiveKernelHookInterface :=
  { family := spec
    hook :=
      { familyName := spec.name
        shape := spec.shape
        parameterCount := spec.parameterCount
        indexCount := spec.indexCount
        ctors := spec.ctors.map fun ctor => { name := ctor.name, argCount := ctor.argCount }
        generatesRecursor := true
        allowsStructuralRecursion := true }
    admissible := h
    hook_eq := spec.toKernelHook?_eq_some h }

/-- Build the first future-facing Pure-kernel inductive interface from an
admissible family spec. -/
def mkPureInductiveKernelInterface
    (spec : InductiveFamilySpec) (h : spec.admitsKernelHook)
    (recursorContractStub : String) :
    PureInductiveKernelInterface :=
  let hookInterface := mkInductiveKernelHookInterface spec h
  { hookInterface := hookInterface
    recursorContractStub := recursorContractStub
    positivity_checked := by
      exact h.1
    recursor_generated := by
      simp [hookInterface, mkInductiveKernelHookInterface]
    structuralRecursion_enabled := by
      simp [hookInterface, mkInductiveKernelHookInterface] }

theorem starterFamilies_admitKernelHook :
    ∀ spec ∈ starterInductiveFamilies, spec.admitsKernelHook := by
  intro spec hspec
  simp [starterInductiveFamilies] at hspec
  rcases hspec with
    hspec | hspec | hspec | hspec | hspec | hspec | hspec | hspec
  all_goals
    subst hspec
    simp [InductiveFamilySpec.admitsKernelHook]

theorem starterFamilies_haveKernelHook :
    ∀ spec ∈ starterInductiveFamilies, ∃ hook, spec.toKernelHook? = some hook := by
  intro spec hspec
  refine ⟨_, spec.toKernelHook?_eq_some (starterFamilies_admitKernelHook spec hspec)⟩

/-- Concrete starter-family handles used by the first kernel hook. -/
def unitFamilySpec : InductiveFamilySpec :=
  { name := "Unit"
    shape := .recordLike
    parameterCount := 0
    indexCount := 0
    strictlyPositive := true
    hasGeneratedRecursor := true
    allowsStructuralRecursion := true
    ctors := [{ name := "unit", argCount := 0 }] }

def boolFamilySpec : InductiveFamilySpec :=
  { name := "Bool"
    shape := .ordinary
    parameterCount := 0
    indexCount := 0
    strictlyPositive := true
    hasGeneratedRecursor := true
    allowsStructuralRecursion := true
    ctors := [{ name := "false", argCount := 0 }, { name := "true", argCount := 0 }] }

def natFamilySpec : InductiveFamilySpec :=
  { name := "Nat"
    shape := .ordinary
    parameterCount := 0
    indexCount := 0
    strictlyPositive := true
    hasGeneratedRecursor := true
    allowsStructuralRecursion := true
    ctors := [{ name := "zero", argCount := 0 }, { name := "succ", argCount := 1 }] }

theorem unitFamilySpec_in_starterFamilies :
    unitFamilySpec ∈ starterInductiveFamilies := by
  simp [starterInductiveFamilies, unitFamilySpec]

theorem boolFamilySpec_in_starterFamilies :
    boolFamilySpec ∈ starterInductiveFamilies := by
  simp [starterInductiveFamilies, boolFamilySpec]

theorem natFamilySpec_in_starterFamilies :
    natFamilySpec ∈ starterInductiveFamilies := by
  simp [starterInductiveFamilies, natFamilySpec]

def unitKernelHookInterface : InductiveKernelHookInterface :=
  mkInductiveKernelHookInterface unitFamilySpec (starterFamilies_admitKernelHook _ unitFamilySpec_in_starterFamilies)

def boolKernelHookInterface : InductiveKernelHookInterface :=
  mkInductiveKernelHookInterface boolFamilySpec (starterFamilies_admitKernelHook _ boolFamilySpec_in_starterFamilies)

def natKernelHookInterface : InductiveKernelHookInterface :=
  mkInductiveKernelHookInterface natFamilySpec (starterFamilies_admitKernelHook _ natFamilySpec_in_starterFamilies)

def unitPureKernelInterface : PureInductiveKernelInterface :=
  mkPureInductiveKernelInterface
    unitFamilySpec
    (starterFamilies_admitKernelHook _ unitFamilySpec_in_starterFamilies)
    "Unit.rec"

def boolPureKernelInterface : PureInductiveKernelInterface :=
  mkPureInductiveKernelInterface
    boolFamilySpec
    (starterFamilies_admitKernelHook _ boolFamilySpec_in_starterFamilies)
    "Bool.rec"

def natPureKernelInterface : PureInductiveKernelInterface :=
  mkPureInductiveKernelInterface
    natFamilySpec
    (starterFamilies_admitKernelHook _ natFamilySpec_in_starterFamilies)
    "Nat.rec"

theorem unitKernelHook_familyName :
    unitKernelHookInterface.hook.familyName = "Unit" := by
  simp [unitKernelHookInterface, mkInductiveKernelHookInterface, unitFamilySpec]

theorem boolKernelHook_familyName :
    boolKernelHookInterface.hook.familyName = "Bool" := by
  simp [boolKernelHookInterface, mkInductiveKernelHookInterface, boolFamilySpec]

theorem natKernelHook_familyName :
    natKernelHookInterface.hook.familyName = "Nat" := by
  simp [natKernelHookInterface, mkInductiveKernelHookInterface, natFamilySpec]

theorem unitKernelHook_shape :
    unitKernelHookInterface.hook.shape = .recordLike := by
  simp [unitKernelHookInterface, mkInductiveKernelHookInterface, unitFamilySpec]

theorem boolKernelHook_ctorCount :
    boolKernelHookInterface.hook.ctors.length = 2 := by
  simp [boolKernelHookInterface, mkInductiveKernelHookInterface, boolFamilySpec]

theorem natKernelHook_ctorCount :
    natKernelHookInterface.hook.ctors.length = 2 := by
  simp [natKernelHookInterface, mkInductiveKernelHookInterface, natFamilySpec]

theorem unitKernelHook_generatesRecursor :
    unitKernelHookInterface.hook.generatesRecursor = true := by
  simp [unitKernelHookInterface, mkInductiveKernelHookInterface, unitFamilySpec]

theorem boolKernelHook_allowsStructuralRecursion :
    boolKernelHookInterface.hook.allowsStructuralRecursion = true := by
  simp [boolKernelHookInterface, mkInductiveKernelHookInterface, boolFamilySpec]

theorem natKernelHook_allowsStructuralRecursion :
    natKernelHookInterface.hook.allowsStructuralRecursion = true := by
  simp [natKernelHookInterface, mkInductiveKernelHookInterface, natFamilySpec]

theorem unitPureKernelInterface_recursorStub :
    unitPureKernelInterface.recursorContractStub = "Unit.rec" := rfl

theorem boolPureKernelInterface_recursorStub :
    boolPureKernelInterface.recursorContractStub = "Bool.rec" := rfl

theorem natPureKernelInterface_recursorStub :
    natPureKernelInterface.recursorContractStub = "Nat.rec" := rfl

theorem unitPureKernelInterface_familyName :
    unitPureKernelInterface.family.name = "Unit" := by
  simp [unitPureKernelInterface, PureInductiveKernelInterface.family,
    mkPureInductiveKernelInterface, mkInductiveKernelHookInterface, unitFamilySpec]

theorem boolPureKernelInterface_familyName :
    boolPureKernelInterface.family.name = "Bool" := by
  simp [boolPureKernelInterface, PureInductiveKernelInterface.family,
    mkPureInductiveKernelInterface, mkInductiveKernelHookInterface, boolFamilySpec]

theorem natPureKernelInterface_familyName :
    natPureKernelInterface.family.name = "Nat" := by
  simp [natPureKernelInterface, PureInductiveKernelInterface.family,
    mkPureInductiveKernelInterface, mkInductiveKernelHookInterface, natFamilySpec]

end Mettapedia.Languages.MeTTa
