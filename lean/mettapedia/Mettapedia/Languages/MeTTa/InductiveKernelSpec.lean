import Mettapedia.Languages.MeTTa.PureCertificateFragment

/-!
# Minimal Inductive-Family Kernel Specification

This file records the next intended kernel-contract widening for `MeTTa-Pure`,
without pretending it is already implemented.

The goal is to state, in Lean-facing terms, the smallest Lean/Coq-like
inductive extension we want to stabilize early:

- strictly positive inductive families,
- parameters and indices,
- generated recursors/eliminators,
- structures as one-constructor inductives,
- structural recursion only.

This is a specification layer, not a proof that the current kernel already
supports these features.
-/

namespace Mettapedia.Languages.MeTTa

/-- The minimal shape classes we want early in the kernel contract. -/
inductive InductiveShape where
  | ordinary
  | indexed
  | recordLike
deriving DecidableEq, Repr

def InductiveShape.name : InductiveShape → String
  | .ordinary => "ordinary"
  | .indexed => "indexed"
  | .recordLike => "record-like"

/-- A minimal constructor specification for the planned inductive-family lane. -/
structure InductiveCtorSpec where
  name : String
  argCount : Nat

/-- Minimal specification for one inductive family declaration.

This remains intentionally small:
- a family name
- number of parameters
- number of indices
- strict positivity discipline
- whether a generated eliminator is expected
- whether structural recursion is admitted
- constructors
-/
structure InductiveFamilySpec where
  name : String
  shape : InductiveShape
  parameterCount : Nat
  indexCount : Nat
  strictlyPositive : Bool
  hasGeneratedRecursor : Bool
  allowsStructuralRecursion : Bool
  ctors : List InductiveCtorSpec

/-- The minimal kernel-support contract we currently want. -/
structure MinimalInductiveKernelSpec where
  supportsStrictlyPositiveFamilies : Bool
  supportsParameters : Bool
  supportsIndices : Bool
  supportsGeneratedRecursors : Bool
  supportsRecordSugar : Bool
  supportsStructuralRecursion : Bool
  deferredFeatures : List String
  starterFamilies : List InductiveFamilySpec

/-- First intended starter family set, small enough to stabilize early. -/
def starterInductiveFamilies : List InductiveFamilySpec :=
  [ { name := "Empty"
      shape := .ordinary
      parameterCount := 0
      indexCount := 0
      strictlyPositive := true
      hasGeneratedRecursor := true
      allowsStructuralRecursion := true
      ctors := [] }
  , { name := "Unit"
      shape := .recordLike
      parameterCount := 0
      indexCount := 0
      strictlyPositive := true
      hasGeneratedRecursor := true
      allowsStructuralRecursion := true
      ctors := [{ name := "unit", argCount := 0 }] }
  , { name := "Bool"
      shape := .ordinary
      parameterCount := 0
      indexCount := 0
      strictlyPositive := true
      hasGeneratedRecursor := true
      allowsStructuralRecursion := true
      ctors := [{ name := "false", argCount := 0 }, { name := "true", argCount := 0 }] }
  , { name := "Nat"
      shape := .ordinary
      parameterCount := 0
      indexCount := 0
      strictlyPositive := true
      hasGeneratedRecursor := true
      allowsStructuralRecursion := true
      ctors := [{ name := "zero", argCount := 0 }, { name := "succ", argCount := 1 }] }
  , { name := "Prod"
      shape := .recordLike
      parameterCount := 2
      indexCount := 0
      strictlyPositive := true
      hasGeneratedRecursor := true
      allowsStructuralRecursion := true
      ctors := [{ name := "mk", argCount := 2 }] }
  , { name := "List"
      shape := .ordinary
      parameterCount := 1
      indexCount := 0
      strictlyPositive := true
      hasGeneratedRecursor := true
      allowsStructuralRecursion := true
      ctors := [{ name := "nil", argCount := 0 }, { name := "cons", argCount := 2 }] }
  , { name := "Fin"
      shape := .indexed
      parameterCount := 0
      indexCount := 1
      strictlyPositive := true
      hasGeneratedRecursor := true
      allowsStructuralRecursion := true
      ctors := [{ name := "fz", argCount := 0 }, { name := "fs", argCount := 1 }] }
  , { name := "Vec"
      shape := .indexed
      parameterCount := 1
      indexCount := 1
      strictlyPositive := true
      hasGeneratedRecursor := true
      allowsStructuralRecursion := true
      ctors := [{ name := "vnil", argCount := 0 }, { name := "vcons", argCount := 2 }] } ]

/-- The minimal early inductive-family contract we want to target next. -/
def minimalInductiveKernelSpec : MinimalInductiveKernelSpec :=
  { supportsStrictlyPositiveFamilies := true
    supportsParameters := true
    supportsIndices := true
    supportsGeneratedRecursors := true
    supportsRecordSugar := true
    supportsStructuralRecursion := true
    deferredFeatures :=
      [ "induction-recursion"
      , "coinductives"
      , "quotients"
      , "higher-inductive-types"
      , "general-fixpoints" ]
    starterFamilies := starterInductiveFamilies }

theorem minimalInductiveKernelSpec_strictlyPositive :
    minimalInductiveKernelSpec.supportsStrictlyPositiveFamilies = true := rfl

theorem minimalInductiveKernelSpec_indices :
    minimalInductiveKernelSpec.supportsIndices = true := rfl

theorem minimalInductiveKernelSpec_structuralRecursion :
    minimalInductiveKernelSpec.supportsStructuralRecursion = true := rfl

theorem minimalInductiveKernelSpec_defers_inductionRecursion :
    "induction-recursion" ∈ minimalInductiveKernelSpec.deferredFeatures := by
  simp [minimalInductiveKernelSpec]

theorem starterFamilies_include_nat :
    ∃ spec ∈ minimalInductiveKernelSpec.starterFamilies, spec.name = "Nat" := by
  simp [minimalInductiveKernelSpec, starterInductiveFamilies]

theorem starterFamilies_include_vec :
    ∃ spec ∈ minimalInductiveKernelSpec.starterFamilies, spec.name = "Vec" := by
  simp [minimalInductiveKernelSpec, starterInductiveFamilies]

end Mettapedia.Languages.MeTTa
