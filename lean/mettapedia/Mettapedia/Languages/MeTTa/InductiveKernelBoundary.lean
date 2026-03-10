import Mettapedia.Languages.MeTTa.InductiveKernelHook
import Mettapedia.Languages.MeTTa.ElaboratedCoreBase

/-!
# Ordinary-Family Kernel Boundary

This file packages the first explicit kernel-facing boundary object for ordinary
strictly-positive inductive families.

It sits above `InductiveKernelHook` and below the current proof/runtime
certificate interfaces. The purpose is to make the current kernel-side
commitments exact without pretending that inductives are already implemented in
`MeTTa-Pure`.
-/

namespace Mettapedia.Languages.MeTTa

open Mettapedia.Languages.MeTTa.ElaboratedCore

/-- Kernel-side judgment classes currently promised for ordinary families. -/
inductive InductiveKernelJudgmentKind where
  | familyDeclaration
  | positivityChecked
  | generatedRecursor
  | structuralRecursion
deriving DecidableEq, Repr

/-- First explicit future-facing kernel boundary for ordinary families. -/
structure InductiveKernelBoundary where
  kernelInterface : PureInductiveKernelInterface
  supportedJudgments : List InductiveKernelJudgmentKind
  region : ElaboratedRegion
  overlapClass : OverlapClass

/-- Build the current boundary object from a future-facing kernel interface. -/
def PureInductiveKernelInterface.toKernelBoundary
    (iface : PureInductiveKernelInterface) : InductiveKernelBoundary :=
  { kernelInterface := iface
    supportedJudgments :=
      [ .familyDeclaration
      , .positivityChecked
      , .generatedRecursor
      , .structuralRecursion ]
    region := .pureKernelRegion
    overlapClass := .artifactOnly }

theorem PureInductiveKernelInterface.toKernelBoundary_region
    (iface : PureInductiveKernelInterface) :
    iface.toKernelBoundary.region = .pureKernelRegion := rfl

theorem PureInductiveKernelInterface.toKernelBoundary_overlap
    (iface : PureInductiveKernelInterface) :
    iface.toKernelBoundary.overlapClass = .artifactOnly := rfl

theorem PureInductiveKernelInterface.toKernelBoundary_supports_familyDeclaration
    (iface : PureInductiveKernelInterface) :
    InductiveKernelJudgmentKind.familyDeclaration ∈
      iface.toKernelBoundary.supportedJudgments := by
  simp [PureInductiveKernelInterface.toKernelBoundary]

theorem PureInductiveKernelInterface.toKernelBoundary_supports_positivity
    (iface : PureInductiveKernelInterface) :
    InductiveKernelJudgmentKind.positivityChecked ∈
      iface.toKernelBoundary.supportedJudgments := by
  simp [PureInductiveKernelInterface.toKernelBoundary]

theorem PureInductiveKernelInterface.toKernelBoundary_supports_generatedRecursor
    (iface : PureInductiveKernelInterface) :
    InductiveKernelJudgmentKind.generatedRecursor ∈
      iface.toKernelBoundary.supportedJudgments := by
  simp [PureInductiveKernelInterface.toKernelBoundary]

theorem PureInductiveKernelInterface.toKernelBoundary_supports_structuralRecursion
    (iface : PureInductiveKernelInterface) :
    InductiveKernelJudgmentKind.structuralRecursion ∈
      iface.toKernelBoundary.supportedJudgments := by
  simp [PureInductiveKernelInterface.toKernelBoundary]

theorem PureInductiveKernelInterface.toKernelBoundary_positivity_holds
    (iface : PureInductiveKernelInterface) :
    iface.hookInterface.family.strictlyPositive = true :=
  iface.positivity_checked

theorem PureInductiveKernelInterface.toKernelBoundary_recursor_holds
    (iface : PureInductiveKernelInterface) :
    iface.hook.generatesRecursor = true :=
  iface.recursor_generated

theorem PureInductiveKernelInterface.toKernelBoundary_structuralRecursion_holds
    (iface : PureInductiveKernelInterface) :
    iface.hook.allowsStructuralRecursion = true :=
  iface.structuralRecursion_enabled

def unitKernelBoundary : InductiveKernelBoundary :=
  unitPureKernelInterface.toKernelBoundary

def boolKernelBoundary : InductiveKernelBoundary :=
  boolPureKernelInterface.toKernelBoundary

def natKernelBoundary : InductiveKernelBoundary :=
  natPureKernelInterface.toKernelBoundary

theorem unitKernelBoundary_familyName :
    unitKernelBoundary.kernelInterface.hook.familyName = "Unit" := by
  exact unitPureKernelInterface_familyName

theorem boolKernelBoundary_familyName :
    boolKernelBoundary.kernelInterface.hook.familyName = "Bool" := by
  exact boolPureKernelInterface_familyName

theorem natKernelBoundary_familyName :
    natKernelBoundary.kernelInterface.hook.familyName = "Nat" := by
  exact natPureKernelInterface_familyName

theorem unitKernelBoundary_supports_recursor :
    InductiveKernelJudgmentKind.generatedRecursor ∈
      unitKernelBoundary.supportedJudgments := by
  exact unitPureKernelInterface.toKernelBoundary_supports_generatedRecursor

theorem boolKernelBoundary_supports_recursor :
    InductiveKernelJudgmentKind.generatedRecursor ∈
      boolKernelBoundary.supportedJudgments := by
  exact boolPureKernelInterface.toKernelBoundary_supports_generatedRecursor

theorem natKernelBoundary_supports_recursor :
    InductiveKernelJudgmentKind.generatedRecursor ∈
      natKernelBoundary.supportedJudgments := by
  exact natPureKernelInterface.toKernelBoundary_supports_generatedRecursor

theorem unitKernelBoundary_supports_structuralRecursion :
    InductiveKernelJudgmentKind.structuralRecursion ∈
      unitKernelBoundary.supportedJudgments := by
  exact unitPureKernelInterface.toKernelBoundary_supports_structuralRecursion

theorem boolKernelBoundary_supports_structuralRecursion :
    InductiveKernelJudgmentKind.structuralRecursion ∈
      boolKernelBoundary.supportedJudgments := by
  exact boolPureKernelInterface.toKernelBoundary_supports_structuralRecursion

theorem natKernelBoundary_supports_structuralRecursion :
    InductiveKernelJudgmentKind.structuralRecursion ∈
      natKernelBoundary.supportedJudgments := by
  exact natPureKernelInterface.toKernelBoundary_supports_structuralRecursion

theorem unitKernelBoundary_overlap :
    unitKernelBoundary.overlapClass = .artifactOnly := rfl

theorem boolKernelBoundary_overlap :
    boolKernelBoundary.overlapClass = .artifactOnly := rfl

theorem natKernelBoundary_overlap :
    natKernelBoundary.overlapClass = .artifactOnly := rfl

end Mettapedia.Languages.MeTTa
