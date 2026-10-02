import Mettapedia.GSLT.LanguageDef.Cost.RegionOccurrenceRestoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryValueControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionEquationModel

/-!
# Positional restoration of the actual repeated-input region plan

The existing planner's two boundary positions generate the skeleton below.
Supported reflective substitution restores independent current values, including
an actual second-position `setTree` update. This is restoration of a retained
state; it does not assert that the child replacement is a process reduction or
that source canonicalization already transports the occurrence origins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryPositionalRestoration

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted LanguageDefContinuedInteraction
open RepeatedBoundaryValueControls RetainedBoundaryGraftControls
open CostRegionBoundaryEvidence.OccurrenceRestoration

/-- Run the common positional fold on the existing authored region plan. -/
def sourceSkeleton : Pattern :=
  CostRegionPlanAbstraction.pattern plan CostRegionBoundaryEvidence.OccurrenceTokens.token

def skeleton : Pattern := mapPattern (CostStaticColor.base.symbols rhoCIGSLT) sourceSkeleton

theorem skeleton_exact : skeleton = .collection .hashBag
    [.fvar (CostRegionBoundaryEvidence.OccurrenceTokens.token firstSlot),
     .fvar (CostRegionBoundaryEvidence.OccurrenceTokens.token secondSlot)] none := rfl

theorem skeleton_typed : HasType rhoCIGSLT.costWholeLanguage
    (freeContext frame.boundaryTable) [] skeleton (.base (costBaseSortName "Proc")) := by
  rw [skeleton_exact]
  exact .collectionConstructor (rule := GeneratedCollectionEquationModel.parallelRule .base)
    (GeneratedCollectionEquationModel.parallel_member .base) rfl
    (.cons (.fvar (freeContext_token frame.boundaryTable firstSlot))
      (.cons (.fvar (freeContext_token frame.boundaryTable secondSlot))
        (.nil [] (.base (costBaseSortName "Proc")))))

theorem skeleton_safe : skeleton_typed.ReflectiveSupportSafeAt
    rhoCIGSLT.costWholeReflectionProfile (support frame.boundaryTable) [] := by
  exact HasType.ReflectiveSupportSafeAt.collectionConstructor
    (profile := rhoCIGSLT.costWholeReflectionProfile)
    (support := support frame.boundaryTable)
    (membership := GeneratedCollectionEquationModel.parallel_member .base)
    (parameterShape := rfl)
    (.cons (.fvar (freeContext_token frame.boundaryTable firstSlot) [] ⟨[], rfl⟩)
      (.cons (.fvar (freeContext_token frame.boundaryTable secondSlot) [] ⟨[], rfl⟩)
        (.nil [] (.base (costBaseSortName "Proc")) [])))

def openSkeleton : ReflectiveWellSorted.OpenPattern rhoCIGSLT.costWholeReflectionProfile
    rhoCIGSLT.costWholeLanguage (freeContext frame.boundaryTable) []
    (.base (costBaseSortName "Proc")) :=
  ⟨skeleton, ⟨skeleton_typed, rfl, rfl, skeleton_typed.isWellScopedAt⟩,
    by intro declaration member; rfl⟩

/-- Reuse the established typed reflective substitution, with actual current
values from the planner's table. -/
def restored (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base
    FreeTypeContext.empty frame.boundaryTable) :=
  ReflectiveWellSorted.OpenPattern.substituteReflectiveSupported
    openSkeleton (supportedAssignment frame.boundaryTable values) skeleton_safe

theorem mixed_restored : (restored mixedValues).1 =
    .collection .hashBag [inputPattern, zeroPattern] none := by
  change ReflectiveContextSupport.substitute rhoCIGSLT.costWholeReflectionProfile
    (support frame.boundaryTable) (assignment frame.boundaryTable mixedValues) [] skeleton = _
  rw [skeleton_exact]
  simp only [ReflectiveContextSupport.substitute, ReflectiveContextSupport.substituteAt,
    List.map_cons, List.map_nil, assignment_token, support_token]
  rfl

theorem uniform_restored : (restored uniformValues).1 = originalPattern := by
  change ReflectiveContextSupport.substitute rhoCIGSLT.costWholeReflectionProfile
    (support frame.boundaryTable) (assignment frame.boundaryTable uniformValues) [] skeleton = _
  rw [skeleton_exact]
  simp only [ReflectiveContextSupport.substitute, ReflectiveContextSupport.substituteAt,
    List.map_cons, List.map_nil, assignment_token, support_token]
  rfl

/-- Unlike whole-key restoration, this actual planner restoration observes the
independently changed second retained value. -/
theorem restorations_different : (restored mixedValues).1 ≠ (restored uniformValues).1 := by
  rw [mixed_restored, uniform_restored]
  decide +kernel

/-- The distinguishing current vector is exactly the existing public update,
and its separately retained child forest is supplied by the same operation. -/
theorem public_update_restored :
    (restored (BoundaryOccurrenceValues.set frame.boundaryTable uniformValues
      secondSlot zeroValue)).1 = .collection .hashBag [inputPattern, zeroPattern] none ∧
    BoundaryOccurrenceValues.setTree frame.boundaryTable uniformValues uniformChildren
      secondSlot zeroValue zeroTree = mixedChildren :=
  ⟨mixed_restored, positional_second_tree_update⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RepeatedBoundaryPositionalRestoration
