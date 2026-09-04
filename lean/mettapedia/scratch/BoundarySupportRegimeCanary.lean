import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryPlanOccurrenceAvailability
import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryView

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

mutual
  theorem CostStaticRegionPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil_canary
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
        plan.abstractPattern = true)
      (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
      (membership : boundary ∈ plan.boundaryTable.entries) :
      boundary.boundary.targetSupport = sourceAvailable ∨
        boundary.boundary.targetSupport = [] := by
    cases plan with
    | bvar sourceIndex lookup correspondence availableScope =>
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary rhoCIGSLT color targetFree)) at membership
        simp at membership
    | fvar lookup =>
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary rhoCIGSLT color targetFree)) at membership
        simp at membership
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        change boundary ∈ [certified.typed] at membership
        simp only [List.mem_singleton] at membership
        subst boundary
        exact Or.inl certified.targetSupport_eq
    | application constructor rendered current preimage notBare children =>
        have childrenFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList
              children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        have childResult :=
          CostStaticArgumentPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil_canary
            children childrenFree boundary membership
        by_cases quote : ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.reflection.1 preimage.sourceConstructor.1.label = true
        · right
          rcases childResult with exposed | sealed
          · simpa [quote] using exposed
          · exact sealed
        · simpa [quote] using childResult
    | lambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern] at frameFree
    | multiLambda bodyPlan =>
        simp [CostStaticRegionPlan.abstractPattern,
          WellSorted.ReflectiveSubstitutionBinderFree] at frameFree
    | collection choice selected children =>
        have childrenFree :
            WellSorted.ReflectiveSubstitutionBinderFreeList
              children.abstractPatterns = true := by
          simpa [CostStaticRegionPlan.abstractPattern,
            WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
        exact
          CostStaticElementPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil_canary
            children childrenFree boundary membership
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        change boundary ∈ [certified.typed] at membership
        simp only [List.mem_singleton] at membership
        subst boundary
        exact Or.inl certified.targetSupport_eq
  termination_by 3 * sizeOf pattern + 2

  theorem CostStaticArgumentPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil_canary
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true)
      (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
      (membership : boundary ∈ plan.boundaryTable.entries) :
      boundary.boundary.targetSupport = sourceAvailable ∨
        boundary.boundary.targetSupport = [] := by
    cases plan with
    | nil =>
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary rhoCIGSLT color targetFree)) at membership
        simp at membership
    | cons representation parameterType head tail =>
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree head.abstractPattern =
                true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                tail.abstractPatterns = true := by
          simpa [CostStaticArgumentPlan.abstractPatterns,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        change boundary ∈
          (TypedCostRegionBoundaryTable.append head.boundaryTable
            tail.boundaryTable).entries at membership
        rw [TypedCostRegionBoundaryTable.entries_append] at membership
        rcases List.mem_append.mp membership with headMembership | tailMembership
        · exact
            CostStaticRegionPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil_canary
              head freeParts.1 boundary headMembership
        · exact
            CostStaticArgumentPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil_canary
              tail freeParts.2 boundary tailMembership
  termination_by 3 * sizeOf arguments + 1

  theorem CostStaticElementPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil_canary
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
        targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      (frameFree : WellSorted.ReflectiveSubstitutionBinderFreeList
        plan.abstractPatterns = true)
      (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
      (membership : boundary ∈ plan.boundaryTable.entries) :
      boundary.boundary.targetSupport = sourceAvailable ∨
        boundary.boundary.targetSupport = [] := by
    cases plan with
    | nil =>
        change boundary ∈ ([] : List
          (TypedCostRegionBoundary rhoCIGSLT color targetFree)) at membership
        simp at membership
    | cons head tail =>
        have freeParts :
            WellSorted.ReflectiveSubstitutionBinderFree head.abstractPattern =
                true ∧
              WellSorted.ReflectiveSubstitutionBinderFreeList
                tail.abstractPatterns = true := by
          simpa [CostStaticElementPlan.abstractPatterns,
            WellSorted.ReflectiveSubstitutionBinderFreeList] using frameFree
        change boundary ∈
          (TypedCostRegionBoundaryTable.append head.boundaryTable
            tail.boundaryTable).entries at membership
        rw [TypedCostRegionBoundaryTable.entries_append] at membership
        rcases List.mem_append.mp membership with headMembership | tailMembership
        · exact
            CostStaticRegionPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil_canary
              head freeParts.1 boundary headMembership
        · exact
            CostStaticElementPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil_canary
              tail freeParts.2 boundary tailMembership
  termination_by 3 * sizeOf elements + 1
end

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
