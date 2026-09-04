import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace CostStaticAtomEnvironment

private theorem object_of_mem_objectList {patterns : List Pattern}
    {pattern : Pattern} (membership : pattern ∈ patterns)
    (objects : WellSorted.isObjectPatternList patterns = true) :
    WellSorted.isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      simp only [WellSorted.isObjectPatternList, Bool.and_eq_true] at objects
      simp only [List.mem_cons] at membership
      rcases membership with rfl | inTail
      · exact objects.1
      · exact inductionHypothesis inTail objects.2

theorem exists_originalName_of_mem_freeFvarNames_reify_of_object
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ∀ (pattern : Pattern), WellSorted.isObjectPattern pattern = true →
      ∀ {name}, name ∈ (environment.reify pattern).freeFvarNames →
        ∃ originalName, originalName ∈ pattern.freeFvarNames ∧
          environment.reifyName originalName = name := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro object name membership
      rw [environment.reify_eq_renameFVars] at membership
      simp [Pattern.renameFVars, Pattern.freeFvarNames] at membership
  | hfvar originalName =>
      intro object name membership
      rw [environment.reify_eq_renameFVars] at membership
      simp [Pattern.renameFVars, Pattern.freeFvarNames] at membership
      exact ⟨originalName, by simp [Pattern.freeFvarNames], membership.symm⟩
  | happly constructor arguments inductionHypothesis =>
      intro object name membership
      simp only [CostStaticAtomEnvironment.reify, Pattern.freeFvarNames,
        List.mem_flatMap] at membership ⊢
      obtain ⟨reifiedArgument, reifiedMembership, nameMembership⟩ := membership
      obtain ⟨argument, argumentMembership, argumentEq⟩ :=
        List.mem_map.mp reifiedMembership
      subst reifiedArgument
      have argumentsObject : WellSorted.isObjectPatternList arguments = true := by
        simpa [WellSorted.isObjectPattern] using object
      have argumentObject : WellSorted.isObjectPattern argument = true :=
        object_of_mem_objectList argumentMembership argumentsObject
      obtain ⟨originalName, originalMembership, reifiedName⟩ :=
        inductionHypothesis argument argumentMembership argumentObject
          nameMembership
      exact ⟨originalName, ⟨argument, argumentMembership, originalMembership⟩,
        reifiedName⟩
  | hlambda binder body inductionHypothesis =>
      intro object name membership
      rw [environment.reify_eq_renameFVars] at membership
      simp only [Pattern.renameFVars, Pattern.freeFvarNames] at membership
      rw [← environment.reify_eq_renameFVars] at membership
      obtain ⟨originalName, originalMembership, reifiedName⟩ :=
        inductionHypothesis (by
          simpa [WellSorted.isObjectPattern] using object) (by
          exact membership)
      exact ⟨originalName, by simpa [Pattern.freeFvarNames] using
        originalMembership, reifiedName⟩
  | hmultiLambda arity binders body inductionHypothesis =>
      intro object name membership
      rw [environment.reify_eq_renameFVars] at membership
      simp only [Pattern.renameFVars, Pattern.freeFvarNames] at membership
      rw [← environment.reify_eq_renameFVars] at membership
      obtain ⟨originalName, originalMembership, reifiedName⟩ :=
        inductionHypothesis (by
          simpa [WellSorted.isObjectPattern] using object) (by
          exact membership)
      exact ⟨originalName, by simpa [Pattern.freeFvarNames] using
        originalMembership, reifiedName⟩
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro object
      simp [WellSorted.isObjectPattern] at object
  | hcollection collectionType elements rest inductionHypothesis =>
      intro object name membership
      have objectParts : rest = none ∧
          WellSorted.isObjectPatternList elements = true := by
        simpa [WellSorted.isObjectPattern] using object
      cases objectParts.1
      simp only [CostStaticAtomEnvironment.reify, Pattern.freeFvarNames,
        Option.toList_none, List.append_nil, List.mem_flatMap] at membership ⊢
      obtain ⟨reifiedElement, reifiedMembership, nameMembership⟩ := membership
      obtain ⟨element, elementMembership, elementEq⟩ :=
        List.mem_map.mp reifiedMembership
      subst reifiedElement
      have elementObject : WellSorted.isObjectPattern element = true :=
        object_of_mem_objectList elementMembership objectParts.2
      obtain ⟨originalName, originalMembership, reifiedName⟩ :=
        inductionHypothesis element elementMembership elementObject nameMembership
      exact ⟨originalName, ⟨element, elementMembership, originalMembership⟩,
        reifiedName⟩

end CostStaticAtomEnvironment
end Mettapedia.GSLT.LanguageDef
