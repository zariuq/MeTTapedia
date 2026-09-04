import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelFrontier

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoCommonRestorationApex
open Mettapedia.GSLT.LanguageDef.ReflectionExtension

mutual
  theorem parallelLeaves_renameFVars_canary
      (declaration : ReflectivePresentationDecl) (rename : String → String) :
      ∀ pattern,
      parallelLeaves declaration (Pattern.renameFVars rename pattern) =
        (parallelLeaves declaration pattern).map
          (Pattern.renameFVars rename)
    | .bvar index => by simp [parallelLeaves, Pattern.renameFVars]
    | .fvar name => by simp [parallelLeaves, Pattern.renameFVars]
    | .apply constructor arguments => by
        by_cases unit : constructor = declaration.parallelUnitConstructor ∧
          arguments = []
        · rcases unit with ⟨rfl, rfl⟩
          simp [parallelLeaves, Pattern.renameFVars]
        · simp [parallelLeaves, Pattern.renameFVars, unit]
    | .lambda binder body => by
        simp [parallelLeaves, Pattern.renameFVars]
    | .multiLambda arity binders body => by
        simp [parallelLeaves, Pattern.renameFVars]
    | .subst body replacement => by
        simp [parallelLeaves, Pattern.renameFVars]
    | .collection collectionType elements rest => by
        by_cases parallel : collectionType = declaration.parallelCollection ∧
          rest = none
        · rcases parallel with ⟨rfl, rfl⟩
          simp only [Pattern.renameFVars, parallelLeaves, and_self, if_true]
          exact parallelLeavesList_renameFVars_canary declaration rename elements
        · simp only [Pattern.renameFVars, parallelLeaves,
            if_neg parallel, List.map_singleton]

  theorem parallelLeavesList_renameFVars_canary
      (declaration : ReflectivePresentationDecl) (rename : String → String) :
      ∀ patterns,
      parallelLeavesList declaration
          (patterns.map (Pattern.renameFVars rename)) =
        (parallelLeavesList declaration patterns).map
          (Pattern.renameFVars rename)
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map_cons, parallelLeavesList, List.map_append]
        rw [parallelLeaves_renameFVars_canary,
          parallelLeavesList_renameFVars_canary]
end

mutual
  theorem parallelLeaves_mapCostStatic_canary
      (color : CostStaticColor) (declaration : ReflectivePresentationDecl) :
      ∀ pattern,
      parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color declaration)
          (mapPattern (color.symbols rhoCIGSLT) pattern) =
        (parallelLeaves declaration pattern).map
          (mapPattern (color.symbols rhoCIGSLT))
    | .bvar index => rfl
    | .fvar name => rfl
    | .apply constructor arguments => by
        let targetDeclaration := costStaticReflectivePresentationDecl
          rhoCIGSLT color declaration
        have unitMap : targetDeclaration.parallelUnitConstructor =
            (color.symbols rhoCIGSLT).constructor
              declaration.parallelUnitConstructor := by
          cases color <;> rfl
        by_cases unit : constructor = declaration.parallelUnitConstructor ∧
          arguments = []
        · rcases unit with ⟨rfl, rfl⟩
          have mappedUnit :
              (color.symbols rhoCIGSLT).constructor
                    declaration.parallelUnitConstructor =
                  targetDeclaration.parallelUnitConstructor ∧
                mapPatternList (color.symbols rhoCIGSLT) [] = [] :=
            ⟨unitMap.symm, rfl⟩
          simp only [mapPattern, parallelLeaves]
          rw [if_pos mappedUnit]
          simp
        · have mappedNotUnit : ¬
            ((color.symbols rhoCIGSLT).constructor constructor =
                targetDeclaration.parallelUnitConstructor ∧
              mapPatternList (color.symbols rhoCIGSLT) arguments = []) := by
            rintro ⟨constructorEq, argumentsEq⟩
            apply unit
            constructor
            · apply CostStaticColor.symbols_constructor_injective
                rhoCIGSLT color
              simpa [unitMap] using constructorEq
            · simpa [mapPatternList_eq_map] using argumentsEq
          simp only [mapPattern, parallelLeaves]
          rw [if_neg mappedNotUnit, if_neg unit]
          rfl
    | .lambda binder body => by simp [parallelLeaves, mapPattern]
    | .multiLambda arity binders body => by simp [parallelLeaves, mapPattern]
    | .subst body replacement => by
        simp [parallelLeaves, mapPattern]
    | .collection collectionType elements rest => by
        let targetDeclaration := costStaticReflectivePresentationDecl
          rhoCIGSLT color declaration
        have parallelMap : targetDeclaration.parallelCollection =
            declaration.parallelCollection := by
          cases color <;> rfl
        by_cases parallel : collectionType = declaration.parallelCollection ∧
          rest = none
        · rcases parallel with ⟨rfl, rfl⟩
          simp only [mapPattern, parallelLeaves, mapPatternList_eq_map]
          rw [parallelMap]
          simp only [and_self, if_true]
          exact parallelLeavesList_mapCostStatic_canary color declaration
            elements
        · have mappedNotParallel : ¬
            (collectionType = targetDeclaration.parallelCollection ∧
              rest = none) := by
            simpa [parallelMap] using parallel
          simp only [mapPattern, parallelLeaves, mapPatternList_eq_map]
          rw [if_neg parallel, if_neg mappedNotParallel]
          simp [mapPattern, mapPatternList_eq_map]

  theorem parallelLeavesList_mapCostStatic_canary
      (color : CostStaticColor) (declaration : ReflectivePresentationDecl) :
      ∀ patterns,
      parallelLeavesList
          (costStaticReflectivePresentationDecl rhoCIGSLT color declaration)
          (patterns.map (mapPattern (color.symbols rhoCIGSLT))) =
        (parallelLeavesList declaration patterns).map
          (mapPattern (color.symbols rhoCIGSLT))
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map_cons, parallelLeavesList, List.map_append]
        rw [parallelLeaves_mapCostStatic_canary,
          parallelLeavesList_mapCostStatic_canary]
end

theorem reached_parentFrame_commonReify_canary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      parentNode.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      parentNode.boundaryTable values parentNode.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {payload : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      parentNode.plan.abstractPattern)
    (availableDepth scopeDepth : Nat) :
    cospan.reifyWith environment.lookupAtom? leg
        (parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                environment)
              rhoReflectivePresentation availableDepth scopeDepth
              (environment.reify reached.plan.abstractPattern)))) =
      canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        availableDepth
        (cospan.reifyWith environment.lookupAtom? leg
          (parentNode.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (environment.reify reached.plan.abstractPattern)))) := by
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  let targetKey : Nat → Nat → Pattern → Nat :=
    fun current _ candidate =>
      CostStaticRegionNode.semanticPatternKeyAt environment current candidate
  let targetFrame := parentNode.thinning.thickenAmbientBVars scopeDepth
    (mapPattern (color.symbols rhoCIGSLT)
      (environment.reify reached.plan.abstractPattern))
  have sourceKeyEq :
      CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode environment =
        fun availableDepth scopeDepth pattern =>
          CostStaticRegionNode.semanticPatternKeyAt environment availableDepth
            (parentNode.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT) pattern)) := rfl
  have targetFrameCovered : environment.Covers targetFrame := by
    intro name membership
    have canonicalMembership : name ∈
        (canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth targetFrame).freeFvarNames :=
      (CostStaticAtomKeyCospan.mem_freeFvarNames_canonicalizeByDepths_iff
        targetKey targetDeclaration name availableDepth scopeDepth
        targetFrame).mpr membership
    have canonicalFrameEq :
        canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth targetFrame =
          parentNode.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                  environment)
                rhoReflectivePresentation availableDepth scopeDepth
                (environment.reify reached.plan.abstractPattern))) := by
      rw [sourceKeyEq]
      simpa [targetKey, targetDeclaration, targetFrame] using
        (Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.mapThicken_canonicalizeByDepths
          parentNode.thinning targetKey rhoReflectivePresentation
          availableDepth scopeDepth
          (environment.reify reached.plan.abstractPattern)).symm
    rw [canonicalFrameEq] at canonicalMembership
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_atomCovered
        parentNode environment reached availableDepth scopeDepth name
          canonicalMembership
  have targetNaturality :
      parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                environment)
              rhoReflectivePresentation availableDepth scopeDepth
              (environment.reify reached.plan.abstractPattern))) =
        canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth targetFrame := by
    rw [sourceKeyEq]
    simpa [targetKey, targetDeclaration, targetFrame] using
      Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.mapThicken_canonicalizeByDepths
        parentNode.thinning targetKey rhoReflectivePresentation
        availableDepth scopeDepth
        (environment.reify reached.plan.abstractPattern)
  rw [targetNaturality]
  rw [environment.reifyWith_canonicalizeByDepths_semanticPatternKeyAt
    cospan leg commutes targetDeclaration availableDepth scopeDepth targetFrame
    targetFrameCovered]
  simpa [targetKey, targetDeclaration, targetFrame] using
    canonicalizeByDepths_ignoreScope
      (cospan.commonSemanticPatternKeyAt rhoCIGSLT) targetDeclaration
      availableDepth scopeDepth
      (cospan.reifyWith environment.lookupAtom? leg targetFrame)

end ParallelFrontier
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
