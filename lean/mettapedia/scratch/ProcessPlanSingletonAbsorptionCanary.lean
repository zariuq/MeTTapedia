import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelFrontier

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

theorem processPlan_abstractPattern_ne_quote_of_processType
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (processType : sourceType = .base "Proc") :
    ∀ arguments, plan.abstractPattern ≠ .apply
      rhoReflectivePresentation.toReflectivePresentationDecl.quoteConstructor
      arguments := by
  cases plan with
  | bvar | fvar | boundaryApplication | boundaryCollection | collection =>
      simp [CostStaticRegionPlan.abstractPattern]
  | @application _ _ _ _ _ wireName arguments declared rendered current
      preimage notBare children =>
      intro quoteArguments abstractQuote
      have labelQuote : preimage.sourceConstructor.1.label = "NQuote" :=
        (Pattern.apply.inj abstractQuote).1
      have categoryName := rhoCalc_category_eq_name_of_label_eq_quote
        preimage.sourceConstructor.2 labelQuote
      have categoryProc : preimage.sourceConstructor.1.category = "Proc" :=
        TypeExpr.base.inj processType
      rw [categoryProc] at categoryName
      exact (by decide : "Proc" ≠ "Name") categoryName
  | lambda | multiLambda => cases processType

theorem processPlan_commonFrame_parallelSingleton_absorbed
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      table values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {frameSourceBound frameTargetBound : List TypeExpr}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color
      frameSourceBound frameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {payload : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload (.base "Proc"))
    (scopeDepth depth : Nat) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let frame := fun pattern =>
      cospan.reifyWith environment.lookupAtom? leg
        (frameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (environment.reify pattern)))
    canonicalizeByAt key declaration depth
        (.collection declaration.parallelCollection
          [frame plan.abstractPattern] none) =
      canonicalizeByAt key declaration depth
        (frame plan.abstractPattern) := by
  dsimp only
  let sourceDeclaration :=
    rhoReflectivePresentation.toReflectivePresentationDecl
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let frame := fun pattern =>
    cospan.reifyWith environment.lookupAtom? leg
      (frameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (environment.reify pattern)))
  change canonicalizeByAt key declaration depth
      (.collection declaration.parallelCollection
        [frame plan.abstractPattern] none) =
    canonicalizeByAt key declaration depth (frame plan.abstractPattern)
  have notQuote := processPlan_abstractPattern_ne_quote_of_processType plan rfl
  by_cases unit : plan.abstractPattern =
      .apply sourceDeclaration.parallelUnitConstructor []
  · have frameEq : frame plan.abstractPattern =
        .apply declaration.parallelUnitConstructor [] := by
      rw [unit]
      simp only [frame]
      rw [cospan.reifyWith_eq_renameFVars,
        environment.reify_eq_renameFVars]
      simp [sourceDeclaration, declaration, Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars]
      cases color <;> rfl
    rw [frameEq]
    apply canonicalizeByAt_parallel_singleton_of_not_parallel
    intro elements equality
    have unitCanonical : canonicalizeByAt key declaration depth
        (.apply declaration.parallelUnitConstructor []) =
          .apply declaration.parallelUnitConstructor [] := by
      simp [canonicalizeByAt, canonicalizeListByAt,
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]
    rw [unitCanonical] at equality
    cases equality
  · by_cases parallel : ∃ elements, plan.abstractPattern =
        .collection sourceDeclaration.parallelCollection elements none
    · obtain ⟨elements, abstractEq⟩ := parallel
      have frameEq : ∃ framedElements, frame plan.abstractPattern =
          .collection declaration.parallelCollection framedElements none := by
        rw [abstractEq]
        simp only [frame]
        rw [cospan.reifyWith_eq_renameFVars,
          environment.reify_eq_renameFVars]
        simp only [Pattern.renameFVars, mapPattern,
          mapPatternList_eq_map,
          CostStaticBinderThinning.thickenAmbientBVars]
        cases color <;> refine ⟨_, rfl⟩
      obtain ⟨framedElements, frameEq⟩ := frameEq
      rw [frameEq]
      exact canonicalizeByAt_parallel_singleton_parallel key declaration depth
        framedElements
    · have stable : plan.abstractPattern ≠
            .apply sourceDeclaration.parallelUnitConstructor [] ∧
          (∀ elements, plan.abstractPattern ≠
            .collection sourceDeclaration.parallelCollection elements none) ∧
          ∀ arguments, plan.abstractPattern ≠
            .apply sourceDeclaration.quoteConstructor arguments :=
        ⟨unit, fun elements equality => parallel ⟨elements, equality⟩,
          notQuote⟩
      have framedStable := commonReifiedMappedThickened_root_stable
        environment frameThinning cospan leg scopeDepth plan.abstractPattern
          stable
      apply canonicalizeByAt_parallel_singleton_of_not_parallel
      exact (canonicalizeByAt_leaf_stable_of_root_stable key declaration depth
        (frame plan.abstractPattern) framedStable.1 framedStable.2.1
          framedStable.2.2).2

end ParallelFrontier
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
