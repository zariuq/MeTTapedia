import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignPlanStopRestoration

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- At a declaration colour foreign to both static views, the exact root-plan
stop apex follows by specializing the provenance-carrying stop theorem to the
two root plans. -/
noncomputable def rho_staticPlanStopCommonApex_of_foreign
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)) :
    @RhoStaticPlanStopCommonApex targetFree available outer leftPattern
      rightPattern type left right color leftView rightView declarationColor
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)) := by
  let leftRootReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftView.node.term.1 leftView.node.plan.abstractPattern :=
    { sourceBound := leftView.node.sourceBound
      targetBound := leftView.node.targetBound
      thinning := leftView.node.thinning
      sourceAvailable := leftView.node.targetBound
      outer := .hole
      sourceType := .base leftView.node.sourceSort.1
      plan := leftView.node.plan
      skeletonContext := .hole
      abstract_eq := rfl }
  let rightRootReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightView.node.term.1 rightView.node.plan.abstractPattern :=
    { sourceBound := rightView.node.sourceBound
      targetBound := rightView.node.targetBound
      thinning := rightView.node.thinning
      sourceAvailable := rightView.node.targetBound
      outer := .hole
      sourceType := .base rightView.node.sourceSort.1
      plan := rightView.node.plan
      skeletonContext := .hole
      abstract_eq := rfl }
  intro availableDepth scopeDepth rootDepth leftAbstract rightAbstract stopped
  exact rho_foreignPlanStop_commonRestorationApex leftView rightView foreign
    rightRootAdmissible closeSmaller leftRootReached rightRootReached
    ⟨CostStaticPlanEntryEmbedding.refl _⟩
    ⟨CostStaticPlanEntryEmbedding.refl _⟩
    ⟨CostCanonicalTypeRoute.refl⟩ ⟨CostCanonicalTypeRoute.refl⟩
    (Nat.le_refl _) (Nat.le_refl _) availableDepth scopeDepth rootDepth stopped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
