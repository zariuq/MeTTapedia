import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderLeftCollapsing

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- The depth-uniform source form of the plan-stop obligation. -/
def RhoStaticPlanStopSourceAligned
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rawStop : Pattern → Pattern → Prop) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  ∀ callbackAvailable callbackScope {leftAbstract rightAbstract},
    CostStaticPlanCanonicalStop leftView.node.plan rightView.node.plan
        rhoReflectivePresentation rawDeclaration rawStop leftAbstract
        rightAbstract →
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      PatternLeafAligned
        (fun leftLeaf rightLeaf => ∀ sourceDepth,
          ReflectiveContextSupport.RestoresTogether
            rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment
              (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
                (leftView.node.thinning.thickenAmbientBVars sourceDepth
                  (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
              (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
                (rightView.node.thinning.thickenAmbientBVars sourceDepth
                  (mapPattern (color.symbols rhoCIGSLT) rightLeaf))))
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (leftEnvironment.reify leftAbstract))
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (rightEnvironment.reify rightAbstract))

/-- Obligation A1 from the depth-uniform plan-stop obligation alone. -/
theorem rhoAlignedViewsRestorationAligned_of_planStopSourceAligned
    {declarationColor : CostStaticColor}
    (planStops : ∀ {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
        type}
      {color : CostStaticColor}
      (leftView : left.StaticRootView color)
      (rightView : right.StaticRootView color),
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type leftPattern →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type rightPattern →
      RhoPairCloseSmaller declarationColor targetFree
        (sizeOf leftPattern + sizeOf rightPattern) →
      RhoStaticPlanStopSourceAligned leftView rightView declarationColor
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern))) :
    RhoAlignedViewsRestorationAlignedInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWellSorted rightWellSorted
    closeSmaller roots
  apply RhoStaticFramesRestorationAligned.ofSourceCanonicalAlignment leftView
    rightView
  have rawAligned := canonicalStopAligned_of_root_aligned
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation) roots
  have stops := planStops leftView rightView admissible leftWellSorted
    rightWellSorted closeSmaller
  have result := reifiedSourceAlignment_of_rawAlignment leftView.node
    rightView.node leftView.children rightView.children
    (CostStaticAtomEnvironment.ofInventory
      (leftView.node.semanticAtomEnvironment
        (leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
    (CostStaticAtomEnvironment.ofInventory
      (rightView.node.semanticAtomEnvironment
        (rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
    (leftView.targetBound_eq_targetBound rightView)
    (leftView.sourceSort_eq_sourceSort rightView)
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation)
    (rawStop := RhoCanonicalRawStop declarationColor
      (sizeOf leftPattern + sizeOf rightPattern))
    (by
      rw [leftView.patternEq, rightView.patternEq]
      exact rawAligned)
    (sourceSemanticPatternKeyAt leftView.node
      (CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1))
    (sourceSemanticPatternKeyAt rightView.node
      (CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1))
    leftView.node.targetBound.length 0
    (fun callbackAvailable callbackScope {leftAbstract rightAbstract} stop =>
      stops callbackAvailable callbackScope stop)
  rw [leftView.targetBound_length_eq_targetBound_length rightView] at result ⊢
  exact result

section ApexForm

/-- The apex-form aligned obligation: exactly A1 with the depth-uniform
source relation replaced by the one-depth common restoration apex. -/
def RhoAlignedViewsPlanStopApexInDomain (declarationColor : CostStaticColor) :
    Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color),
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type rightPattern →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) →
    CanonicalRootAligned
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern rightPattern →
    RhoStaticPlanStopCommonApex leftView rightView declarationColor
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftPattern + sizeOf rightPattern))

/-- The provider from the apex-form aligned obligation.  A1 is not used. -/
theorem rhoCanonicalStaticPairSemanticCutProviderInDomain_of_apexObligations
    {declarationColor : CostStaticColor}
    (alignedApex : RhoAlignedViewsPlanStopApexInDomain declarationColor)
    (collapsingRestoration :
      RhoCollapsingViewsRestorationAlignedInDomain declarationColor)
    (exposure : RhoCollapsingLeafExposureInDomain declarationColor) :
    RhoCanonicalStaticPairSemanticCutProviderInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical _staticShape closeSmaller
    left right rootCase
  have close : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) := closeSmaller
  cases rootCase with
  | leftCollapsing leftColor leftView collapsing =>
      exact
        nonempty_rhoCanonicalStaticPairSemanticCut_leftCollapsing_of_restorationRoutes
          leftView collapsing
          (fun rightView =>
            collapsingRestoration leftView rightView admissible leftWellSorted
              rightWellSorted close (Or.inl collapsing) canonical)
          (fun rightStructural =>
            exposure leftView collapsing rightStructural canonical)
  | rightCollapsing rightColor rightView collapsing =>
      exact
        nonempty_rhoCanonicalStaticPairSemanticCut_rightCollapsing_of_restorationRoutes
          rightView collapsing
          (fun leftView =>
            collapsingRestoration leftView rightView admissible leftWellSorted
              rightWellSorted close (Or.inr collapsing) canonical)
          (fun leftStructural =>
            exposure rightView collapsing leftStructural canonical.symm)
  | aligned color leftView rightView roots =>
      exact ⟨RhoCanonicalStaticPairSemanticCut.matchedOfProvenancedPlanStops
        leftView rightView roots canonical
        (alignedApex leftView rightView admissible leftWellSorted
          rightWellSorted close roots)⟩

/-- The depth-uniform source obligation dominates the apex obligation. -/
theorem rhoAlignedViewsPlanStopApex_of_sourceAligned
    {declarationColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    {rawStop : Pattern → Pattern → Prop}
    (source : RhoStaticPlanStopSourceAligned leftView rightView
      declarationColor rawStop) :
    RhoStaticPlanStopCommonApex leftView rightView declarationColor rawStop :=
  fun callbackAvailable callbackScope callbackRoot {_leftAbstract _rightAbstract}
      stop =>
    RhoStaticPlanStopCommonApex.ofSourcePatternLeafAligned leftView.node
      rightView.node (leftView.targetBound_eq_targetBound rightView) _ _
      (source callbackAvailable callbackScope stop) callbackScope callbackRoot

end ApexForm




end Mettapedia.Languages.ProcessCalculi.RhoCalculus
