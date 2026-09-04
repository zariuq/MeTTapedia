import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryQuoteBoundaryAlignment

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A strictly smaller pair of reached authored Quotes has an exact apex in
the enclosing semantic-atom cospan. -/
noncomputable def quotePlanStops_commonRestorationApex_of_closeSmaller
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries)
    (rightRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    {parentMeasure : Nat}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure) leftPayload
        rightPayload)
    (leftQuote : leftReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (smaller : sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  have leftAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
    rw [sourceTypeEq]
    exact CostCanonicalTypeRoute.rho_admissible rightRoute
      rightRootAdmissible
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftReached.sourceAvailable
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)
      rightPayload := by
    rw [sourceAvailableEq, sourceTypeEq]
    exact rightAdmission.wellSorted
  have canonical := rawAligned.canonicalize_eq
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation)
    (fun stopped => stopped.1.2)
  let pair := Classical.choice
    (closeSmaller (childOuter := []) leftAdmission.wellSorted rightWellSorted
      canonical smaller leftAdmissible)
  let rightTree : CostRegionTree rhoCIGSLT targetFree
      rightReached.sourceAvailable [] rightPayload
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
    CostRegionTree.reindexFiber sourceAvailableEq rfl
      (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq)
        pair.rightTree
  have pairNormal :
      (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    have alignmentNormal :
        (pair.leftTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          (pair.rightTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      simpa only [rhoHereditaryNormalizationKernel] using
        pair.alignment.normalize_pattern_eq
    exact alignmentNormal.trans (by simp [rightTree])
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let leftFrame := leftView.node.thinning.thickenAmbientBVars callbackScope
    (mapPattern (color.symbols rhoCIGSLT)
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
          leftEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (leftEnvironment.reify leftReached.plan.abstractPattern)))
  let rightFrame := rightView.node.thinning.thickenAmbientBVars callbackScope
    (mapPattern (color.symbols rhoCIGSLT)
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
          rightEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (rightEnvironment.reify rightReached.plan.abstractPattern)))
  have leftCovered : leftEnvironment.Covers leftFrame := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_atomCovered
        leftView.node leftEnvironment leftReached callbackAvailable
          callbackScope
  have rightCovered : rightEnvironment.Covers rightFrame := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_atomCovered
        rightView.node rightEnvironment rightReached callbackAvailable
          callbackScope
  have leftRestore : ∀ restorationDepth,
      leftEnvironment.restoreAt restorationDepth leftFrame =
        (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    intro restorationDepth
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentQuoteFrame_restoresToPayloadNormal
        leftView.node leftView.children leftEnvironment leftReached
          leftAdmission leftQuote leftEmbedding pair.leftTree callbackAvailable
            callbackScope restorationDepth
  have rightRestore : ∀ restorationDepth,
      rightEnvironment.restoreAt restorationDepth rightFrame =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    intro restorationDepth
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentQuoteFrame_restoresToPayloadNormal
        rightView.node rightView.children rightEnvironment rightReached
          rightAdmission rightQuote rightEmbedding rightTree callbackAvailable
            callbackScope restorationDepth
  subst leftAbstractEq
  subst rightAbstractEq
  apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
  apply PatternLeafAligned.leaf
  intro restorationDepth
  have leftFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt
      leftEnvironment cospan cospan.leftSlot cospan.leftCommutes
      restorationDepth leftFrame leftCovered
  have rightFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt
      rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
      restorationDepth rightFrame rightCovered
  have endpointEq : leftEnvironment.restoreAt restorationDepth leftFrame =
      rightEnvironment.restoreAt restorationDepth rightFrame :=
    (leftRestore restorationDepth).trans
      (pairNormal.trans (rightRestore restorationDepth).symm)
  exact leftFactor.trans (endpointEq.trans rightFactor.symm)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
