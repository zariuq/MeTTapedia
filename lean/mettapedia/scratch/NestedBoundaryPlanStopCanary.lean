import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryQuoteBoundaryAlignment

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A certified-boundary stop reached inside an already reached pair retains
its parent-cospan apex after composing contexts, entry embeddings, and type
routes back to the static roots. -/
noncomputable def nestedBoundaryPlanStops_commonRestorationApex_of_closeSmaller
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
    (parentMeasure : Nat)
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
    {leftParentPayload rightParentPayload : Pattern}
    (leftParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftParentPayload leftView.node.plan.abstractPattern)
    (rightParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightParentPayload rightView.node.plan.abstractPattern)
    (leftParentEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftParentReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries)
    (rightParentEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightParentReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries)
    (leftParentRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        leftParentReached.sourceType))
    (rightParentRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightParentReached.sourceType))
    (leftParentSizeLe : sizeOf leftParentPayload ≤
      sizeOf leftView.node.term.1)
    (rightParentSizeLe : sizeOf rightParentPayload ≤
      sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftParentReached.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightParentReached.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
        leftParentReached.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
        rightParentReached.plan.boundaryTable.entries)
    (leftRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) leftParentReached.sourceType)
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType))
    (rightRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) rightParentReached.sourceType)
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    (stopReason : RhoCanonicalRawStop declarationColor parentMeasure
        leftPayload rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftParentPayload)
    (rightPayloadSizeLe : sizeOf rightPayload ≤ sizeOf rightParentPayload)
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure) leftPayload
        rightPayload)
    (notBothBoundary : ¬
      (leftReached.plan.rootClass.IsCertifiedBoundary ∧
        rightReached.plan.rootClass.IsCertifiedBoundary))
    (cell : RhoPlanStopBoundarySideCell leftReached.plan.rootClass
      rightReached.plan.rootClass) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let leftReached' := leftReached.rebaseAbstractRoot
    leftParentReached.skeletonContext leftParentReached.abstract_eq
  let rightReached' := rightReached.rebaseAbstractRoot
    rightParentReached.skeletonContext rightParentReached.abstract_eq
  have sourceAligned := rhoPlanStopBoundarySide_sourceAligned leftView
    rightView declarationColor parentMeasure rightRootAdmissible closeSmaller
  have aligned := sourceAligned callbackAvailable callbackScope leftReached'
    rightReached' leftAdmission rightAdmission leftAbstractEq rightAbstractEq
    sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
    ⟨leftEmbedding.comp leftParentEmbedding⟩
    ⟨rightEmbedding.comp rightParentEmbedding⟩
    ⟨leftParentRoute.prepend leftRoute⟩
    ⟨rightParentRoute.prepend rightRoute⟩ stopReason
    (leftPayloadSizeLe.trans leftParentSizeLe)
    (rightPayloadSizeLe.trans rightParentSizeLe) rawAligned notBothBoundary
    cell
  exact RhoStaticPlanStopCommonApex.ofSourcePatternLeafAligned leftView.node
    rightView.node (leftView.targetBound_eq_targetBound rightView) _ _ aligned
    callbackScope callbackRoot

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
