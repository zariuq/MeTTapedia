import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell
import Mettapedia.GSLT.LanguageDef.CostHereditaryTransportAtoms
import Mettapedia.GSLT.LanguageDef.CostStaticPlanStopCarriers

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

#check CostHereditaryCrossColorLeafHinge.rhoCrossColor_staticRoot_singleton_plan
#check rhoNameFibre_staticRoot_shape
#check CostStaticPlanReached.exists_rootPlanSealedAlignment
#check CostStaticRegionPlan.normalizeValues_restoreMappedAbstract_restrict_eq
#check CostStaticRegionPlan.normalizeValues_restoreMappedAbstract_equationEquiv
#check CostStaticRegionPlan.restoreMappedAbstractPattern
#check CostStaticRegionNode.normalizeHereditaryRawWithInventory_eq_sourceAction
#check CostStaticRegionNode.normalizeHereditaryRawWithInventory
#check CostStaticRegionNode.sourceAction_eq_restoreSupportedSkeleton
#check CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
#check ReflectiveContextSupport.RestoresTogether
#check CostStaticAtomEnvironment.substituteAt_commonReifiedAtom_eq_of_scoped_normal

theorem rootClass_cases_canary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    plan.rootClass = .rigid ∨
      (∃ constructor, plan.rootClass = .application constructor) ∨
      (∃ collectionType, plan.rootClass = .collection collectionType) ∨
      plan.rootClass.IsCertifiedBoundary := by
  cases plan <;>
    simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary]

theorem application_sourceType_proc_of_not_quote_canary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    {constructor : String}
    (applicationClass : plan.rootClass = .application constructor)
    (notQuote : constructor ≠ rhoReflectivePresentation.quoteConstructor) :
    sourceType = .base "Proc" := by
  rcases rho_applicationPlan_sourceType_name_or_proc plan
      ⟨constructor, applicationClass⟩ with name | process
  · cases plan with
    | application declared rendered current preimage notBare children =>
        have categoryEq : preimage.sourceConstructor.1.category = "Name" :=
          TypeExpr.base.inj name
        have labelEq : preimage.sourceConstructor.1.label = "NQuote" :=
          rhoCalc_label_eq_quote_of_category_name
            preimage.sourceConstructor.2 categoryEq
        have classEq : constructor = preimage.sourceConstructor.1.label := by
          simpa [CostStaticRegionPlan.rootClass] using
            (CostStaticPlanRootClass.application.inj applicationClass).symm
        exact (notQuote (classEq.trans labelEq)).elim
    | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
        boundaryCollection =>
        simp [CostStaticRegionPlan.rootClass] at applicationClass
  · exact process

def BoundaryNonQuoteCell_canary (leftClass rightClass :
    CostStaticPlanRootClass) : Prop :=
  (leftClass.IsCertifiedBoundary ∧
      rightClass ≠ .application rhoReflectivePresentation.quoteConstructor) ∨
    (leftClass ≠ .application rhoReflectivePresentation.quoteConstructor ∧
      rightClass.IsCertifiedBoundary)

noncomputable def boundaryNonQuote_sourceAligned_canary
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
          childOuter leftChild rightChild childType)) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor (RhoCanonicalRawStop declarationColor parentMeasure)
      BoundaryNonQuoteCell_canary := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
    cell
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightEndpointAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
    CostCanonicalTypeRoute.rho_admissible rightRoute' rightRootAdmissible
  rcases cell with ⟨leftBoundary, rightNotQuote⟩ |
      ⟨leftNotQuote, rightBoundary⟩
  · rcases
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.rootClass_cases
        rightReached.plan with rightRigid |
        ⟨constructor, rightApplication⟩ |
        ⟨collectionType, rightCollection⟩ | rightBoundary'
    · obtain ⟨name, payloadEq, abstractEq, lookup⟩ :=
        boundarySide_rigidPartner_is_sourceVariable leftReached rightReached
          sourceTypeEq leftBoundary rightRigid stopReason
      have aligned :=
        rhoPlanStopBoundarySide_sourceVariablePartner_sourceAligned
          leftView rightView declarationColor rightRootAdmissible
          (fun stopped => stopped.1.2) closeSmaller callbackAvailable
          callbackScope leftReached rightReached sourceTypeEq leftEmbedding
          ⟨rightRoute'⟩ rightPayloadSizeLe rawAligned leftBoundary rightRigid
          ⟨costRegionSourceVariableName name, abstractEq⟩
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · have rightProcess :=
        rho_applicationPlan_sourceType_eq_proc_of_not_quote rightReached.plan
          rightApplication (fun equality => rightNotQuote
            (rightApplication.trans (congrArg _ equality)))
      have aligned := rhoPlanStopBoundarySide_processPartner_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq sourceAvailableEq
        leftEmbedding rightEmbedding ⟨rightRoute'⟩ rawAligned leftBoundary
        rightProcess
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · have rightProcess := rho_collectionPlan_sourceType_eq_proc
        rightReached.plan ⟨collectionType, rightCollection⟩
          rightEndpointAdmissible
      have aligned := rhoPlanStopBoundarySide_processPartner_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq sourceAvailableEq
        leftEmbedding rightEmbedding ⟨rightRoute'⟩ rawAligned leftBoundary
        rightProcess
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · exact (notBothBoundary ⟨leftBoundary, rightBoundary'⟩).elim
  · rcases
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.rootClass_cases
        leftReached.plan with leftRigid |
        ⟨constructor, leftApplication⟩ |
        ⟨collectionType, leftCollection⟩ | leftBoundary'
    · obtain ⟨name, payloadEq, abstractEq, lookup⟩ :=
        rigidPartner_boundarySide_is_sourceVariable leftReached rightReached
          sourceTypeEq leftRigid rightBoundary stopReason
      have aligned :=
        rhoPlanStopSourceVariablePartner_boundarySide_sourceAligned
          leftView rightView declarationColor rightRootAdmissible
          (fun stopped => stopped.1.2) closeSmaller callbackAvailable
          callbackScope leftReached rightReached sourceTypeEq rightEmbedding
          ⟨rightRoute'⟩ leftPayloadSizeLe rawAligned leftRigid
          ⟨costRegionSourceVariableName name, abstractEq⟩ rightBoundary
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · have leftProcess :=
        rho_applicationPlan_sourceType_eq_proc_of_not_quote leftReached.plan
          leftApplication (fun equality => leftNotQuote
            (leftApplication.trans (congrArg _ equality)))
      have aligned := rhoPlanStopProcessPartner_boundarySide_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq sourceAvailableEq
        leftEmbedding rightEmbedding ⟨rightRoute'⟩ rawAligned leftProcess
        rightBoundary
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · have leftEndpointAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
        rw [sourceTypeEq]
        exact rightEndpointAdmissible
      have leftProcess := rho_collectionPlan_sourceType_eq_proc
        leftReached.plan ⟨collectionType, leftCollection⟩
          leftEndpointAdmissible
      have aligned := rhoPlanStopProcessPartner_boundarySide_sourceAligned
        leftView rightView declarationColor rightRootAdmissible
        (fun stopped => stopped.1.2) closeSmaller callbackAvailable
        callbackScope leftReached rightReached sourceTypeEq sourceAvailableEq
        leftEmbedding rightEmbedding ⟨rightRoute'⟩ rawAligned leftProcess
        rightBoundary
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · exact (notBothBoundary ⟨leftBoundary', rightBoundary⟩).elim

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
