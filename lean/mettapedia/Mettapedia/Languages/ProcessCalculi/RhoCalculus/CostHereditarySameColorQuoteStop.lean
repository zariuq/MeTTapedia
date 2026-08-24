import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySameColorParallelStopApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryVariableStopApex

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Away from certified boundaries, a same-colour Quote side is either a
paired Quote or has a variable canonical result.  The non-Quote partner has
the same `Name` source type; rho's remaining application and collection plans
are `Proc`-typed, while a rigid `Name` plan is a bound or free variable. -/
theorem rho_sameColorQuoteSide_quotePair_or_canonicalIsVariable
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    (leftNotBoundary : ¬ leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightNotBoundary : ¬ rightReached.plan.rootClass.IsCertifiedBoundary)
    (quoteSide : leftReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor ∨
      rightReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload) :
    RhoPlanStopQuotePairCell leftReached.plan.rootClass
        rightReached.plan.rootClass ∨
      ((∃ index, canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) leftPayload = .bvar index) ∨
        ∃ name, canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) leftPayload = .fvar name) := by
  rcases quoteSide with leftQuote | rightQuote
  · by_cases rightQuote : rightReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor
    · exact Or.inl ⟨leftQuote, rightQuote⟩
    · apply Or.inr
      have leftName := rho_applicationPlan_sourceType_eq_name_of_quoteRoot
        leftReached.plan leftQuote
      rcases CostStaticRegionPlan.rootClass_cases rightReached.plan with rigid |
          application | collection | boundary
      · rcases CostStaticRegionPlan.rigid_cases_typed rightReached.plan rigid
          with ⟨index, sourceIndex, payloadEq, _⟩ |
          ⟨name, payloadEq, _, _⟩ |
          ⟨binder, body, abstractBody, domain, codomain, payloadEq, _, typeEq⟩ |
          ⟨arity, binders, body, abstractBody, domain, codomain, payloadEq, _,
            typeEq⟩
        · rw [payloadEq] at canonical
          exact Or.inl ⟨index, canonical.trans (by rfl)⟩
        · rw [payloadEq] at canonical
          exact Or.inr ⟨name, canonical.trans (by rfl)⟩
        · have impossible : (TypeExpr.base "Name") =
              .arrow domain codomain :=
            leftName.symm.trans (sourceTypeEq.trans typeEq)
          cases impossible
        · have impossible : (TypeExpr.base "Name") =
              .arrow (.multiBinder domain) codomain :=
            leftName.symm.trans (sourceTypeEq.trans typeEq)
          cases impossible
      · obtain ⟨constructor, applicationClass⟩ := application
        have notQuote : constructor ≠
            rhoReflectivePresentation.quoteConstructor := by
          intro constructorEq
          exact rightQuote (applicationClass.trans
            (congrArg CostStaticPlanRootClass.application constructorEq))
        have rightProcess := rho_applicationPlan_sourceType_eq_proc_of_not_quote
          rightReached.plan applicationClass notQuote
        have impossible : (TypeExpr.base "Name") = .base "Proc" :=
          leftName.symm.trans (sourceTypeEq.trans rightProcess)
        have : ("Name" : String) = "Proc" := TypeExpr.base.inj impossible
        contradiction
      · obtain ⟨collectionType, collectionClass⟩ := collection
        have rightProcess := rho_collectionPlan_sourceType_eq_proc
          rightReached.plan ⟨collectionType, collectionClass⟩ rightAdmissible
        have impossible : (TypeExpr.base "Name") = .base "Proc" :=
          leftName.symm.trans (sourceTypeEq.trans rightProcess)
        have : ("Name" : String) = "Proc" := TypeExpr.base.inj impossible
        contradiction
      · exact (rightNotBoundary boundary).elim
  · by_cases leftQuote : leftReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor
    · exact Or.inl ⟨leftQuote, rightQuote⟩
    · apply Or.inr
      have rightName := rho_applicationPlan_sourceType_eq_name_of_quoteRoot
        rightReached.plan rightQuote
      have leftAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
        rw [sourceTypeEq]
        exact rightAdmissible
      rcases CostStaticRegionPlan.rootClass_cases leftReached.plan with rigid |
          application | collection | boundary
      · rcases CostStaticRegionPlan.rigid_cases_typed leftReached.plan rigid
          with ⟨index, sourceIndex, payloadEq, _⟩ |
          ⟨name, payloadEq, _, _⟩ |
          ⟨binder, body, abstractBody, domain, codomain, payloadEq, _, typeEq⟩ |
          ⟨arity, binders, body, abstractBody, domain, codomain, payloadEq, _,
            typeEq⟩
        · exact Or.inl ⟨index, by rw [payloadEq]; rfl⟩
        · exact Or.inr ⟨name, by rw [payloadEq]; rfl⟩
        · have impossible : TypeExpr.arrow domain codomain = .base "Name" :=
            typeEq.symm.trans (sourceTypeEq.trans rightName)
          cases impossible
        · have impossible : TypeExpr.arrow (.multiBinder domain) codomain =
              .base "Name" :=
            typeEq.symm.trans (sourceTypeEq.trans rightName)
          cases impossible
      · obtain ⟨constructor, applicationClass⟩ := application
        have notQuote : constructor ≠
            rhoReflectivePresentation.quoteConstructor := by
          intro constructorEq
          exact leftQuote (applicationClass.trans
            (congrArg CostStaticPlanRootClass.application constructorEq))
        have leftProcess := rho_applicationPlan_sourceType_eq_proc_of_not_quote
          leftReached.plan applicationClass notQuote
        have impossible : (TypeExpr.base "Proc") = .base "Name" :=
          leftProcess.symm.trans (sourceTypeEq.trans rightName)
        have : ("Proc" : String) = "Name" := TypeExpr.base.inj impossible
        contradiction
      · obtain ⟨collectionType, collectionClass⟩ := collection
        have leftProcess := rho_collectionPlan_sourceType_eq_proc leftReached.plan
          ⟨collectionType, collectionClass⟩ leftAdmissible
        have impossible : (TypeExpr.base "Proc") = .base "Name" :=
          leftProcess.symm.trans (sourceTypeEq.trans rightName)
        have : ("Proc" : String) = "Name" := TypeExpr.base.inj impossible
        contradiction
      · exact (leftNotBoundary boundary).elim

/-- A strictly smaller same-colour stop with an authored Quote side restores
in the enclosing semantic cospan.  Paired Quotes use the compact hereditary
elaboration supplied at the smaller measure; a lone Quote can share its
canonical result only with a bound or free variable. -/
noncomputable def rho_sameColorQuoteStop_commonRestorationApex
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller color targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
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
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    {parentMeasure : Nat}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation)
      (RhoCanonicalRawStop color parentMeasure) leftPayload rightPayload)
    (leftNotBoundary : ¬ leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightNotBoundary : ¬ rightReached.plan.rootClass.IsCertifiedBoundary)
    (quoteSide : leftReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor ∨
      rightReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor)
    (smaller : sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
    CostCanonicalTypeRoute.rho_admissible rightRoute' rightRootAdmissible
  have canonical := rawAligned.canonicalize_eq
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation) (fun stopped => stopped.1.2)
  rcases rho_sameColorQuoteSide_quotePair_or_canonicalIsVariable leftReached
      rightReached sourceTypeEq rightAdmissible leftNotBoundary
      rightNotBoundary quoteSide canonical with quotePair | variableCase
  · obtain ⟨leftEmbedding'⟩ := leftEmbedding
    obtain ⟨rightEmbedding'⟩ := rightEmbedding
    exact quotePlanStops_commonRestorationApex_of_closeSmaller leftView
      rightView color rightRootAdmissible closeSmaller leftReached rightReached
      leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
      sourceAvailableEq leftEmbedding' rightEmbedding' rightRoute' rawAligned
      quotePair.1 quotePair.2 smaller callbackAvailable callbackScope
      callbackRoot
  · subst leftAbstractEq
    subst rightAbstractEq
    exact rho_reachedPlanPairCommonApex_of_sameColorVariable leftView rightView
      callbackAvailable callbackScope callbackRoot leftReached rightReached
      sourceBoundEq targetBoundEq thinningEq canonical variableCase

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
