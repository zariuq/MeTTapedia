import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySameColorParallelStopApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Away from boundary and parallel cells, a same-colour Quote side is either
a paired Quote or has a variable canonical result. -/
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
      rcases CostStaticRegionPlan.rootClass_cases rightReached.plan with rigid | application |
          collection | boundary
      · rcases CostStaticRegionPlan.rigid_cases_typed rightReached.plan rigid with
          ⟨index, sourceIndex, payloadEq, _⟩ |
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
      rcases CostStaticRegionPlan.rootClass_cases leftReached.plan with rigid | application |
          collection | boundary
      · rcases CostStaticRegionPlan.rigid_cases_typed leftReached.plan rigid with
          ⟨index, sourceIndex, payloadEq, _⟩ |
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

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
