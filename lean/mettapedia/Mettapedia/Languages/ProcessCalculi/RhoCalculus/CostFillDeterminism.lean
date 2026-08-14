import Mettapedia.GSLT.LanguageDef.CostWholeLanguageDeterminism
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-!
# Determinism instances for the generated rho Cost language

The typed fill descent takes two determinism hypotheses.  Label determinism
holds for every continued interactive GSLT through validated label
collision-freeness.  Collection-choice determinism for rho is discharged by
classifying every generated rule that carries a single bare-collection
parameter: only the two parallel copies qualify, and their result
categories separate the base and wrapped fibres.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Distinct generated rho Cost rules never share a wire label. -/
theorem rho_costWholeLanguage_labelDeterministic :
    LabelDeterministic rhoCIGSLT.costWholeLanguage :=
  rhoCIGSLT.costWholeLanguage_labelDeterministic

/-- Pure rho collection typing chooses one element type at a fixed
collection constructor and result category. -/
theorem rho_collectionChoiceDeterministic :
    CollectionChoiceDeterministic rhoCalc :=
  collectionChoiceDeterministic_of_check (by decide)

/-- Every generated rho Cost rule with one bare-collection parameter is one
of the two parallel copies, classified by its result category. -/
theorem rho_collectionRule_cases {rule : GrammarRule}
    (membership : rule ∈ rhoCIGSLT.costWholeLanguage.terms)
    {name : String} {collectionType : CollType} {elementType : TypeExpr}
    (shape : rule.params =
      [.simple name (.collection collectionType elementType)]) :
    (collectionType = rhoReflectivePresentation.parallelCollection ∧
      rule.category = costBaseSortName "Proc" ∧
        elementType = .base (costBaseSortName "Proc")) ∨
      (collectionType = rhoReflectivePresentation.parallelCollection ∧
        rule.category = costWrappedSortName ∧
        elementType = .base costWrappedSortName) := by
  have memberships := membership
  rw [CIGSLT.costWholeLanguage_terms] at memberships
  have split : rule ∈ rhoCIGSLT.continuationRetyping.generatedLanguage.terms ∨
      rule ∈ costCoreConstructors
        rhoCIGSLT.theory.presentation.interactingSort.1.name := by
    simpa [CIGSLT.costCoreLanguage, List.mem_append] using memberships
  rcases split with generated | apparatus
  · rw [show rhoCIGSLT.continuationRetyping.generatedLanguage.terms =
        rhoCalc.terms.map (costBaseConstructor rhoInteractionCut) ++
          rhoContinuationRetyping.wrappedConstructors.map
            (fun constructor =>
              costWrappedConstructor (theory := rhoIGSLT) constructor.1)
      from rfl] at generated
    rcases List.mem_append.mp generated with baseSide | wrappedSide
    · obtain ⟨sourceRule, sourceMembership, ruleEq⟩ :=
        List.mem_map.mp baseSide
      subst ruleEq
      change sourceRule ∈ [rhoCalc.terms[0], rhoCalc.terms[1],
        rhoCalc.terms[2], rhoCalc.terms[3], rhoCalc.terms[4],
        rhoCalc.terms[5]] at sourceMembership
      simp only [List.mem_cons, List.not_mem_nil, or_false]
        at sourceMembership
      rcases sourceMembership with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [costBaseConstructor, rhoCalc] at shape
      · rw [rho_costBaseDropConstructor_params] at shape
        simp at shape
      · rw [rho_costBaseQuoteConstructor_params] at shape
        simp at shape
      · rw [rho_costBaseParallelConstructor_params] at shape
        simp only [List.cons.injEq, TermParam.simple.injEq,
          TypeExpr.collection.injEq, and_true] at shape
        exact Or.inl ⟨shape.2.1.symm, rfl, shape.2.2.symm⟩
      · rw [rho_costBaseOutputConstructor_params] at shape
        simp at shape
      · rw [rho_costBaseInputConstructor_params] at shape
        simp at shape
    · obtain ⟨constructor, _, ruleEq⟩ := List.mem_map.mp wrappedSide
      subst ruleEq
      have sourceMembership := constructor.2
      change constructor.1 ∈ [rhoCalc.terms[0], rhoCalc.terms[1],
        rhoCalc.terms[2], rhoCalc.terms[3], rhoCalc.terms[4],
        rhoCalc.terms[5]] at sourceMembership
      simp only [List.mem_cons, List.not_mem_nil, or_false]
        at sourceMembership
      rcases sourceMembership with sourceEq | sourceEq | sourceEq |
        sourceEq | sourceEq | sourceEq <;> rw [sourceEq] at shape ⊢
      · simp [costWrappedConstructor, rhoCalc] at shape
      · rw [rho_costWrappedDropConstructor_params] at shape
        simp at shape
      · simp [costWrappedConstructor, mapParameterType,
          costWrappedTypeExpr, rhoCalc, rhoIGSLT,
          rhoInteractivePresentation, TypeDecl.plain, TypeExpr.name,
          TypeExpr.proc, TypeExpr.baseType] at shape
      · rw [rho_costWrappedParallelConstructor_params] at shape
        simp only [List.cons.injEq, TermParam.simple.injEq,
          TypeExpr.collection.injEq, and_true] at shape
        refine Or.inr ⟨shape.2.1.symm, ?_, shape.2.2.symm⟩
        simp [costWrappedConstructor, rhoCalc, rhoIGSLT,
          rhoInteractivePresentation, TypeDecl.plain]
      · simp [costWrappedConstructor, mapParameterType,
          costWrappedTypeExpr, rhoCalc, rhoIGSLT,
          rhoInteractivePresentation, TypeDecl.plain, TypeExpr.name,
          TypeExpr.proc, TypeExpr.baseType] at shape
      · simp [costWrappedConstructor, mapParameterType,
          costWrappedTypeExpr, rhoCalc, rhoIGSLT,
          rhoInteractivePresentation, TypeDecl.plain, TypeExpr.name,
          TypeExpr.proc, TypeExpr.funType, TypeExpr.baseType] at shape
  · change rule ∈ [costSignatureUnitConstructor,
      costSignatureProductConstructor,
      costSignedConstructor
        rhoCIGSLT.theory.presentation.interactingSort.1.name,
      costTokenStackEmptyConstructor, costTokenStackConsConstructor,
      costFundingConstructor, costContactConstructor] at apparatus
    simp only [List.mem_cons, List.not_mem_nil, or_false] at apparatus
    rcases apparatus with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [costSignatureUnitConstructor] at shape
    · simp [costSignatureProductConstructor] at shape
    · simp [costSignedConstructor] at shape
    · simp [costTokenStackEmptyConstructor] at shape
    · simp [costTokenStackConsConstructor] at shape
    · simp [costFundingConstructor] at shape
    · simp [costContactConstructor] at shape

/-- A generated rho Cost collection at one collection type and result
category selects one element type. -/
theorem rho_costWholeLanguage_collectionChoiceDeterministic :
    CollectionChoiceDeterministic rhoCIGSLT.costWholeLanguage := by
  intro leftRule rightRule leftName rightName collectionType leftElementType
    rightElementType leftMembership rightMembership leftShape rightShape
    categoriesEq
  rcases rho_collectionRule_cases leftMembership leftShape with
    ⟨_, leftCategory, leftElement⟩ | ⟨_, leftCategory, leftElement⟩ <;>
    rcases rho_collectionRule_cases rightMembership rightShape with
      ⟨_, rightCategory, rightElement⟩ | ⟨_, rightCategory, rightElement⟩
  · exact leftElement.trans rightElement.symm
  · exact absurd (leftCategory.symm.trans (categoriesEq.trans rightCategory))
      (by decide)
  · exact absurd (leftCategory.symm.trans (categoriesEq.trans rightCategory))
      (by decide)
  · exact leftElement.trans rightElement.symm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
