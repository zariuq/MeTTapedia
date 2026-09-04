import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- Rho's only bare-collection rule is the parallel: any authored rule
using a bare collection has category `Proc`. -/
theorem kimi_rho_bare_src_category (src : GrammarRule)
    (membership : src ∈ rhoCalc.terms)
    (bare : WellSorted.UsesBareCollection src) :
    src.category = "Proc" := by
  change src ∈ [rhoCalc.terms[0], rhoCalc.terms[1], rhoCalc.terms[2],
    rhoCalc.terms[3], rhoCalc.terms[4], rhoCalc.terms[5]] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  obtain ⟨parameterName, bareCollectionType, bareElementType, bareShape⟩ :=
    bare
  rcases membership with first | second | third | fourth | fifth | sixth <;>
    subst src <;> simp [rhoCalc] at bareShape ⊢ <;>
    (try exact TypeExpr.noConfusion bareShape.2)

/-- The whole-language rule behind a bare singleton-collection parameter
has category a `Proc` colour image: rho's parallel, in either copy. -/
theorem kimi_bare_whole_rule_category {rule : GrammarRule}
    (membership : rule ∈ rhoCIGSLT.costWholeLanguage.terms)
    (bare : WellSorted.UsesBareCollection rule) :
    rule.category = costBaseSortName "Proc" ∨
      rule.category = costWrappedSortName := by
  have coreMembership : rule ∈ rhoCIGSLT.costCoreLanguage.terms := by
    simpa only [rhoCIGSLT.costWholeLanguage_terms] using membership
  obtain ⟨constructor, materializes⟩ :=
    rhoCIGSLT.exists_declaredCostConstructor_of_mem rule coreMembership
  rw [← materializes] at bare ⊢
  rcases constructor with ⟨shape, declared⟩
  cases shape with
  | base sourceConstructor =>
      have sourceBare : WellSorted.UsesBareCollection sourceConstructor.1 :=
        (usesBareCollection_costBaseConstructor_iff rhoInteractionCut
          sourceConstructor.1).mp bare
      left
      simp [CIGSLT.materializeDeclaredCostConstructor, costBaseConstructor,
        kimi_rho_bare_src_category sourceConstructor.1 sourceConstructor.2
          sourceBare]
  | wrapped sourceConstructor =>
      have sourceBare : WellSorted.UsesBareCollection sourceConstructor.1 :=
        (usesBareCollection_costWrappedConstructor_iff sourceConstructor.1
          ).mp bare
      right
      simp [CIGSLT.materializeDeclaredCostConstructor, costWrappedConstructor,
        kimi_rho_bare_src_category sourceConstructor.1 sourceConstructor.2
          sourceBare, rho_interactingSort_name]
  | apparatus kind =>
      obtain ⟨parameterName, collectionType, elementType, shape⟩ := bare
      cases kind <;>
        simp [CIGSLT.materializeDeclaredCostConstructor,
          CostApparatusConstructor.grammarRule,
          costSignatureUnitConstructor, costSignatureProductConstructor,
          costSignedConstructor, costTokenStackEmptyConstructor,
          costTokenStackConsConstructor, costFundingConstructor,
          costContactConstructor] at shape

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
