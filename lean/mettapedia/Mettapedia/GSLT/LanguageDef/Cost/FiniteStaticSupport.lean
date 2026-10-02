import Mettapedia.GSLT.LanguageDef.ConstructorFragmentSupport
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticTypingCore
import Mettapedia.GSLT.LanguageDef.Cost.FiniteReflection
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticSourceTerm
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticThinning
import Mettapedia.GSLT.LanguageDef.ContextRenamingSupport

/-!
# Reflective support in finite Cost static frames

The actual finite declaration rows and existing reflection transport discharge
common row-wise support transport. Available target binders stay fixed;
principal introductions remain outside the static fragment.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open StructuralMorphism WellSorted ReflectionExtension
namespace ContinuationDecorationProfile

@[simp]
theorem reflectiveIsQuoteConstructor_mapStatic
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (profile : ContinuationDecorationProfile cut) (reflection : ReflectionProfile)
    (color : CostStaticColor) (constructor : String) :
    ReflectiveContextSupport.isQuoteConstructor
        (profile.costWholeReflectionProfile reflection)
        ((color.symbolsOf theory).constructor constructor) =
      ReflectiveContextSupport.isQuoteConstructor
        reflection constructor := by
  unfold ReflectiveContextSupport.isQuoteConstructor
  simp only [costWholeReflectionProfile, costStaticReflectivePresentations, List.any_append]
  cases color with
  | base =>
      rw [Bool.eq_iff_iff]
      simp only [List.any_map, Function.comp_apply, Bool.or_eq_true,
        List.any_eq_true, beq_iff_eq]
      constructor
      · rintro (⟨declaration, membership, equality⟩ |
          ⟨declaration, _membership, equality⟩)
        · refine ⟨declaration, membership, ?_⟩
          apply costBaseConstructorName_injective
          simpa [CostStaticColor.symbolsOf,
            costBaseReflectivePresentationDecl, mapReflectivePresentation,
            costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
            costBaseLanguageDefSymbolMap] using equality
        · have impossible :
              costWrappedConstructorName declaration.quoteConstructor =
                costBaseConstructorName constructor := by
            simpa [CostStaticColor.symbolsOf,
              costWrappedReflectivePresentationDecl,
              mapReflectivePresentation, costWrappedStaticSymbols,
              costWrappedStaticReflectiveSymbols, costBaseStaticSymbols,
              costBaseLanguageDefSymbolMap] using equality
          exact False.elim
            (costBaseConstructorName_ne_wrapped constructor
              declaration.quoteConstructor impossible.symm)
      · rintro ⟨declaration, membership, equality⟩
        left
        refine ⟨declaration, membership, ?_⟩
        simp [CostStaticColor.symbolsOf,
          costBaseReflectivePresentationDecl, mapReflectivePresentation,
          costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
          costBaseLanguageDefSymbolMap, equality]
  | wrapped =>
      rw [Bool.eq_iff_iff]
      simp only [List.any_map, Function.comp_apply, Bool.or_eq_true,
        List.any_eq_true, beq_iff_eq]
      constructor
      · rintro (⟨declaration, _membership, equality⟩ |
          ⟨declaration, membership, equality⟩)
        · have impossible :
              costBaseConstructorName declaration.quoteConstructor =
                costWrappedConstructorName constructor := by
            simpa [CostStaticColor.symbolsOf,
              costBaseReflectivePresentationDecl, mapReflectivePresentation,
              costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
              costBaseLanguageDefSymbolMap,
              costWrappedStaticSymbols] using equality
          exact False.elim
            (costBaseConstructorName_ne_wrapped
              declaration.quoteConstructor constructor impossible)
        · refine ⟨declaration, membership, ?_⟩
          apply costWrappedConstructorName_injective
          simpa [CostStaticColor.symbolsOf,
            costWrappedReflectivePresentationDecl,
            mapReflectivePresentation, costWrappedStaticSymbols,
            costWrappedStaticReflectiveSymbols] using equality
      · rintro ⟨declaration, membership, equality⟩
        right
        refine ⟨declaration, membership, ?_⟩
        simp [CostStaticColor.symbolsOf,
          costWrappedReflectivePresentationDecl, mapReflectivePresentation,
          costWrappedStaticSymbols, costWrappedStaticReflectiveSymbols,
          equality]

/-- The ordinary typing map also preserves reflective support at the fixed
target availability. The bare-row condition is a declaration inventory law. -/
theorem mapStatic_reflectiveSupport
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels)
    (reflection : ReflectionProfile) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors theory.presentation.presentation.language
      (· ∈ profile.wrappedLabels) free bound pattern type)
    {support : ContextSupport.Support} {available : List TypeExpr}
    (safe : typed.toHasType.ReflectiveSupportSafeAt reflection support available
      (mapTypeExpr (color.symbolsOf theory))) :
    (profile.mapStatic_hasType nonprincipal color typed).ReflectiveSupportSafeAt
      (profile.costWholeReflectionProfile reflection) support available id := by
  have rows : ∀ rule ∈ theory.presentation.presentation.language.terms,
      rule.label ∈ profile.wrappedLabels →
      ∃ targetRule ∈ profile.costWholeLanguage.terms,
        targetRule.label = (color.symbolsOf theory).constructor rule.label ∧
        targetRule.category = (color.symbolsOf theory).sort rule.category ∧
        targetRule.params = rule.params.map (mapTermParam (color.symbolsOf theory)) := by
    intro rule member admitted
    obtain ⟨targetRule, targetMember, rest⟩ := profile.staticRows nonprincipal color rule member admitted
    exact ⟨targetRule, profile.generatedTerms_mem_costWhole targetRule targetMember, rest⟩
  have transported := typed.mapRows_reflectiveSupport (color.symbolsOf theory) rows bareAllowed
    (fun rule _ _ => profile.reflectiveIsQuoteConstructor_mapStatic reflection color rule.label) safe
  exact transported.castTyping

/-- The finite retained-source certificate supplies the source support
premise; the generated term keeps its exact target dependency context. -/
theorem StaticSourceTerm.mapped_reflectiveSupport
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    {profile : ContinuationDecorationProfile cut}
    {reflection : AdmittedProfile theory.presentation.presentation.language}
    {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort
      theory.presentation.presentation.language}
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels) :
    (term.mapped_hasType nonprincipal).ReflectiveSupportSafeAt
      (profile.costWholeReflectionProfile reflection.1) support targetBound id :=
  profile.mapStatic_reflectiveSupport nonprincipal bareAllowed reflection.1 color
    term.supported term.safe.castTyping

/-- Reinsertion preserves the target dependency context already certified by
the source fibre, including quotation's support reset. Quotation binder scope
remains a separate obligation of the reflective open-term carrier. -/
theorem StaticSourceTerm.reinsert_reflectiveSupport
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    {profile : ContinuationDecorationProfile cut}
    {reflection : AdmittedProfile theory.presentation.presentation.language}
    {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort
      theory.presentation.presentation.language}
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    (term.reinsert_hasType nonprincipal thinning).ReflectiveSupportSafeAt
      (profile.costWholeReflectionProfile reflection.1) support targetBound id := by
  have mapped := term.mapped_reflectiveSupport nonprincipal bareAllowed
  have inserted := mapped.renameAmbientBVarsAt (inner := [])
    thinning.toTargetIndex thinning.preservesBoundTypes
  exact inserted.castTyping

end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
