import Mettapedia.GSLT.LanguageDef.ContextRenamingScope
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticSupport

/-!
# Reflective open carriers for finite static frames

The actual finite source fibre maps to the existing generated language and
reinserts its ambient binders. All carrier fields, including quotation seals,
are proved. This is static-frame transport, not arbitrary principal compilation
or a substitution action on retained trees.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted StructuralMorphism ReflectionExtension

theorem CostStaticColor.binderSafeAt_mapPattern_symbolsOf
    (theory : IGSLT) (color : CostStaticColor)
    (quoteConstructor : String) (depth : Nat) (pattern : Pattern) :
    binderSafeAt ((color.symbolsOf theory).constructor quoteConstructor) depth
      (mapPattern (color.symbolsOf theory) pattern) =
      binderSafeAt quoteConstructor depth pattern := by
  apply WellSorted.binderSafeAt_mapPattern_of_constructor_injective
  cases color with
  | base => exact costBaseConstructorName_injective
  | wrapped => exact costWrappedConstructorName_injective

namespace ContinuationDecorationProfile
/-- Static Cost transport preserves every authored reflective scope boundary.
The selected color transports the corresponding source quotation exactly;
the opposite color is disjoint from every constructor in the mapped term and
therefore contributes only the ordinary locally nameless scope check. -/
theorem reflectiveScopeSafeAt_mapStatic
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (profile : ContinuationDecorationProfile cut)
    (reflection : ReflectionProfile) (color : CostStaticColor)
    {depth : Nat} {pattern : Pattern}
    (sourceSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
      reflection depth pattern)
    (mappedOrdinaryScope :
      (mapPattern (color.symbolsOf theory) pattern).isWellScopedAt depth = true) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt
      (profile.costWholeReflectionProfile reflection) depth
      (mapPattern (color.symbolsOf theory) pattern) := by
  intro targetPresentation targetMembership
  rw [costWholeReflectionProfile,
    costStaticReflectivePresentations, List.mem_append]
    at targetMembership
  rcases targetMembership with baseMembership | wrappedMembership
  · rcases List.mem_map.mp baseMembership with
      ⟨sourcePresentation, sourceMembership, rfl⟩
    cases color with
    | base =>
        simpa [costBaseReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbolsOf,
          costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
          costBaseLanguageDefSymbolMap] using
          (show binderSafeAt
              ((CostStaticColor.base.symbolsOf theory).constructor
                sourcePresentation.quoteConstructor) depth
              (mapPattern (CostStaticColor.base.symbolsOf theory) pattern) = true
            from by
              rw [CostStaticColor.binderSafeAt_mapPattern_symbolsOf]
              exact sourceSafe sourcePresentation sourceMembership)
    | wrapped =>
        have scopeEquality :=
          WellSorted.binderSafeAt_mapPattern_of_constructor_avoids
            (CostStaticColor.wrapped.symbolsOf theory)
            (costBaseConstructorName sourcePresentation.quoteConstructor)
            (fun constructor equality =>
              costBaseConstructorName_ne_wrapped
                sourcePresentation.quoteConstructor constructor equality.symm)
            depth pattern
        simpa [costBaseReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbolsOf,
          costBaseStaticSymbols, costBaseStaticReflectiveSymbols,
          costBaseLanguageDefSymbolMap] using
          (scopeEquality.trans mappedOrdinaryScope)
  · rcases List.mem_map.mp wrappedMembership with
      ⟨sourcePresentation, sourceMembership, rfl⟩
    cases color with
    | base =>
        have scopeEquality :=
          WellSorted.binderSafeAt_mapPattern_of_constructor_avoids
            (CostStaticColor.base.symbolsOf theory)
            (costWrappedConstructorName sourcePresentation.quoteConstructor)
            (fun constructor =>
              costBaseConstructorName_ne_wrapped constructor
                sourcePresentation.quoteConstructor)
            depth pattern
        simpa [costWrappedReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbolsOf,
          costWrappedStaticSymbols, costWrappedStaticReflectiveSymbols] using
          (scopeEquality.trans mappedOrdinaryScope)
    | wrapped =>
        simpa [costWrappedReflectivePresentationDecl,
          mapReflectivePresentation, CostStaticColor.symbolsOf,
          costWrappedStaticReflectiveSymbols] using
          (show binderSafeAt
              ((CostStaticColor.wrapped.symbolsOf theory).constructor
                sourcePresentation.quoteConstructor) depth
              (mapPattern (CostStaticColor.wrapped.symbolsOf theory) pattern) = true
            from by
              rw [CostStaticColor.binderSafeAt_mapPattern_symbolsOf]
              exact sourceSafe sourcePresentation sourceMembership)


namespace StaticSourceTerm

/-- Construct the complete existing reflective carrier after static tagging
and actual positional binder insertion. -/
def reinsert
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    {profile : ContinuationDecorationProfile cut}
    {reflection : ReflectionExtension.AdmittedProfile theory.presentation.presentation.language}
    {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    ReflectiveWellSorted.OpenPattern (profile.costWholeReflectionProfile reflection.1)
      profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetBound
      (mapTypeExpr (color.symbolsOf theory) (.base sort.1)) := by
  have typed := term.mapped_hasType nonprincipal
  have sorted : ReflectiveWellSorted.OpenPatternWellSorted
      (profile.costWholeReflectionProfile reflection.1)
      profile.costWholeLanguage (free.map (color.symbolsOf theory))
      (sourceBound.map (mapTypeExpr (color.symbolsOf theory)))
      (mapTypeExpr (color.symbolsOf theory) (.base sort.1))
      (mapPattern (color.symbolsOf theory) term.term.1) := by
    refine ⟨⟨typed, ?_, ?_, typed.isWellScopedAt⟩, ?_⟩
    · simpa only [hasCanonicalBinderMetadata_mapPattern] using term.term.2.1.2.1
    · simpa only [isObjectPattern_mapPattern] using term.term.2.1.2.2.1
    · have safe := profile.reflectiveScopeSafeAt_mapStatic reflection.1 color
        term.term.2.2 (by simpa only [List.length_map] using typed.isWellScopedAt)
      simpa only [List.length_map] using safe
  exact ⟨_, sorted.renameAmbientBVarsAt (inner := [])
    thinning.toTargetIndex thinning.preservesBoundTypes⟩

@[simp] theorem reinsert_pattern
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    {profile : ContinuationDecorationProfile cut}
    {reflection : ReflectionExtension.AdmittedProfile theory.presentation.presentation.language}
    {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    (term.reinsert nonprincipal thinning).1 =
      ContextSubstitution.renameAmbientBVarsAt thinning.toTargetIndex 0
        (mapPattern (color.symbolsOf theory) term.term.1) := rfl

/-- The constructed carrier retains the exact target support certificate. -/
theorem reinsert_support
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    {profile : ContinuationDecorationProfile cut}
    {reflection : ReflectionExtension.AdmittedProfile theory.presentation.presentation.language}
    {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
    {sourceBound targetBound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    (term.reinsert nonprincipal thinning).2.1.1.ReflectiveSupportSafeAt
      (profile.costWholeReflectionProfile reflection.1) support targetBound id :=
  (term.reinsert_reflectiveSupport nonprincipal bareAllowed thinning).castTyping

end StaticSourceTerm
end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
