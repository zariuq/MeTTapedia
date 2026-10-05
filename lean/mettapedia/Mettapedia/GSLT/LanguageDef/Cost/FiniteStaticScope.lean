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

namespace ContinuationDecorationProfile
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
