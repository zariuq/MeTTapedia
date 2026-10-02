import Mettapedia.GSLT.LanguageDef.Cost.StaticTypeThinning
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticSourceTerm

/-!
# Typed insertion of finite-profile static source terms

A supported authored frame maps into the existing finite Cost language and
then embeds its ambient variables into an arbitrary mixed target context.
This constructs the typing prerequisite for retained region insertion. It
does not claim a reflective support action or a retained normalization law.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted
namespace ContinuationDecorationProfile

/-- Static declaration transport and exact binder insertion compose. -/
theorem mapStatic_hasType_thinning
    {theory : IGSLT} {cut : InteractionCutPresentation theory}
    (profile : ContinuationDecorationProfile cut)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (color : CostStaticColor)
    {free : FreeTypeContext} {sourceBound targetBound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasTypeWithConstructors theory.presentation.presentation.language
      (· ∈ profile.wrappedLabels) free sourceBound pattern type)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    HasType profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetBound
      (ContextSubstitution.renameAmbientBVarsAt thinning.toTargetIndex 0
        (mapPattern (color.symbolsOf theory) pattern))
      (mapTypeExpr (color.symbolsOf theory) type) :=
  thinning.hasType_renameAmbient (inner := [])
    (profile.mapStatic_hasType nonprincipal color typed)

namespace StaticSourceTerm

/-- The source fibre's actual representative is well typed after reinsertion.
Its recorded target support remains separate from this typing conclusion. -/
theorem reinsert_hasType
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
    HasType profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetBound
      (ContextSubstitution.renameAmbientBVarsAt thinning.toTargetIndex 0
        (mapPattern (color.symbolsOf theory) term.term.1))
      (mapTypeExpr (color.symbolsOf theory) (.base sort.1)) :=
  profile.mapStatic_hasType_thinning nonprincipal color term.supported thinning

end StaticSourceTerm
end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
