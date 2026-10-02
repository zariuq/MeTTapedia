import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticScope
import Mettapedia.GSLT.LanguageDef.EquationSubstitution

/-!
# Supported finite static-frame action

The existing support-indexed substitution restores arbitrary admitted target
values after source tagging and binder reinsertion. The visible/sealed context
split and typed equation relation are the existing ones. No normalization
stability assumption or second retained tree is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted
namespace ContinuationDecorationProfile.StaticSourceTerm

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}
  {profile : ContinuationDecorationProfile cut}
  {reflection : ReflectionExtension.AdmittedProfile theory.presentation.presentation.language}
  {color : CostStaticColor} {free targetFree : FreeTypeContext} {support : ContextSupport.Support}
  {sourceBound targetBound : List TypeExpr}
  {sort : LangSort theory.presentation.presentation.language}

/-- The actual source frame with all target binders visible at its root. -/
def reinsertAvailable
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    AvailableOpenPattern (profile.costWholeReflectionProfile reflection.1)
      profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetBound []
      (mapTypeExpr (color.symbolsOf theory) (.base sort.1)) :=
  AvailableOpenPattern.ofOpenPattern (term.reinsert nonprincipal thinning)

theorem reinsertAvailable_support
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound) :
    (term.reinsertAvailable nonprincipal thinning).typed.ReflectiveSupportSafeAt
      (profile.costWholeReflectionProfile reflection.1) support targetBound id :=
  HasType.ReflectiveSupportSafeAt.castBound (List.append_nil targetBound).symm
    (term.reinsert_support nonprincipal bareAllowed thinning)

/-- Restore target values at their declared dependency contexts. A value may
contain either static color or any admitted principal/apparatus constructor. -/
def actAvailable
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    (assignment : SupportedOpenAssignment (profile.costWholeReflectionProfile reflection.1)
      profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetFree support) :
    AvailableOpenPattern (profile.costWholeReflectionProfile reflection.1)
      profile.costWholeLanguage targetFree targetBound []
      (mapTypeExpr (color.symbolsOf theory) (.base sort.1)) :=
  (term.reinsertAvailable nonprincipal thinning).substitute assignment
    (term.reinsertAvailable_support nonprincipal bareAllowed thinning)

@[simp] theorem actAvailable_pattern
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    (assignment : SupportedOpenAssignment (profile.costWholeReflectionProfile reflection.1)
      profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetFree support) :
    (term.actAvailable nonprincipal bareAllowed thinning assignment).pattern =
      ReflectiveContextSupport.substituteAt (profile.costWholeReflectionProfile reflection.1)
        support assignment.assignment targetBound.length
        (ContextSubstitution.renameAmbientBVarsAt thinning.toTargetIndex 0
          (mapPattern (color.symbolsOf theory) term.term.1)) := rfl

/-- Vary the boundary values along actual typed target equation paths while
keeping the authored source frame fixed. This does not assume that changing
the source frame preserves its action. -/
theorem actAvailable_equationSetoid_pointwise
    (valid : profile.costWholeLanguage.validate = [])
    (reflectionValid : Mettapedia.OSLF.MeTTaIL.Reflection.validate
      profile.costWholeLanguage (profile.costWholeReflectionProfile reflection.1) = [])
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort)
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (bareAllowed : ∀ rule ∈ theory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ profile.wrappedLabels)
    (thinning : CostStaticTypeThinning theory color sourceBound targetBound)
    (first second : SupportedOpenAssignment (profile.costWholeReflectionProfile reflection.1)
      profile.costWholeLanguage (free.map (color.symbolsOf theory)) targetFree support)
    (equivalent : first.FiberEquivalent second) :
    (AvailableOpenPattern.equationSetoid profile.costWholeLanguage targetFree targetBound []
      (mapTypeExpr (color.symbolsOf theory) (.base sort.1))).r
      (term.actAvailable nonprincipal bareAllowed thinning first)
      (term.actAvailable nonprincipal bareAllowed thinning second) :=
  AvailableOpenPattern.equationSetoid_substitute_pointwise valid reflectionValid
    (term.reinsertAvailable nonprincipal thinning)
    (term.reinsertAvailable_support nonprincipal bareAllowed thinning)
    first second equivalent

end ContinuationDecorationProfile.StaticSourceTerm
end Mettapedia.GSLT.LanguageDef
