import Mettapedia.GSLT.LanguageDef.Cost.FiniteInteraction
import Mettapedia.GSLT.LanguageDef.ClosedSchemaInstantiation

/-!
# Typed instances of finite-bundle funded interaction

A typed simultaneous assignment instantiates the generated rule in any ambient
context. Both endpoints retain the wrapped sort, including substitutions whose
values refer to ambient variables. This is the schema-level typing theorem;
matching completeness and agreement with a particular executor are separate
operational comparisons.
-/

namespace Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

set_option autoImplicit false

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

theorem costWholeRedexSource_instantiated_hasType
    (profile : ContinuationDecorationProfile cut) (redexTyped : profile.RedexRetypable)
    {target : FreeTypeContext} {ambient : List TypeExpr}
    (assignment : TypedAssignment profile.costCoreLanguage
      profile.costWholeRedexFreeContext target ambient) :
    HasSort profile.costCoreLanguage target ambient
      (ContextSubstitution.substitute assignment.assignment profile.costWholeRedexSource)
      costWrappedSortName :=
  (profile.costWholeRedexSource_hasType redexTyped).instantiateClosed assignment

theorem costWholeRedexTarget_instantiated_hasType
    (profile : ContinuationDecorationProfile cut) (contractumTyped : profile.Wrappable)
    {target : FreeTypeContext} {ambient : List TypeExpr}
    (assignment : TypedAssignment profile.costCoreLanguage
      profile.costWholeRedexFreeContext target ambient) :
    HasSort profile.costCoreLanguage target ambient
      (ContextSubstitution.substitute assignment.assignment profile.costWholeRedexTarget)
      costWrappedSortName :=
  (profile.costWholeRedexTarget_hasType contractumTyped).instantiateClosed assignment

/-- Installing the selected rule changes the transition relation while
preserving the constructor-typing derivations of the Cost core. -/
theorem hasType_costWholeRedexLanguage (profile : ContinuationDecorationProfile cut)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType profile.costCoreLanguage free bound pattern type) :
    HasType profile.costWholeRedexLanguage free bound pattern type :=
  typed.weakenTerms (targetLanguage := profile.costWholeRedexLanguage)
    (fun _ membership => (membership : _ ∈ profile.costCoreLanguage.terms))

/-- Every admitted instance has the same sort on both sides in the actual
generated rule signature. Admission records types of schema images, rather
than assuming typing of the resulting contractum. -/
theorem costWholeRedex_instances_typed
    (profile : ContinuationDecorationProfile cut)
    (redexTyped : profile.RedexRetypable) (contractumTyped : profile.Wrappable)
    {target : FreeTypeContext} {ambient : List TypeExpr}
    (assignment : TypedAssignment profile.costCoreLanguage
      profile.costWholeRedexFreeContext target ambient) :
    HasSort profile.costWholeRedexLanguage target ambient
      (ContextSubstitution.substitute assignment.assignment profile.costWholeRedexSource)
      costWrappedSortName ∧
    HasSort profile.costWholeRedexLanguage target ambient
      (ContextSubstitution.substitute assignment.assignment profile.costWholeRedexTarget)
      costWrappedSortName :=
  ⟨profile.hasType_costWholeRedexLanguage
      (profile.costWholeRedexSource_instantiated_hasType redexTyped assignment),
    profile.hasType_costWholeRedexLanguage
      (profile.costWholeRedexTarget_instantiated_hasType contractumTyped assignment)⟩

end Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile
