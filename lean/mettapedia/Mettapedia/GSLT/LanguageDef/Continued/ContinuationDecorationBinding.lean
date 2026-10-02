import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecoration
import Mettapedia.GSLT.LanguageDef.StructuralPatternBindingNaturality
import Mettapedia.GSLT.LanguageDef.TypedBoundSubstitution

/-!
# Binder elimination for finite continuation decoration

Continuation payloads can live under local binders.  Eliminating a selected
binder uses the existing simultaneous substitution, lifted through the exact
remaining local context.  Finite contractum decoration commutes with that
operation because its symbol action leaves binding structure intact.

These are substitution and sorting laws.  They do not identify static
signature products, supply funding, or authorize an operational firing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

namespace WellSorted

/-- A typed replacement eliminates the first bound variable and shifts each
older variable down once, using the existing executable singleton assignment. -/
def TypedBoundAssignment.single {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {replacement : Pattern} {domain : TypeExpr}
    (typed : HasType language free bound replacement domain) :
    TypedBoundAssignment language free (domain :: bound) bound where
  assignment := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.single replacement
  typed := by
    intro index type lookup
    cases index with
    | zero =>
        have same : domain = type := Option.some.inj lookup
        subst type
        exact typed
    | succ index => exact HasType.bvar lookup

/-- Binder elimination preserves typing below an arbitrary heterogeneous local
prefix.  The replacement is lifted below that prefix, so its free ambient
indices cannot be captured by the retained local binders. -/
theorem HasType.instantiateBVarAt {language : LanguageDef} {free : FreeTypeContext}
    {bound binders : List TypeExpr} {body replacement : Pattern} {domain result : TypeExpr}
    (bodyTyped : HasType language free (binders ++ domain :: bound) body result)
    (replacementTyped : HasType language free bound replacement domain) :
    HasType language free (binders ++ bound)
      (instantiateBVarAt binders.length replacement body) result := by
  have substituted := bodyTyped.substituteBound
    ((TypedBoundAssignment.single replacementTyped).liftContext binders)
  change HasType language free (binders ++ bound)
    (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift binders.length
        (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.single replacement)) body) result
      at substituted
  rwa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_lift_single] at substituted

/-- The input continuation's innermost binder can be filled by a typed
argument in its ambient context. -/
theorem HasType.instantiateBVar {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {body replacement : Pattern} {domain result : TypeExpr}
    (bodyTyped : HasType language free (domain :: bound) body result)
    (replacementTyped : HasType language free bound replacement domain) :
    HasType language free bound (instantiateBVar replacement body) result :=
  HasType.instantiateBVarAt (binders := []) bodyTyped replacementTyped

end WellSorted

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- The existing finite contractum action commutes with binder elimination at
every local depth, including inside quoted continuation payloads. -/
theorem mapContractum_instantiateBVarAt (profile : ContinuationDecorationProfile cut)
    (depth : Nat) (replacement body : Pattern) :
    profile.mapContractum (instantiateBVarAt depth replacement body) =
      instantiateBVarAt depth (profile.mapContractum replacement)
        (profile.mapContractum body) :=
  mapPattern_instantiateBVarAt profile.contractumSymbols depth replacement body

end ContinuationDecorationProfile

/-- The ambient variable in the replacement stays outside the retained local
lambda.  Substitution that inserts it without lifting would capture it. -/
theorem continuation_substitution_avoids_capture :
    instantiateBVar (.bvar 0) (.lambda none (.bvar 1)) =
      .lambda none (.bvar 1) ∧
    instantiateBVar (.bvar 0) (.lambda none (.bvar 1)) ≠
      .lambda none (.bvar 0) := by
  decide +kernel

#print axioms WellSorted.HasType.instantiateBVarAt
#print axioms ContinuationDecorationProfile.mapContractum_instantiateBVarAt
#print axioms continuation_substitution_avoids_capture

end Mettapedia.GSLT.LanguageDef
