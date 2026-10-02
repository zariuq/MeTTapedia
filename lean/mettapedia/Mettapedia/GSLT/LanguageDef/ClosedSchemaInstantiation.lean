import Mettapedia.GSLT.LanguageDef.ContextSubstitution

/-!
# Instantiating closed schemas in an ambient context

A schema closed in its de Bruijn context may still contain named parameters.
Its local binders remain fixed when it is placed in a larger ambient context;
typed parameter substitution may then introduce terms from that context.
These laws use the existing capture-avoiding substitution and typing judgment.
-/

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

set_option autoImplicit false

/-- Adding ambient variables to a de Bruijn-closed schema leaves its syntax
unchanged, including its own local binders. -/
theorem HasType.weakenEmptyBound {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free [] pattern type) (ambient : List TypeExpr) :
    HasType language free ambient pattern type := by
  have weakened := typed.liftBVars_insert (inner := []) (outer := []) (inserted := ambient)
  have isScoped : pattern.isWellScopedAt 0 = true := typed.isWellScopedAt
  have unchanged := liftBVars_eq_self_of_isWellScopedAt
    (shift := ambient.length) isScoped
  simpa only [List.nil_append, List.append_nil, List.length_nil, unchanged] using weakened

/-- Named parameters can be instantiated by arbitrary well-typed ambient
terms without capturing the schema's locally bound variables. -/
theorem HasType.instantiateClosed {language : LanguageDef} {source target : FreeTypeContext}
    {pattern : Pattern} {type : TypeExpr} {ambient : List TypeExpr}
    (typed : HasType language source [] pattern type)
    (assignment : TypedAssignment language source target ambient) :
    HasType language target ambient
      (ContextSubstitution.substitute assignment.assignment pattern) type := by
  exact (typed.weakenEmptyBound ambient).substituteAt assignment (inner := [])

#print axioms HasType.instantiateClosed

end Mettapedia.GSLT.LanguageDef.WellSorted
