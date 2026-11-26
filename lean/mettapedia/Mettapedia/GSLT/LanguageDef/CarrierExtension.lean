import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# Extending a declared carrier signature

A typing proof reads the constructor declarations and the literal
carriers. Adding declarations preserves the proof, without a hypothesis
about directed rewrites or equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CarrierWellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)

theorem builtin_of_signature_inclusion {source target : LanguageDef}
    (types : source.types ⊆ target.types) {spelling : String} {sort : TypeExpr}
    (typed : BuiltinAtomHasType source spelling sort) :
    BuiltinAtomHasType target spelling sort := by
  obtain ⟨decl, member, sortEq, accepted⟩ := typed
  exact ⟨decl, types member, sortEq, accepted⟩

mutual
theorem HasType.of_signature_inclusion {source target : LanguageDef} {free : FreeTypeContext}
    (types : source.types ⊆ target.types) (terms : source.terms ⊆ target.terms) :
    ∀ {bound : List TypeExpr} {pattern : Pattern} {sort : TypeExpr},
      HasType source free bound pattern sort → HasType target free bound pattern sort
  | _, _, _, .bvar found => .bvar found
  | _, _, _, .fvar found => .fvar found
  | _, _, _, .builtinAtom accepted => .builtinAtom (builtin_of_signature_inclusion types accepted)
  | _, _, _, .constructor member nonbare args =>
      .constructor (terms member) nonbare (args.of_signature_inclusion types terms)
  | _, _, _, .lambda body => .lambda (body.of_signature_inclusion types terms)
  | _, _, _, .multiLambda body => .multiLambda (body.of_signature_inclusion types terms)
  | _, _, _, .subst body replacement =>
      .subst (body.of_signature_inclusion types terms) (replacement.of_signature_inclusion types terms)
  | _, _, _, .collection elements => .collection (elements.of_signature_inclusion types terms)
  | _, _, _, .collectionConstructor member shape elements =>
      .collectionConstructor (terms member) shape (elements.of_signature_inclusion types terms)

theorem ArgumentsHaveTypes.of_signature_inclusion
    {source target : LanguageDef} {free : FreeTypeContext}
    (types : source.types ⊆ target.types) (terms : source.terms ⊆ target.terms) :
    ∀ {bound : List TypeExpr} {patterns : List Pattern} {params : List TermParam},
      ArgumentsHaveTypes source free bound patterns params →
        ArgumentsHaveTypes target free bound patterns params
  | _, _, _, .nil => .nil
  | _, _, _, .cons represents expected head tail =>
      .cons represents expected (head.of_signature_inclusion types terms)
        (tail.of_signature_inclusion types terms)

theorem ElementsHaveTypes.of_signature_inclusion
    {source target : LanguageDef} {free : FreeTypeContext}
    (types : source.types ⊆ target.types) (terms : source.terms ⊆ target.terms) :
    ∀ {bound : List TypeExpr} {patterns : List Pattern} {sort : TypeExpr},
      ElementsHaveTypes source free bound patterns sort →
        ElementsHaveTypes target free bound patterns sort
  | _, _, _, .nil => .nil
  | _, _, _, .cons head tail =>
      .cons (head.of_signature_inclusion types terms) (tail.of_signature_inclusion types terms)
end

end Mettapedia.GSLT.LanguageDef.CarrierWellSorted
