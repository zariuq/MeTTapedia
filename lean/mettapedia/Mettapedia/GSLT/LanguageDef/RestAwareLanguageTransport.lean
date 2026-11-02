import Mettapedia.GSLT.LanguageDef.RestAwareTyping

/-! Rest-aware schema typing depends on constructor declarations and the
caller contexts. Changes to operational rows preserve it when the grammar
vocabulary is exactly equal.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

mutual
theorem type_transport {first second : LanguageDef} (same : first.terms = second.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType first free bound pattern type) : HasType second free bound pattern type := by
  cases typed with
  | bvar found => exact .bvar found
  | fvar found => exact .fvar found
  | constructor declared ordinary arguments =>
      exact .constructor (same ▸ declared) ordinary (arguments_transport same arguments)
  | lambda body => exact .lambda (type_transport same body)
  | multiLambda body => exact .multiLambda (type_transport same body)
  | subst body replacement => exact .subst (type_transport same body) (type_transport same replacement)
  | collection elements rest => exact .collection (elements_transport same elements) rest
  | collectionConstructor declared representation elements rest =>
      exact .collectionConstructor (same ▸ declared) representation (elements_transport same elements) rest
termination_by sizeOf pattern

theorem arguments_transport {first second : LanguageDef} (same : first.terms = second.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {patterns : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes first free bound patterns parameters) :
    ArgumentsHaveTypes second free bound patterns parameters := by
  cases typed with
  | nil => exact .nil
  | cons representation expected head tail =>
      exact .cons representation expected (type_transport same head) (arguments_transport same tail)
termination_by sizeOf patterns

theorem elements_transport {first second : LanguageDef} (same : first.terms = second.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {patterns : List Pattern} {type : TypeExpr}
    (typed : ElementsHaveType first free bound patterns type) : ElementsHaveType second free bound patterns type := by
  cases typed with
  | nil => exact .nil _ _
  | cons head tail => exact .cons (type_transport same head) (elements_transport same tail)
termination_by sizeOf patterns
end

#print axioms type_transport

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
