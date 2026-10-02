import Mettapedia.GSLT.LanguageDef.ContextSubstitution

/-!
# Typed ambient context renaming

The existing ambient binder traversal preserves typing whenever its index map
preserves the types of available ambient variables. Local binder prefixes and
constructor parameter representations remain unchanged. Injectivity is not
needed for typing; insertion maps used by Cost satisfy the stronger property.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open ContextSubstitution
namespace WellSorted

/-- A type-preserving map of ambient binder positions. -/
def PreservesBoundTypes (source target : List TypeExpr) (rename : Nat → Nat) : Prop :=
  ∀ {index type}, source[index]? = some type → target[rename index]? = some type

theorem PreservesBoundTypes.id (bound : List TypeExpr) :
    PreservesBoundTypes bound bound id := fun lookup => lookup

theorem PreservesBoundTypes.comp
    {source middle target : List TypeExpr} {first second : Nat → Nat}
    (firstTyped : PreservesBoundTypes source middle first)
    (secondTyped : PreservesBoundTypes middle target second) :
    PreservesBoundTypes source target (second ∘ first) :=
  fun lookup => secondTyped (firstTyped lookup)

theorem PreservesBoundTypes.lookup_prefix
    {source target : List TypeExpr} {rename : Nat → Nat}
    (preserves : PreservesBoundTypes source target rename)
    (inner : List TypeExpr) {index : Nat} {type : TypeExpr}
    (lookup : (inner ++ source)[index]? = some type) :
    (inner ++ target)[if index < inner.length then index
      else inner.length + rename (index - inner.length)]? = some type := by
  by_cases inside : index < inner.length
  · simpa [inside, List.getElem?_append_left inside] using lookup
  · rw [if_neg inside, List.getElem?_append_right (by omega)]
    rw [List.getElem?_append_right (by omega)] at lookup
    simpa using preserves lookup

theorem MatchesParameterRepresentation.renameAmbientBVarsAt
    (rename : Nat → Nat) (depth : Nat) {parameter : TermParam} {pattern : Pattern}
    (representation : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (renameAmbientBVarsAt rename depth pattern) := by
  cases parameter with
  | simple => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;> simp_all [MatchesParameterRepresentation, ContextSubstitution.renameAmbientBVarsAt]
      case lambda binder body => cases binder <;> simp_all
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;> simp_all [MatchesParameterRepresentation, ContextSubstitution.renameAmbientBVarsAt]
      case multiLambda arity binders body => cases binders <;> simp_all

mutual
  /-- A typed ambient map acts on open terms beneath arbitrary local binders. -/
  theorem HasType.renameAmbientBVarsAt
      {language : LanguageDef} {free : FreeTypeContext}
      {source target inner : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free (inner ++ source) pattern type)
      (rename : Nat → Nat) (preserves : PreservesBoundTypes source target rename) :
      HasType language free (inner ++ target)
        (renameAmbientBVarsAt rename inner.length pattern) type := by
    cases typed with
    | @bvar _ index type lookup =>
        have result := HasType.bvar (language := language) (free := free) (preserves.lookup_prefix inner lookup)
        by_cases inside : index < inner.length <;>
          simpa [renameAmbientBVarsAt, inside] using result
    | fvar lookup =>
        simpa only [ContextSubstitution.renameAmbientBVarsAt] using
          (HasType.fvar (bound := inner ++ target) lookup)
    | constructor membership notBare argumentsTyped =>
        simpa only [ContextSubstitution.renameAmbientBVarsAt] using
          (HasType.constructor membership notBare
            (argumentsTyped.renameAmbientBVarsAt rename preserves))
    | @lambda _ binder body domain codomain bodyTyped =>
        simpa [renameAmbientBVarsAt] using
          (HasType.lambda (binder := binder)
            (bodyTyped.renameAmbientBVarsAt (inner := domain :: inner) rename preserves))
    | @multiLambda _ arity binders body domain codomain bodyTyped =>
        have bodyTyped' : HasType language free
            ((List.replicate arity domain ++ inner) ++ source) body codomain := by
          simpa only [List.append_assoc] using bodyTyped
        have result := bodyTyped'.renameAmbientBVarsAt rename preserves
        have bodyResult : HasType language free
            (List.replicate arity domain ++ (inner ++ target))
            (renameAmbientBVarsAt rename (inner.length + arity) body) codomain := by
          simpa [List.append_assoc, List.length_append, List.length_replicate,
            Nat.add_comm] using result
        simpa only [ContextSubstitution.renameAmbientBVarsAt] using
          (HasType.multiLambda (binders := binders) bodyResult)
    | @subst _ body replacement domain codomain bodyTyped replacementTyped =>
        simpa [renameAmbientBVarsAt] using
          (HasType.subst
            (bodyTyped.renameAmbientBVarsAt (inner := domain :: inner) rename preserves)
            (replacementTyped.renameAmbientBVarsAt rename preserves))
    | collection elementsTyped =>
        simpa only [ContextSubstitution.renameAmbientBVarsAt] using
          (HasType.collection (elementsTyped.renameAmbientBVarsAt rename preserves))
    | collectionConstructor membership shape elementsTyped =>
        simpa only [ContextSubstitution.renameAmbientBVarsAt] using
          (HasType.collectionConstructor membership shape
            (elementsTyped.renameAmbientBVarsAt rename preserves))

  /-- Parameter representation and ordered arguments survive ambient renaming. -/
  theorem ArgumentsHaveTypes.renameAmbientBVarsAt
      {language : LanguageDef} {free : FreeTypeContext}
      {source target inner : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free (inner ++ source) arguments parameters)
      (rename : Nat → Nat) (preserves : PreservesBoundTypes source target rename) :
      ArgumentsHaveTypes language free (inner ++ target)
        (arguments.map (renameAmbientBVarsAt rename inner.length)) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons (representation.renameAmbientBVarsAt rename inner.length) parameterType
          (argumentTyped.renameAmbientBVarsAt rename preserves)
          (argumentsTyped.renameAmbientBVarsAt rename preserves)

  /-- Collection positions and multiplicities survive ambient renaming. -/
  theorem ElementsHaveType.renameAmbientBVarsAt
      {language : LanguageDef} {free : FreeTypeContext}
      {source target inner : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType language free (inner ++ source) elements elementType)
      (rename : Nat → Nat) (preserves : PreservesBoundTypes source target rename) :
      ElementsHaveType language free (inner ++ target)
        (elements.map (renameAmbientBVarsAt rename inner.length)) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons (elementTyped.renameAmbientBVarsAt rename preserves)
          (elementsTyped.renameAmbientBVarsAt rename preserves)
end

end WellSorted
end Mettapedia.GSLT.LanguageDef
