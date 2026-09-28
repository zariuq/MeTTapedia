import Mettapedia.GSLT.LanguageDef.ContextSubstitution
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-!
# Authored typing for executable bound-context substitution

The operational occurrence substitution acts on de Bruijn context variables.
The existing `TypedAssignment` acts on named free variables, so it cannot
justify this execution step. Here a typed assignment follows the exact bound
contexts and the same substitution function used by the rule executor.
Collection rests remain schema names and are not changed by this action.
-/

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

set_option autoImplicit false

namespace RawSub
export Mettapedia.OSLF.MeTTaIL.ContextSubstitution
  (lift substitute substituteList_eq_map)
end RawSub

/-- A simultaneous de Bruijn assignment whose every image has the source
variable's declared type in the target bound context. -/
structure TypedBoundAssignment (language : LanguageDef)
    (free : FreeTypeContext) (source target : List TypeExpr) where
  assignment : Nat → Pattern
  typed : ∀ {index type}, source[index]? = some type →
    HasType language free target (assignment index) type

namespace TypedBoundAssignment

/-- Entering an authored binder fixes its new variables and weakens every
older assignment image below them. -/
def lift {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr}
    (assignment : TypedBoundAssignment language free source target)
    (arity : Nat) (binderType : TypeExpr) :
    TypedBoundAssignment language free
      (List.replicate arity binderType ++ source)
      (List.replicate arity binderType ++ target) where
  assignment := RawSub.lift arity assignment.assignment
  typed := by
    intro index type lookup
    by_cases fresh : index < arity
    · have sourceType : binderType = type := by
        rw [List.getElem?_append_left (by simpa using fresh),
          List.getElem?_replicate_of_lt fresh] at lookup
        exact Option.some.inj lookup
      subst type
      have targetLookup :
          (List.replicate arity binderType ++ target)[index]? =
            some binderType := by
        rw [List.getElem?_append_left (by simpa using fresh),
          List.getElem?_replicate_of_lt fresh]
      simpa [RawSub.lift, fresh] using
        (HasType.bvar (free := free) targetLookup)
    · have sourceLookup : source[index - arity]? = some type := by
        rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt fresh)]
          at lookup
        simpa using lookup
      have lifted := (assignment.typed sourceLookup).liftBVars_insert
        (inner := []) (outer := target)
        (inserted := List.replicate arity binderType)
      simpa [RawSub.lift, fresh] using lifted

/-- Extend a typed bound-variable assignment through a heterogeneous list of
premise-local binder sorts. The operational assignment is the same `lift`
used by the untyped scoped-premise action. -/
def liftContext {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr}
    (assignment : TypedBoundAssignment language free source target)
    (binders : List TypeExpr) :
    TypedBoundAssignment language free
      (binders ++ source) (binders ++ target) where
  assignment := RawSub.lift binders.length assignment.assignment
  typed := by
    intro index type lookup
    by_cases fresh : index < binders.length
    · have binderType : binders[index]? = some type := by
        simpa only [List.getElem?_append_left fresh] using lookup
      have targetLookup :
          (binders ++ target)[index]? = some type := by
        simpa only [List.getElem?_append_left fresh] using binderType
      simpa [RawSub.lift, fresh] using
        (HasType.bvar (free := free) targetLookup)
    · have sourceLookup : source[index - binders.length]? = some type := by
        rw [List.getElem?_append_right
          (by simpa using Nat.le_of_not_gt fresh)] at lookup
        simpa using lookup
      have shifted := (assignment.typed sourceLookup).liftBVars_insert
        (inner := []) (outer := target) (inserted := binders)
      simpa [RawSub.lift, fresh] using shifted

/-- Forgetting sorts from a typed bound assignment gives exactly the
scope-preserving raw assignment used by premise transport. -/
theorem wellScoped {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr}
    (assignment : TypedBoundAssignment language free source target) :
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.WellScopedAssignment
      source.length target.length assignment.assignment := by
  intro index inSource
  have lookup : source[index]? = some (source[index]'inSource) := by
    simp
  exact (assignment.typed lookup).isWellScopedAt

end TypedBoundAssignment

/-- Bound-context substitution retains the authored representation class
chosen for a constructor argument. -/
theorem matchesParameterRepresentation_substituteBound
    (parameter : TermParam) (pattern : Pattern)
    (assignment : Nat → Pattern) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter
        (RawSub.substitute assignment pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binder body type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation, RawSub.substitute]
      case lambda binderName body => cases binderName <;> simp
  | multiAbstractionNamed binders body type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation, RawSub.substitute]
      case multiLambda arity binderNames body => cases binderNames <;> simp

mutual
  /-- The executable simultaneous substitution preserves authored typing in
  every bound context, including nested lambda, multi-binder, explicit
  substitution, and collection nodes. -/
  theorem HasType.substituteBound
      {language : LanguageDef} {free : FreeTypeContext}
      {source target : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (assignment : TypedBoundAssignment language free source target)
      (typed : HasType language free source pattern type) :
      HasType language free target
        (RawSub.substitute assignment.assignment pattern) type := by
    cases typed with
    | bvar lookup => exact assignment.typed lookup
    | fvar lookup => simpa [RawSub.substitute] using
        (HasType.fvar (bound := target) lookup)
    | constructor membership shape arguments =>
        simpa [RawSub.substitute] using
          (HasType.constructor membership shape
            (arguments.substituteBound assignment))
    | lambda body =>
        have substituted := body.substituteBound (assignment.lift 1 _)
        simpa [RawSub.substitute, TypedBoundAssignment.lift] using
          HasType.lambda substituted
    | multiLambda body =>
        have substituted := body.substituteBound (assignment.lift _ _)
        simpa [RawSub.substitute, TypedBoundAssignment.lift] using
          HasType.multiLambda substituted
    | subst body replacement =>
        have substitutedBody := body.substituteBound (assignment.lift 1 _)
        have substitutedReplacement := replacement.substituteBound assignment
        simpa [RawSub.substitute, TypedBoundAssignment.lift] using
          HasType.subst substitutedBody substitutedReplacement
    | collection elements =>
        simpa [RawSub.substitute, RawSub.substituteList_eq_map] using
          (HasType.collection (elements.substituteBound assignment))
    | collectionConstructor membership shape elements =>
        simpa [RawSub.substitute, RawSub.substituteList_eq_map] using
          (HasType.collectionConstructor membership shape
            (elements.substituteBound assignment))

  theorem ArgumentsHaveTypes.substituteBound
      {language : LanguageDef} {free : FreeTypeContext}
      {source target : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (assignment : TypedBoundAssignment language free source target)
      (typed : ArgumentsHaveTypes language free source arguments parameters) :
      ArgumentsHaveTypes language free target
        (arguments.map (RawSub.substitute assignment.assignment))
        parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation expected argument rest =>
        exact .cons
          (matchesParameterRepresentation_substituteBound _ _ _ representation)
          expected
          (argument.substituteBound assignment)
          (rest.substituteBound assignment)

  theorem ElementsHaveType.substituteBound
      {language : LanguageDef} {free : FreeTypeContext}
      {source target : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (assignment : TypedBoundAssignment language free source target)
      (typed : ElementsHaveType language free source elements elementType) :
      ElementsHaveType language free target
        (elements.map (RawSub.substitute assignment.assignment))
        elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons element rest =>
        exact .cons (element.substituteBound assignment)
          (rest.substituteBound assignment)
end

end Mettapedia.GSLT.LanguageDef.WellSorted
