import Mettapedia.GSLT.LanguageDef.RestAwareTyping
import Mettapedia.GSLT.LanguageDef.TypedBoundSubstitution

/-!
# Bound-context substitution of rest-aware authored schemas

The collection rest is a named schema occurrence, not a de Bruijn variable.
Bound substitution acts on elements and constructor arguments while retaining
the rest's declared collection type. This extends the ordinary typed law to
the stronger schema judgment rather than inferring rest typing by forgetting
to the object-term relation.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

set_option autoImplicit false

private theorem getElem?_insert
    {inner outer inserted : List TypeExpr} {index : Nat} {type : TypeExpr}
    (lookup : (inner ++ outer)[index]? = some type) :
    ((inner ++ inserted) ++ outer)[if index ≥ inner.length then
      index + inserted.length else index]? = some type := by
  induction inner generalizing index with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.zero_le, ↓reduceIte]
      rw [List.getElem?_append_right]
      · simpa using lookup
      · omega
  | cons head inner inductionHypothesis =>
      cases index with
      | zero => simpa using lookup
      | succ index =>
          simp only [List.cons_append, List.getElem?_cons_succ] at lookup ⊢
          have shifted := inductionHypothesis lookup
          by_cases beyond : index ≥ inner.length
          · have beyond' : Nat.succ index ≥ (head :: inner).length := by
              simp only [List.length_cons]
              omega
            simp only [beyond, beyond', if_pos] at shifted ⊢
            simpa [Nat.succ_add] using shifted
          · have within' : ¬ Nat.succ index ≥ (head :: inner).length := by
              simp only [List.length_cons]
              omega
            simp only [beyond, within'] at shifted ⊢
            exact shifted

private theorem matchesParameterRepresentation_liftBVars
    (parameter : TermParam) (pattern : Pattern) (cutoff shift : Nat) :
    MatchesParameterRepresentation parameter pattern →
      MatchesParameterRepresentation parameter
        (liftBVars cutoff shift pattern) := by
  cases parameter with
  | simple => exact fun _ => trivial
  | abstractionNamed binderName bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation, liftBVars,
          liftBVarsList_eq_map]
      case lambda binder body => cases binder <;> simp
  | multiAbstractionNamed binderNames bodyName type =>
      cases pattern <;>
        simp [MatchesParameterRepresentation, liftBVars,
          liftBVarsList_eq_map]
      case multiLambda arity binders body => cases binders <;> simp

mutual
  /-- Insert a block of binder types while retaining every rest annotation's
  typing condition. -/
  theorem HasType.liftBVars_insert
      {language : LanguageDef} {free : FreeTypeContext}
      {inner outer inserted : List TypeExpr} {pattern : Pattern}
      {type : TypeExpr}
      (typed : HasType language free (inner ++ outer) pattern type) :
      HasType language free ((inner ++ inserted) ++ outer)
        (liftBVars inner.length inserted.length pattern) type := by
    cases typed with
    | @bvar _ index type lookup =>
        by_cases beyond : index ≥ inner.length
        · simpa [liftBVars, liftBVarsList_eq_map, beyond] using
            (HasType.bvar (free := free)
              (getElem?_insert (inserted := inserted) lookup))
        · simpa [liftBVars, liftBVarsList_eq_map, beyond] using
            (HasType.bvar (free := free)
              (getElem?_insert (inserted := inserted) lookup))
    | @fvar _ name type lookup =>
        simpa only [liftBVars, liftBVarsList_eq_map] using
          (HasType.fvar
            (bound := (inner ++ inserted) ++ outer) lookup)
    | @constructor _ rule arguments membership notBare argumentsTyped =>
        simpa only [liftBVars, liftBVarsList_eq_map] using
          (HasType.constructor membership notBare
            (argumentsTyped.liftBVars_insert
              (inner := inner) (outer := outer) (inserted := inserted)))
    | @lambda _ binder body domain codomain bodyTyped =>
        have liftedBody := bodyTyped.liftBVars_insert
          (inner := domain :: inner) (outer := outer)
          (inserted := inserted)
        have liftedBody' : HasType language free
            (domain :: ((inner ++ inserted) ++ outer))
            (liftBVars (inner.length + 1) inserted.length body)
            codomain := by
          simpa only [List.cons_append, List.length_cons, Nat.add_comm]
            using liftedBody
        simpa only [liftBVars, liftBVarsList_eq_map] using
          HasType.lambda (binder := binder) liftedBody'
    | @multiLambda _ arity binders body domain codomain bodyTyped =>
        have bodyTyped' : HasType language free
            ((List.replicate arity domain ++ inner) ++ outer) body
            codomain := by
          simpa only [List.append_assoc] using bodyTyped
        have liftedBody := bodyTyped'.liftBVars_insert
          (inner := List.replicate arity domain ++ inner)
          (outer := outer) (inserted := inserted)
        have liftedBody' : HasType language free
            (List.replicate arity domain ++ ((inner ++ inserted) ++ outer))
            (liftBVars (inner.length + arity) inserted.length body)
            codomain := by
          simpa only [List.append_assoc, List.length_append,
            List.length_replicate, Nat.add_comm] using liftedBody
        simpa only [liftBVars, liftBVarsList_eq_map] using
          HasType.multiLambda (binders := binders) liftedBody'
    | @subst _ body replacement domain codomain bodyTyped replacementTyped =>
        have liftedBody := bodyTyped.liftBVars_insert
          (inner := domain :: inner) (outer := outer)
          (inserted := inserted)
        have liftedReplacement := replacementTyped.liftBVars_insert
          (inner := inner) (outer := outer) (inserted := inserted)
        have liftedBody' : HasType language free
            (domain :: ((inner ++ inserted) ++ outer))
            (liftBVars (inner.length + 1) inserted.length body) type := by
          simpa only [List.cons_append, List.length_cons, Nat.add_comm]
            using liftedBody
        simpa only [liftBVars, liftBVarsList_eq_map] using
          HasType.subst liftedBody' liftedReplacement
    | @collection _ kind elements rest elementType elementsTyped restTyped =>
        simpa only [liftBVars, liftBVarsList_eq_map] using
          (HasType.collection (rest := rest)
            (elementsTyped.liftBVars_insert
              (inner := inner) (outer := outer) (inserted := inserted))
            restTyped)
    | @collectionConstructor _ rule parameterName kind elements rest
        elementType membership parameterShape elementsTyped restTyped =>
        simpa only [liftBVars, liftBVarsList_eq_map] using
          (HasType.collectionConstructor membership parameterShape
            (elementsTyped.liftBVars_insert
              (inner := inner) (outer := outer) (inserted := inserted))
            restTyped)

  theorem ArgumentsHaveTypes.liftBVars_insert
      {language : LanguageDef} {free : FreeTypeContext}
      {inner outer inserted : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free (inner ++ outer)
        arguments parameters) :
      ArgumentsHaveTypes language free ((inner ++ inserted) ++ outer)
        (arguments.map (liftBVars inner.length inserted.length))
        parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation parameterType argumentTyped argumentsTyped =>
        exact .cons
          (matchesParameterRepresentation_liftBVars _ _ _ _ representation)
          parameterType
          (argumentTyped.liftBVars_insert
            (inner := inner) (outer := outer) (inserted := inserted))
          (argumentsTyped.liftBVars_insert
            (inner := inner) (outer := outer) (inserted := inserted))

  theorem ElementsHaveType.liftBVars_insert
      {language : LanguageDef} {free : FreeTypeContext}
      {inner outer inserted : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType language free (inner ++ outer)
        elements elementType) :
      ElementsHaveType language free ((inner ++ inserted) ++ outer)
        (elements.map (liftBVars inner.length inserted.length))
        elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (elementTyped.liftBVars_insert
            (inner := inner) (outer := outer) (inserted := inserted))
          (elementsTyped.liftBVars_insert
            (inner := inner) (outer := outer) (inserted := inserted))
end

/-- A bound assignment whose images satisfy the stronger schema judgment,
including all collection-rest declarations inside the images. -/
structure TypedBoundAssignment (language : LanguageDef)
    (free : FreeTypeContext) (source target : List TypeExpr) where
  assignment : Nat → Pattern
  typed : ∀ {index type}, source[index]? = some type →
    HasType language free target (assignment index) type

namespace TypedBoundAssignment

def lift {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr}
    (assignment : TypedBoundAssignment language free source target)
    (arity : Nat) (binderType : TypeExpr) :
    TypedBoundAssignment language free
      (List.replicate arity binderType ++ source)
      (List.replicate arity binderType ++ target) where
  assignment := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
    arity assignment.assignment
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
      simpa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift, fresh] using
        (HasType.bvar (free := free) targetLookup)
    · have sourceLookup : source[index - arity]? = some type := by
        rw [List.getElem?_append_right
          (by simpa using Nat.le_of_not_gt fresh)] at lookup
        simpa using lookup
      have lifted := (assignment.typed sourceLookup).liftBVars_insert
        (inner := []) (outer := target)
        (inserted := List.replicate arity binderType)
      simpa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift, fresh]
        using lifted

/-- Forgetting a schema-typed assignment yields an ordinary typed assignment
with precisely the same operational substitution function. -/
def forget {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr}
    (assignment : TypedBoundAssignment language free source target) :
    WellSorted.TypedBoundAssignment language free source target where
  assignment := assignment.assignment
  typed := fun lookup => (assignment.typed lookup).forget

end TypedBoundAssignment

mutual
  /-- The actual simultaneous bound substitution preserves rest-aware
  authored typing, including nested collection-rest occurrences. -/
  theorem HasType.substituteBound
      {language : LanguageDef} {free : FreeTypeContext}
      {source target : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (assignment : TypedBoundAssignment language free source target)
      (typed : HasType language free source pattern type) :
      HasType language free target
        (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
          assignment.assignment pattern) type := by
    cases typed with
    | bvar lookup => exact assignment.typed lookup
    | fvar lookup =>
        simpa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute] using
          (HasType.fvar (bound := target) lookup)
    | constructor membership shape arguments =>
        simpa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute] using
          (HasType.constructor membership shape
            (arguments.substituteBound assignment))
    | lambda body =>
        have substituted := body.substituteBound (assignment.lift 1 _)
        simpa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
          TypedBoundAssignment.lift] using HasType.lambda substituted
    | multiLambda body =>
        have substituted := body.substituteBound (assignment.lift _ _)
        simpa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
          TypedBoundAssignment.lift] using HasType.multiLambda substituted
    | subst body replacement =>
        have substitutedBody := body.substituteBound (assignment.lift 1 _)
        have substitutedReplacement := replacement.substituteBound assignment
        simpa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
          TypedBoundAssignment.lift] using
          HasType.subst substitutedBody substitutedReplacement
    | collection elements restTyped =>
        simpa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
          Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map]
          using (HasType.collection
            (elements.substituteBound assignment) restTyped)
    | collectionConstructor membership shape elements restTyped =>
        simpa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
          Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map]
          using (HasType.collectionConstructor membership shape
            (elements.substituteBound assignment) restTyped)

  theorem ArgumentsHaveTypes.substituteBound
      {language : LanguageDef} {free : FreeTypeContext}
      {source target : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (assignment : TypedBoundAssignment language free source target)
      (typed : ArgumentsHaveTypes language free source arguments parameters) :
      ArgumentsHaveTypes language free target
        (arguments.map
          (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
            assignment.assignment)) parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation expected argument rest =>
        exact .cons
          (WellSorted.matchesParameterRepresentation_substituteBound
            _ _ _ representation)
          expected (argument.substituteBound assignment)
          (rest.substituteBound assignment)

  theorem ElementsHaveType.substituteBound
      {language : LanguageDef} {free : FreeTypeContext}
      {source target : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (assignment : TypedBoundAssignment language free source target)
      (typed : ElementsHaveType language free source elements elementType) :
      ElementsHaveType language free target
        (elements.map
          (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
            assignment.assignment)) elementType := by
    cases typed with
    | nil => exact .nil _ _
    | cons element rest =>
        exact .cons (element.substituteBound assignment)
          (rest.substituteBound assignment)
end

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
