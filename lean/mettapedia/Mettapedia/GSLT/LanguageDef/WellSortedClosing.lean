import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Closing a typed free name in an authored language

Closing a free name appends its type outside the current bound context.
Existing bound indices remain unchanged; the closed name points to that new
outer binder. The result holds for every authored signature, constructor
spine and collection, with the original binding-parameter representation.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- Closing changes variable incidence, while preserving binder-node shapes. -/
theorem matchesParameterRepresentation_closeFVar_iff
    (parameter : TermParam) (pattern : Pattern) (index : Nat) (name : String) :
    MatchesParameterRepresentation parameter (closeFVar index name pattern) ↔
      MatchesParameterRepresentation parameter pattern := by
  cases parameter with
  | simple => simp [MatchesParameterRepresentation]
  | abstractionNamed =>
      cases pattern <;> simp only [closeFVar] <;> try rfl
      case fvar => split_ifs <;> rfl
      case lambda binder body => cases binder <;> simp only [MatchesParameterRepresentation]
  | multiAbstractionNamed =>
      cases pattern <;> simp only [closeFVar] <;> try rfl
      case fvar => split_ifs <;> rfl
      case multiLambda arity binders body => cases binders <;> simp only [MatchesParameterRepresentation]

mutual
  /-- A typed name can be closed into one additional outer binder. -/
  theorem HasType.closeFVar
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type)
      (name : String) (binderType : TypeExpr)
      (lookup : free name = some binderType) :
      HasType language free (bound ++ [binderType])
        (closeFVar bound.length name pattern) type := by
    cases typed with
    | @bvar bound index type present =>
        have lt : index < bound.length := (List.getElem?_eq_some_iff.mp present).choose
        simp only [closeFVar]
        exact .bvar (by rw [List.getElem?_append_left lt]; exact present)
    | @fvar bound actualName type present =>
        by_cases same : actualName = name
        · subst actualName
          have types : type = binderType := Option.some.inj (present.symm.trans lookup)
          subst type
          simp only [closeFVar, beq_self_eq_true, if_true]
          exact .bvar (by simp)
        · simp only [closeFVar, beq_eq_false_iff_ne.mpr same]
          exact .fvar present
    | @constructor bound rule arguments member notBare argumentsTyped =>
        simpa only [closeFVar] using
          HasType.constructor member notBare (argumentsTyped.closeFVar name binderType lookup)
    | @lambda bound binder body domain codomain bodyTyped =>
        have closedBody : HasType language free (domain :: (bound ++ [binderType]))
            (closeFVar (bound.length + 1) name body) codomain := by
          simpa only [List.cons_append, List.length_cons] using
            bodyTyped.closeFVar name binderType lookup
        simpa only [closeFVar] using HasType.lambda closedBody
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
        have closedBody : HasType language free
            (List.replicate arity domain ++ (bound ++ [binderType]))
            (closeFVar (bound.length + arity) name body) codomain := by
          simpa only [List.append_assoc, List.length_append,
            List.length_replicate, Nat.add_comm] using
            bodyTyped.closeFVar name binderType lookup
        simpa only [closeFVar] using HasType.multiLambda closedBody
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
        have closedBody : HasType language free (domain :: (bound ++ [binderType]))
            (closeFVar (bound.length + 1) name body) type := by
          simpa only [List.cons_append, List.length_cons] using
            bodyTyped.closeFVar name binderType lookup
        simpa only [closeFVar] using HasType.subst closedBody
            (replacementTyped.closeFVar name binderType lookup)
    | @collection bound collectionType elements rest elementType elementsTyped =>
        simpa only [closeFVar] using
          HasType.collection (elementsTyped.closeFVar name binderType lookup)
    | @collectionConstructor bound rule parameterName collectionType elements rest elementType member shape elementsTyped =>
        simpa only [closeFVar] using
          HasType.collectionConstructor member shape
            (elementsTyped.closeFVar name binderType lookup)

  /-- Closing preserves each constructor argument at its declared type. -/
  theorem ArgumentsHaveTypes.closeFVar
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {patterns : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound patterns parameters)
      (name : String) (binderType : TypeExpr)
      (lookup : free name = some binderType) :
      ArgumentsHaveTypes language free (bound ++ [binderType])
        (patterns.map (closeFVar bound.length name)) parameters := by
    cases typed with
    | nil => exact .nil
    | @cons bound argument arguments parameter parameters expected representation parameterType typed rest =>
        exact .cons
          ((matchesParameterRepresentation_closeFVar_iff _ _ _ _).mpr representation)
          parameterType (typed.closeFVar name binderType lookup)
          (rest.closeFVar name binderType lookup)

  /-- Closing preserves the element type of a collection spine. -/
  theorem ElementsHaveType.closeFVar
      {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {patterns : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType language free bound patterns type)
      (name : String) (binderType : TypeExpr)
      (lookup : free name = some binderType) :
      ElementsHaveType language free (bound ++ [binderType])
        (patterns.map (closeFVar bound.length name)) type := by
    cases typed with
    | nil => exact .nil _ _
    | @cons bound element elements elementType typed rest =>
        exact .cons (typed.closeFVar name binderType lookup)
          (rest.closeFVar name binderType lookup)
end
end Mettapedia.GSLT.LanguageDef.WellSorted
