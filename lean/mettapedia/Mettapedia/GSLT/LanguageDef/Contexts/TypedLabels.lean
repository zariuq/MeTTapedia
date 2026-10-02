import Mettapedia.GSLT.LanguageDef.Contexts.Presented
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceReplacement
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping

/-!
# Labels from occurrences

A subterm occurrence in a well-sorted term is a way of cutting the term in
two: the one-hole context around the occurrence and the subterm.  The typing
derivation of the term descends along the context to the occurrence and
records the type and the binders in scope there.

That descent is carried along every map of declarations, and replacing the
subterm by any term of the same type and scope keeps the term well-sorted.
So the context of the occurrence is a label of the presentation, from the
interface of the occurrence to the interface of the term: the observers of a
term are the contexts one can place around it.

The subterm is required to be a constructor application.  A binder node
occupies an abstraction position, and a term of the same type need not be a
binder node.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- A constructor application can be replaced by any pattern without changing
the representation class of the patterns around it. -/
theorem representationCompatible_of_apply (label : String) (arguments : List Pattern)
    (target : Pattern) : RepresentationCompatible (.apply label arguments) target := by
  intro context parameter represented
  cases context with
  | hole => cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | apply _ _ _ _ =>
      cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | lambda binder _ =>
      cases binder <;> cases parameter <;>
        simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | multiLambda _ binders _ =>
      cases binders <;> cases parameter <;>
        simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | substBody _ _ =>
      cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | substReplacement _ _ =>
      cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]
  | collection _ _ _ _ _ =>
      cases parameter <;> simp_all [MatchesParameterRepresentation, OneHoleContext.fill]

/-- **Typing descent is carried along a map of declarations.** -/
theorem TypedAt.map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) {free : FreeTypeContext} {focus : Pattern}
    {context : OneHoleContext} {bound focusBound : List TypeExpr} {type result : TypeExpr}
    (selected : TypedAt source.language free focus context bound type focusBound result) :
    TypedAt target.language (free.map morphism.symbols) (mapPattern morphism.symbols focus)
      (CIGSLT.mapOneHoleContext morphism.symbols context)
      (bound.map (mapTypeExpr morphism.symbols)) (mapTypeExpr morphism.symbols type)
      (focusBound.map (mapTypeExpr morphism.symbols))
      (mapTypeExpr morphism.symbols result) := by
  induction selected with
  | here typed => exact .here (typed.map morphism)
  | @application rule before after inner bound focusBound expected result beforeParams
      afterParams parameter membership ordinary arguments shape length parameterType _ recurse =>
      have mappedArguments := arguments.map morphism
      rw [List.map_append, List.map_cons, ← CIGSLT.mapOneHoleContext_fill] at mappedArguments
      exact TypedAt.application (rule := mapGrammarRule morphism.symbols rule)
        (beforeParams := beforeParams.map (mapTermParam morphism.symbols))
        (afterParams := afterParams.map (mapTermParam morphism.symbols))
        (parameter := mapTermParam morphism.symbols parameter)
        (morphism.mapsTerms rule membership)
        (fun bare => ordinary ((usesBareCollection_mapGrammarRule_iff _ _).mp bare))
        mappedArguments
        (by simp [mapGrammarRule, shape])
        (by simp [length])
        (by simp [parameterType])
        recurse
  | lambda _ recurse => exact .lambda recurse
  | @multiLambda arity binders inner bound focusBound domain codomain result _ recurse =>
      rw [List.map_append, List.map_replicate] at recurse
      exact .multiLambda recurse
  | substBody replacement _ recurse => exact .substBody (replacement.map morphism) recurse
  | substReplacement body _ recurse => exact .substReplacement (body.map morphism) recurse
  | @collection kind before after inner rest bound focusBound element result elements _ recurse =>
      have mappedElements := elements.map morphism
      rw [List.map_append, List.map_cons, ← CIGSLT.mapOneHoleContext_fill] at mappedElements
      exact .collection mappedElements recurse
  | @collectionConstructor rule parameter kind before after inner rest bound focusBound element
      result membership shape elements _ recurse =>
      have mappedElements := elements.map morphism
      rw [List.map_append, List.map_cons, ← CIGSLT.mapOneHoleContext_fill] at mappedElements
      exact TypedAt.collectionConstructor (rule := mapGrammarRule morphism.symbols rule)
        (parameter := parameter)
        (morphism.mapsTerms rule membership)
        (by simp [mapGrammarRule, shape, mapTermParam, mapTypeExpr])
        mappedElements recurse

end Mettapedia.GSLT.LanguageDef.WellSorted

namespace Mettapedia.GSLT.LanguageDef.Contexts

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

variable {presentation : ValidatedLanguageDef}

/-- **The context of an occurrence is a label.**  When a constructor
application occurs in a well-sorted term, the context around the occurrence
is a label from the interface of the occurrence to the interface of the
term. -/
def labelOfOccurrence {source target : Interface} (context : OneHoleContext)
    {label : String} {arguments : List Pattern}
    (selected : TypedAt presentation.language FreeTypeContext.empty (.apply label arguments)
      context target.stage target.type source.stage source.type)
    (canonical : (context.fill (.apply label arguments)).hasCanonicalBinderMetadata = true)
    (object : isObjectPattern (context.fill (.apply label arguments)) = true) :
    Context presentation (fun _ : Unit => source) target :=
  labelOfOneHole context (fun {extension} morphism term => by
    have mapped := selected.map morphism
    rw [FreeTypeContext.map_empty] at mapped
    have typed : HasType extension.language FreeTypeContext.empty
        (target.map morphism.symbols).stage
        ((CIGSLT.mapOneHoleContext morphism.symbols context).fill term.1)
        (target.map morphism.symbols).type := by
      refine mapped.replace ?_ term.2.1
      simp only [mapPattern]
      exact representationCompatible_of_apply _ _ _
    refine ⟨typed, ?_, ?_, ?_⟩
    · refine hasCanonicalBinderMetadata_fill_replace
        (original := mapPattern morphism.symbols (.apply label arguments)) _ ?_
        (fun _ => term.2.2.1)
      rw [CIGSLT.mapOneHoleContext_fill]
      simpa using canonical
    · refine isObjectPattern_fill_replace
        (original := mapPattern morphism.symbols (.apply label arguments)) _ ?_
        (fun _ => term.2.2.2.1)
      rw [CIGSLT.mapOneHoleContext_fill]
      simpa using object
    · simpa [ScopeSafeAt] using typed.isWellScopedAt)

/-- Placing a term in the label of an occurrence plugs it into the context of
the occurrence. -/
theorem apply_labelOfOccurrence (base : BasePremiseEvaluator)
    {source target : Interface} (context : OneHoleContext)
    {label : String} {arguments : List Pattern}
    (selected : TypedAt presentation.language FreeTypeContext.empty (.apply label arguments)
      context target.stage target.type source.stage source.type)
    (canonical : (context.fill (.apply label arguments)).hasCanonicalBinderMetadata = true)
    (object : isObjectPattern (context.fill (.apply label arguments)) = true)
    (term : Term presentation.language source) :
    ((contextTheory base presentation).apply
      (labelOfOccurrence context selected canonical object) term).1 = context.fill term.1 :=
  MultiHoleContext.fill_ofOneHole _ context

end Mettapedia.GSLT.LanguageDef.Contexts
