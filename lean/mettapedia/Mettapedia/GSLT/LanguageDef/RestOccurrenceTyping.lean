import Mettapedia.GSLT.LanguageDef.RestAwareTyping
import Mettapedia.OSLF.MeTTaIL.RestOccurrenceAddress

/-!
# Typed contexts of authored collection rests

Rest-site addresses select collection nodes, not term holes. Descending a
rest-aware schema derivation through the decoded enclosing context retains
the collection's rest premise and the exact ordered binder-sort prefix.
-/

namespace Mettapedia.GSLT.LanguageDef.RestAwareTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress
open Mettapedia.OSLF.MeTTaIL.RestOccurrenceAddress

set_option autoImplicit false

theorem ArgumentsHaveTypes.append_cons_split
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} :
    ∀ {before : List Pattern} {middle : Pattern} {after : List Pattern}
      {parameters : List TermParam},
      ArgumentsHaveTypes language free bound (before ++ middle :: after)
        parameters →
      ∃ beforeParameters parameter afterParameters expected,
        parameters = beforeParameters ++ parameter :: afterParameters ∧
        beforeParameters.length = before.length ∧
        ArgumentsHaveTypes language free bound before beforeParameters ∧
        MatchesParameterRepresentation parameter middle ∧
        parameterType? parameter = some expected ∧
        HasType language free bound middle expected ∧
        ArgumentsHaveTypes language free bound after afterParameters
  | [], middle, after, parameters, typed => by
      cases typed with
      | cons representation parameterType middleTyped afterTyped =>
          exact ⟨[], _, _, _, rfl, rfl, .nil, representation, parameterType,
            middleTyped, afterTyped⟩
  | head :: tail, middle, after, parameters, typed => by
      cases typed with
      | cons representation parameterType headTyped tailTyped =>
          obtain ⟨beforeParameters, parameter, afterParameters, expected,
              parametersEq, lengthEq, beforeTyped, middleRepresentation,
              middleParameterType, middleTyped, afterTyped⟩ :=
            ArgumentsHaveTypes.append_cons_split tailTyped
          exact ⟨_ :: beforeParameters, parameter, afterParameters, expected,
            by simp [parametersEq], by simp [lengthEq],
            .cons representation parameterType headTyped beforeTyped,
            middleRepresentation, middleParameterType, middleTyped,
            afterTyped⟩

theorem ElementsHaveType.append_cons_split
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elementType : TypeExpr} :
    ∀ {before : List Pattern} {middle : Pattern} {after : List Pattern},
      ElementsHaveType language free bound (before ++ middle :: after)
        elementType →
      ElementsHaveType language free bound before elementType ∧
        HasType language free bound middle elementType ∧
        ElementsHaveType language free bound after elementType
  | [], middle, after, typed => by
      cases typed with
      | cons middleTyped afterTyped =>
          exact ⟨.nil bound elementType, middleTyped, afterTyped⟩
  | head :: tail, middle, after, typed => by
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨beforeTyped, middleTyped, afterTyped⟩ :=
            ElementsHaveType.append_cons_split tailTyped
          exact ⟨.cons headTyped beforeTyped, middleTyped, afterTyped⟩

/-- A rest-aware schema derivation descends along any existing one-hole
context, retaining the type of the focus and the ordered binder-sort prefix.
The collection-rest premises in both the focus and its siblings remain part
of the same derivation. -/
theorem HasType.focusAtContext
    {language : LanguageDef} {free : FreeTypeContext}
    {focus : Pattern} (context : OneHoleContext)
    {bound : List TypeExpr} {type : TypeExpr}
    (typed : HasType language free bound (context.fill focus) type) :
    ∃ focusBound focusType binderPrefix,
      HasType language free focusBound focus focusType ∧
      focusBound = binderPrefix ++ bound ∧
      binderPrefix.length = binderCount context := by
  induction context generalizing bound type with
  | hole =>
      exact ⟨bound, type, [], typed, rfl, rfl⟩
  | apply constructor before inner after inductionHypothesis =>
      cases typed with
      | constructor _ _ arguments =>
          obtain ⟨_, _, _, _, _, _, _, _, _, middle, _⟩ :=
            arguments.append_cons_split
          obtain ⟨focusBound, focusType, binderPrefix,
              focusTyped, prefixEq, prefixLength⟩ :=
            inductionHypothesis middle
          exact ⟨focusBound, focusType, binderPrefix,
            focusTyped, prefixEq, by simpa [binderCount] using prefixLength⟩
  | lambda binder inner inductionHypothesis =>
      cases typed with
      | @lambda bound binder body domain codomain bodyTyped =>
          obtain ⟨focusBound, focusType, binderPrefix,
              focusTyped, prefixEq, prefixLength⟩ :=
            inductionHypothesis bodyTyped
          refine ⟨focusBound, focusType, binderPrefix ++ [domain],
            focusTyped, ?_, ?_⟩
          · simpa [List.append_assoc] using prefixEq
          · simp [binderCount, List.length_append]
            omega
  | multiLambda arity binders inner inductionHypothesis =>
      cases typed with
      | @multiLambda bound arity binders body domain codomain bodyTyped =>
          obtain ⟨focusBound, focusType, binderPrefix,
              focusTyped, prefixEq, prefixLength⟩ :=
            inductionHypothesis bodyTyped
          refine ⟨focusBound, focusType,
            binderPrefix ++ List.replicate arity domain,
            focusTyped, ?_, ?_⟩
          · simpa [List.append_assoc] using prefixEq
          · simpa [binderCount, List.length_append,
              List.length_replicate, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using prefixLength
  | substBody inner replacement inductionHypothesis =>
      cases typed with
      | @subst bound body replacement domain codomain bodyTyped _ =>
          obtain ⟨focusBound, focusType, binderPrefix,
              focusTyped, prefixEq, prefixLength⟩ :=
            inductionHypothesis bodyTyped
          refine ⟨focusBound, focusType, binderPrefix ++ [domain],
            focusTyped, ?_, ?_⟩
          · simpa [List.append_assoc] using prefixEq
          · simp [binderCount, List.length_append]
            omega
  | substReplacement body inner inductionHypothesis =>
      cases typed with
      | subst _ replacementTyped =>
          obtain ⟨focusBound, focusType, binderPrefix,
              focusTyped, prefixEq, prefixLength⟩ :=
            inductionHypothesis replacementTyped
          exact ⟨focusBound, focusType, binderPrefix,
            focusTyped, prefixEq, by simpa [binderCount] using prefixLength⟩
  | collection kind before inner after rest inductionHypothesis =>
      cases typed with
      | collection elements _ =>
          obtain ⟨_, middle, _⟩ := elements.append_cons_split
          obtain ⟨focusBound, focusType, binderPrefix,
              focusTyped, prefixEq, prefixLength⟩ :=
            inductionHypothesis middle
          exact ⟨focusBound, focusType, binderPrefix,
            focusTyped, prefixEq, by simpa [binderCount] using prefixLength⟩
      | collectionConstructor _ _ elements _ =>
          obtain ⟨_, middle, _⟩ := elements.append_cons_split
          obtain ⟨focusBound, focusType, binderPrefix,
              focusTyped, prefixEq, prefixLength⟩ :=
            inductionHypothesis middle
          exact ⟨focusBound, focusType, binderPrefix,
            focusTyped, prefixEq, by simpa [binderCount] using prefixLength⟩

/-- A decoded collection-rest address in an authored schema has a rest-aware
typing derivation at its enclosing collection, the rest's exact collection
sort, and a binder-sort prefix agreeing with executable depth. -/
theorem HasType.restSiteAt
    {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {bound : List TypeExpr} {rootType : TypeExpr}
    (typed : HasType language free bound pattern rootType)
    {path : List Nat} {site : RestSite}
    (decoded : restSiteAt? pattern path = some site) :
    ∃ focusBound focusType binderPrefix elementType,
      HasType language free focusBound site.focus focusType ∧
      free site.name = some (.collection site.kind elementType) ∧
      focusBound = binderPrefix ++ bound ∧
      binderPrefix.length = binderCount site.context ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        pattern path 0 = some binderPrefix.length := by
  have sourceAtFocus : HasType language free bound
      (site.context.fill site.focus) rootType := by
    rw [restSiteAt?_fill decoded]
    exact typed
  obtain ⟨focusBound, focusType, binderPrefix,
      focusTyped, prefixEq, prefixLength⟩ :=
    sourceAtFocus.focusAtContext site.context
  have collectionTyped : HasType language free focusBound
      (.collection site.kind site.elements (some site.name)) focusType :=
    focusTyped
  obtain ⟨elementType, lookup⟩ := collectionTyped.restDeclared
  refine ⟨focusBound, focusType, binderPrefix, elementType,
    focusTyped, lookup, prefixEq, prefixLength, ?_⟩
  simpa [prefixLength] using restSiteAt?_depth decoded 0

/-- Computed rest name and binder depth can be refined to the complete
rest-aware collection derivation and the actual binder-sort prefix. -/
theorem HasType.restSiteAt_of_summary
    {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {bound : List TypeExpr} {rootType : TypeExpr}
    (typed : HasType language free bound pattern rootType)
    {path : List Nat} {name : String} {depth : Nat}
    (summary : (restSiteAt? pattern path).map
      (fun site => (site.name, binderCount site.context)) =
        some (name, depth)) :
    ∃ site focusBound focusType binderPrefix elementType,
      restSiteAt? pattern path = some site ∧
      site.name = name ∧
      HasType language free focusBound site.focus focusType ∧
      free name = some (.collection site.kind elementType) ∧
      focusBound = binderPrefix ++ bound ∧
      binderPrefix.length = depth ∧
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceDepthAt?
        pattern path 0 = some depth := by
  cases decoded : restSiteAt? pattern path with
  | none => simp [decoded] at summary
  | some site =>
      simp only [decoded, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at summary
      obtain ⟨nameEq, depthEq⟩ := summary
      obtain ⟨focusBound, focusType, binderPrefix, elementType,
          focusTyped, lookup, prefixEq, prefixLength,
          runtimeDepth⟩ := typed.restSiteAt decoded
      refine ⟨site, focusBound, focusType, binderPrefix, elementType,
        rfl, nameEq, focusTyped, ?_, prefixEq, ?_, ?_⟩
      · simpa [nameEq] using lookup
      · exact prefixLength.trans depthEq
      · simpa [prefixLength, depthEq] using runtimeDepth

end Mettapedia.GSLT.LanguageDef.RestAwareTyping
