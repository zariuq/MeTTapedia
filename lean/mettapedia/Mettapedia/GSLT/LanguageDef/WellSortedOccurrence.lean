import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion
import Mettapedia.GSLT.LanguageDef.SchemaTyping

/-!
# Typing retained along an existing occurrence zipper

`TypedAt` is a proof of typing descent along `OneHoleContext`, not a new
occurrence representation. It records the actual types crossed by each
binder and the exact authored parameter selected by each application frame.
Extraction uses one typing derivation, so it needs no determinism assumption.

This concerns ordinary term occurrences, including schema fvars. A collection
rest is not a term hole of `OneHoleContext`; no rest typing is inferred.
The existing raw typing judgment permits explicit substitutions and open
rests, and the theorem retains that boundary without strengthening admission.
An occurrence's ambient context is not a metavariable permission context.
-/

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

set_option autoImplicit false

/-- Typing descent indexed by the existing zipper. The final two indices are
the complete ambient context and result type at the selected occurrence. -/
inductive TypedAt (language : LanguageDef) (free : FreeTypeContext)
    (focus : Pattern) :
    OneHoleContext → List TypeExpr → TypeExpr → List TypeExpr → TypeExpr → Prop where
  | here {bound : List TypeExpr} {type : TypeExpr} :
      HasType language free bound focus type →
      TypedAt language free focus .hole bound type bound type
  | application {rule : GrammarRule} {before after : List Pattern}
      {inner : OneHoleContext} {bound focusBound : List TypeExpr}
      {expected result : TypeExpr} {beforeParams afterParams : List TermParam}
      {parameter : TermParam} :
      rule ∈ language.terms → ¬ UsesBareCollection rule →
      ArgumentsHaveTypes language free bound
        (before ++ inner.fill focus :: after) rule.params →
      rule.params = beforeParams ++ parameter :: afterParams →
      beforeParams.length = before.length →
      parameterType? parameter = some expected →
      TypedAt language free focus inner bound expected focusBound result →
      TypedAt language free focus (.apply rule.label before inner after)
        bound (.base rule.category) focusBound result
  | lambda {binder : Option String} {inner : OneHoleContext}
      {bound focusBound : List TypeExpr} {domain codomain result : TypeExpr} :
      TypedAt language free focus inner (domain :: bound) codomain focusBound result →
      TypedAt language free focus (.lambda binder inner) bound
        (.arrow domain codomain) focusBound result
  | multiLambda {arity : Nat} {binders : List String} {inner : OneHoleContext}
      {bound focusBound : List TypeExpr} {domain codomain result : TypeExpr} :
      TypedAt language free focus inner (List.replicate arity domain ++ bound)
        codomain focusBound result →
      TypedAt language free focus (.multiLambda arity binders inner) bound
        (.arrow (.multiBinder domain) codomain) focusBound result
  | substBody {inner : OneHoleContext} {replacement : Pattern}
      {bound focusBound : List TypeExpr} {domain codomain result : TypeExpr} :
      HasType language free bound replacement domain →
      TypedAt language free focus inner (domain :: bound) codomain focusBound result →
      TypedAt language free focus (.substBody inner replacement)
        bound codomain focusBound result
  | substReplacement {body : Pattern} {inner : OneHoleContext}
      {bound focusBound : List TypeExpr} {domain codomain result : TypeExpr} :
      HasType language free (domain :: bound) body codomain →
      TypedAt language free focus inner bound domain focusBound result →
      TypedAt language free focus (.substReplacement body inner)
        bound codomain focusBound result
  | collection {kind : CollType} {before after : List Pattern}
      {inner : OneHoleContext} {rest : Option String}
      {bound focusBound : List TypeExpr} {element result : TypeExpr} :
      ElementsHaveType language free bound
        (before ++ inner.fill focus :: after) element →
      TypedAt language free focus inner bound element focusBound result →
      TypedAt language free focus (.collection kind before inner after rest)
        bound (.collection kind element) focusBound result
  | collectionConstructor {rule : GrammarRule} {parameter : String}
      {kind : CollType} {before after : List Pattern}
      {inner : OneHoleContext} {rest : Option String}
      {bound focusBound : List TypeExpr} {element result : TypeExpr} :
      rule ∈ language.terms →
      rule.params = [.simple parameter (.collection kind element)] →
      ElementsHaveType language free bound
        (before ++ inner.fill focus :: after) element →
      TypedAt language free focus inner bound element focusBound result →
      TypedAt language free focus (.collection kind before inner after rest)
        bound (.base rule.category) focusBound result

namespace TypedAt

/-- At the hole itself the retained indices are exactly the current indices. -/
theorem hole_indices {language : LanguageDef} {free : FreeTypeContext}
    {focus : Pattern} {bound focusBound : List TypeExpr} {type result : TypeExpr}
    (selected : TypedAt language free focus .hole bound type focusBound result) :
    focusBound = bound ∧ result = type := by
  cases selected
  exact ⟨rfl, rfl⟩

theorem focus_typed {language : LanguageDef} {free : FreeTypeContext}
    {focus : Pattern} {context : OneHoleContext} {bound focusBound : List TypeExpr}
    {type result : TypeExpr}
    (selected : TypedAt language free focus context bound type focusBound result) :
    HasType language free focusBound focus result := by
  induction selected <;> assumption

theorem source_typed {language : LanguageDef} {free : FreeTypeContext}
    {focus : Pattern} {context : OneHoleContext} {bound focusBound : List TypeExpr}
    {type result : TypeExpr}
    (selected : TypedAt language free focus context bound type focusBound result) :
    HasType language free bound (context.fill focus) type := by
  induction selected with
  | here typed => exact typed
  | application membership ordinary arguments _ _ _ _ _ =>
      exact .constructor membership ordinary arguments
  | lambda _ inductionHypothesis => exact .lambda inductionHypothesis
  | multiLambda _ inductionHypothesis => exact .multiLambda inductionHypothesis
  | substBody replacement _ inductionHypothesis =>
      exact .subst inductionHypothesis replacement
  | substReplacement body _ inductionHypothesis => exact .subst body inductionHypothesis
  | collection elements _ _ => exact .collection elements
  | collectionConstructor membership shape elements _ _ =>
      exact .collectionConstructor membership shape elements

/-- At a selected fvar, its result type is precisely the authored lookup.
Nothing here assigns a dependency arity to that variable. -/
theorem fvar_lookup {language : LanguageDef} {free : FreeTypeContext}
    {name : String} {context : OneHoleContext} {bound focusBound : List TypeExpr}
    {type result : TypeExpr}
    (selected : TypedAt language free (.fvar name) context bound type focusBound result) :
    free name = some result := by
  cases selected.focus_typed with
  | fvar lookup => exact lookup

/-- Descent adds an exact binder prefix; it never discards or rearranges the
ambient context in which the source derivation was checked. -/
theorem ambient_suffix {language : LanguageDef} {free : FreeTypeContext}
    {focus : Pattern} {context : OneHoleContext} {bound focusBound : List TypeExpr}
    {type result : TypeExpr}
    (selected : TypedAt language free focus context bound type focusBound result) :
    ∃ binderPrefix, focusBound = binderPrefix ++ bound := by
  induction selected with
  | here _ => exact ⟨[], rfl⟩
  | application _ _ _ _ _ _ _ inductionHypothesis => exact inductionHypothesis
  | @lambda binder inner bound focusBound domain codomain result _ inductionHypothesis =>
      obtain ⟨binderPrefix, equality⟩ := inductionHypothesis
      exact ⟨binderPrefix ++ [domain], by simpa [List.append_assoc] using equality⟩
  | @multiLambda arity binders inner bound focusBound domain codomain result _ inductionHypothesis =>
      obtain ⟨binderPrefix, equality⟩ := inductionHypothesis
      exact ⟨binderPrefix ++ List.replicate arity domain,
        by simpa [List.append_assoc] using equality⟩
  | @substBody inner replacement bound focusBound domain codomain result _ _ inductionHypothesis =>
      obtain ⟨binderPrefix, equality⟩ := inductionHypothesis
      exact ⟨binderPrefix ++ [domain], by simpa [List.append_assoc] using equality⟩
  | substReplacement _ _ inductionHypothesis => exact inductionHypothesis
  | collection _ _ inductionHypothesis => exact inductionHypothesis
  | collectionConstructor _ _ _ _ inductionHypothesis => exact inductionHypothesis

/-- Descent composes along the existing zipper composition. The intermediate
context and type must match, so plugging paths cannot silently change scope. -/
theorem comp {language : LanguageDef} {free : FreeTypeContext}
    {focus : Pattern} {outer inner : OneHoleContext}
    {bound middleBound focusBound : List TypeExpr}
    {type middleType result : TypeExpr}
    (outerTyped : TypedAt language free (inner.fill focus) outer
      bound type middleBound middleType)
    (innerTyped : TypedAt language free focus inner middleBound middleType
      focusBound result) :
    TypedAt language free focus (outer.comp inner) bound type focusBound result := by
  induction outerTyped with
  | here _ => exact innerTyped
  | application membership ordinary arguments shape length expected _ inductionHypothesis =>
      apply TypedAt.application membership ordinary
      · simpa only [OneHoleContext.fill_comp] using arguments
      · exact shape
      · exact length
      · exact expected
      · exact inductionHypothesis innerTyped
  | lambda _ inductionHypothesis => exact .lambda (inductionHypothesis innerTyped)
  | multiLambda _ inductionHypothesis => exact .multiLambda (inductionHypothesis innerTyped)
  | substBody replacement _ inductionHypothesis =>
      exact .substBody replacement (inductionHypothesis innerTyped)
  | substReplacement body _ inductionHypothesis =>
      exact .substReplacement body (inductionHypothesis innerTyped)
  | collection elements _ inductionHypothesis =>
      apply TypedAt.collection
      · simpa only [OneHoleContext.fill_comp] using elements
      · exact inductionHypothesis innerTyped
  | collectionConstructor membership shape elements _ inductionHypothesis =>
      apply TypedAt.collectionConstructor membership shape
      · simpa only [OneHoleContext.fill_comp] using elements
      · exact inductionHypothesis innerTyped

end TypedAt

/-- Every selected ordinary occurrence in an actual typing derivation has a
coherent typing descent. No collection-choice or label determinism is needed:
the chosen derivation already identifies the declaration being used. -/
theorem hasType_typedAt {language : LanguageDef} {free : FreeTypeContext}
    (context : OneHoleContext) {focus : Pattern} {bound : List TypeExpr}
    {type : TypeExpr}
    (typed : HasType language free bound (context.fill focus) type) :
    ∃ focusBound result, TypedAt language free focus context bound type focusBound result := by
  induction context generalizing bound type with
  | hole => exact ⟨bound, type, .here typed⟩
  | apply constructor before inner after inductionHypothesis =>
      cases typed with
      | constructor membership ordinary arguments =>
          obtain ⟨beforeParams, parameter, afterParams, expected, shape, length,
              _, _, expectedType, middle, _⟩ := arguments.append_cons_split
          obtain ⟨focusBound, result, selected⟩ := inductionHypothesis middle
          exact ⟨focusBound, result, .application membership ordinary arguments
            shape length expectedType selected⟩
  | lambda binder inner inductionHypothesis =>
      cases typed with
      | lambda body =>
          obtain ⟨focusBound, result, selected⟩ := inductionHypothesis body
          exact ⟨focusBound, result, .lambda selected⟩
  | multiLambda arity binders inner inductionHypothesis =>
      cases typed with
      | multiLambda body =>
          obtain ⟨focusBound, result, selected⟩ := inductionHypothesis body
          exact ⟨focusBound, result, .multiLambda selected⟩
  | substBody inner replacement inductionHypothesis =>
      cases typed with
      | subst body replacementTyped =>
          obtain ⟨focusBound, result, selected⟩ := inductionHypothesis body
          exact ⟨focusBound, result, .substBody replacementTyped selected⟩
  | substReplacement body inner inductionHypothesis =>
      cases typed with
      | subst bodyTyped replacement =>
          obtain ⟨focusBound, result, selected⟩ := inductionHypothesis replacement
          exact ⟨focusBound, result, .substReplacement bodyTyped selected⟩
  | collection kind before inner after rest inductionHypothesis =>
      cases typed with
      | collection elements =>
          obtain ⟨_, middle, _⟩ := elements.append_cons_split
          obtain ⟨focusBound, result, selected⟩ := inductionHypothesis middle
          exact ⟨focusBound, result, .collection elements selected⟩
      | collectionConstructor membership shape elements =>
          obtain ⟨_, middle, _⟩ := elements.append_cons_split
          obtain ⟨focusBound, result, selected⟩ := inductionHypothesis middle
          exact ⟨focusBound, result, .collectionConstructor membership shape elements selected⟩

/-- Extraction tied to the existing selected-occurrence relation. -/
theorem HasType.selected_fvar {language : LanguageDef} {free : FreeTypeContext}
    {source : Pattern} {bound : List TypeExpr} {type : TypeExpr}
    (typed : HasType language free bound source type)
    {name : String} {context : OneHoleContext}
    (selection : Selects (.fvar name) context source) :
    ∃ focusBound result,
      TypedAt language free (.fvar name) context bound type focusBound result ∧
      free name = some result := by
  have filled : HasType language free bound (context.fill (.fvar name)) type :=
    selection.fill_eq.symm ▸ typed
  obtain ⟨focusBound, result, selected⟩ := hasType_typedAt context filled
  exact ⟨focusBound, result, selected, selected.fvar_lookup⟩

end Mettapedia.GSLT.LanguageDef.WellSorted
