import Mettapedia.GSLT.LanguageDef.WellSortedOccurrence

/-!
# Typed replacement at an existing occurrence

An occurrence zipper records the authored parameter and binder contexts
crossed on the way to a selected subterm. Replacing that subterm by one of
the same type preserves the typing derivation provided it also preserves
the representation form required by each authored parameter on the path.
This side condition matters for abstraction parameters: an arrow-typed
variable is not a locally nameless lambda node.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

private theorem arguments_append {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {left right : List Pattern}
    {leftParameters rightParameters : List TermParam}
    (front : ArgumentsHaveTypes language free bound left leftParameters)
    (back : ArgumentsHaveTypes language free bound right rightParameters) :
    ArgumentsHaveTypes language free bound (left ++ right)
      (leftParameters ++ rightParameters) :=
  match front with
  | .nil => by simpa using back
  | .cons representation parameterType typed rest =>
      .cons representation parameterType typed (arguments_append rest back)

private theorem elements_append {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elementType : TypeExpr}
    {left right : List Pattern}
    (front : ElementsHaveType language free bound left elementType)
    (back : ElementsHaveType language free bound right elementType) :
    ElementsHaveType language free bound (left ++ right) elementType :=
  match front with
  | .nil _ _ => by simpa using back
  | .cons typed rest => .cons typed (elements_append rest back)

/-- Representation compatibility across the existing zipper. Typing alone
does not imply this for binder-form parameters. -/
def RepresentationCompatible (source target : Pattern) : Prop :=
  ∀ (context : OneHoleContext) (parameter : TermParam),
    MatchesParameterRepresentation parameter (context.fill source) →
      MatchesParameterRepresentation parameter (context.fill target)

/-- Constructor applications can replace one another without changing the
outer representation class: only a binder frame can produce a binder at the
root, and it produces the same frame on either side. -/
theorem representationCompatible_apply
    (sourceLabel targetLabel : String) (sourceArgs targetArgs : List Pattern) :
    RepresentationCompatible (.apply sourceLabel sourceArgs)
      (.apply targetLabel targetArgs) := by
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

/-- Equal function types alone cannot justify replacement at an authored
abstraction parameter: the required lambda representation can be lost. -/
theorem lambda_to_variable_not_representationCompatible
    (body : Pattern) (name : String) :
    ¬ RepresentationCompatible (.lambda none body) (.fvar name) := by
  intro compatible
  have required := compatible .hole
    (.abstractionNamed none "body" (.base "A"))
    (by simp [MatchesParameterRepresentation, OneHoleContext.fill])
  simp [MatchesParameterRepresentation, OneHoleContext.fill] at required

/-- A typed replacement stays typed at the same ambient result type. This
uses the exact occurrence chosen by the original derivation; it does not
assume a deterministic grammar or invent a second context representation. -/
theorem TypedAt.replace {language : LanguageDef} {free : FreeTypeContext}
    {source target : Pattern} {context : OneHoleContext}
    {bound focusBound : List TypeExpr} {ambientType focusType : TypeExpr}
    (selected : TypedAt language free source context bound ambientType
      focusBound focusType)
    (compatible : RepresentationCompatible source target)
    (replacement : HasType language free focusBound target focusType) :
    HasType language free bound (context.fill target) ambientType := by
  induction selected with
  | here _ => exact replacement
  | @application rule before after inner bound focusBound expected result
      beforeParams afterParams parameter member ordinary arguments shape
      length parameterType innerSelected inductionHypothesis =>
      obtain ⟨actualBefore, actualParameter, actualAfter, actualExpected,
          actualShape, actualLength, beforeTyped, oldRepresentation,
          actualParameterType, _, afterTyped⟩ :=
        ArgumentsHaveTypes.append_cons_split arguments
      have aligned : beforeParams = actualBefore ∧
          parameter :: afterParams = actualParameter :: actualAfter :=
        List.append_inj (shape.symm.trans actualShape)
          (length.trans actualLength.symm)
      have parameterEq : parameter = actualParameter :=
        (List.cons.inj aligned.2).1
      have expectedEq : actualExpected = expected := by
        have sameOption : some actualExpected = some expected := by
          calc
            some actualExpected = parameterType? actualParameter :=
              actualParameterType.symm
            _ = parameterType? parameter := congrArg parameterType? parameterEq.symm
            _ = some expected := parameterType
        exact Option.some.inj sameOption
      have replacedInner : HasType language free bound
          (inner.fill target) expected := inductionHypothesis replacement
      have replacementRepresentation :
          MatchesParameterRepresentation actualParameter (inner.fill target) := by
        exact parameterEq.symm ▸ compatible inner parameter
          (parameterEq ▸ oldRepresentation)
      have replacedArgs : ArgumentsHaveTypes language free bound
          (before ++ inner.fill target :: after) rule.params := by
        rw [actualShape]
        exact arguments_append beforeTyped
          (.cons replacementRepresentation actualParameterType
            (expectedEq ▸ replacedInner) afterTyped)
      exact .constructor member ordinary replacedArgs
  | lambda _ inductionHypothesis =>
      exact .lambda (inductionHypothesis replacement)
  | multiLambda _ inductionHypothesis =>
      exact .multiLambda (inductionHypothesis replacement)
  | substBody replacementTyped _ inductionHypothesis =>
      exact .subst (inductionHypothesis replacement) replacementTyped
  | substReplacement bodyTyped _ inductionHypothesis =>
      exact .subst bodyTyped (inductionHypothesis replacement)
  | collection elements _ inductionHypothesis =>
      obtain ⟨beforeTyped, _, afterTyped⟩ :=
        ElementsHaveType.append_cons_split elements
      have replacedElements := elements_append beforeTyped
        (ElementsHaveType.cons (inductionHypothesis replacement) afterTyped)
      exact .collection replacedElements
  | collectionConstructor member shape elements _ inductionHypothesis =>
      obtain ⟨beforeTyped, _, afterTyped⟩ :=
        ElementsHaveType.append_cons_split elements
      have replacedElements := elements_append beforeTyped
        (ElementsHaveType.cons (inductionHypothesis replacement) afterTyped)
      exact .collectionConstructor member shape replacedElements

#print axioms TypedAt.replace
#print axioms representationCompatible_apply
#print axioms lambda_to_variable_not_representationCompatible

end Mettapedia.GSLT.LanguageDef.WellSorted
