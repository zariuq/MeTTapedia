import Mettapedia.OSLF.MeTTaIL.Syntax

/-! Ordered observations of free names and binder annotations. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

structure PatternNames where
  free : List String
  binders : List String

private def PatternNames.append (left right : PatternNames) : PatternNames :=
  ⟨left.free ++ right.free, left.binders ++ right.binders⟩

mutual

/-- Collect the two name observations in one structural traversal. -/
def Pattern.names : Pattern → PatternNames
  | .bvar _ => ⟨[], []⟩
  | .fvar name => ⟨[name], []⟩
  | .apply _ arguments => Pattern.namesList arguments
  | .lambda binder body =>
      let inner := body.names
      ⟨inner.free, binder.toList ++ inner.binders⟩
  | .multiLambda _ binders body =>
      let inner := body.names
      ⟨inner.free, binders ++ inner.binders⟩
  | .subst body argument => body.names.append argument.names
  | .collection _ elements rest =>
      let inner := Pattern.namesList elements
      ⟨inner.free ++ rest.toList, inner.binders⟩

def Pattern.namesList : List Pattern → PatternNames
  | [] => ⟨[], []⟩
  | head :: tail => head.names.append (Pattern.namesList tail)

end

mutual

theorem Pattern.names_eq : ∀ pattern : Pattern,
    pattern.names =
      ⟨pattern.freeFvarNames, LanguageDef.patternBinderNames pattern⟩
  | .bvar _ => by simp [Pattern.names, Pattern.freeFvarNames, LanguageDef.patternBinderNames]
  | .fvar _ => by simp [Pattern.names, Pattern.freeFvarNames, LanguageDef.patternBinderNames]
  | .apply _ arguments => by
      simp [Pattern.names, Pattern.freeFvarNames, LanguageDef.patternBinderNames,
        namesList_eq arguments]
  | .lambda binder body => by
      cases binder <;>
        simp [Pattern.names, Pattern.freeFvarNames, LanguageDef.patternBinderNames, names_eq body]
  | .multiLambda _ _ body => by
      simp [Pattern.names, Pattern.freeFvarNames, LanguageDef.patternBinderNames, names_eq body]
  | .subst body argument => by
      simp [Pattern.names, Pattern.freeFvarNames, LanguageDef.patternBinderNames,
        names_eq body, names_eq argument, PatternNames.append]
  | .collection _ elements _ => by
      simp [Pattern.names, Pattern.freeFvarNames, LanguageDef.patternBinderNames,
        namesList_eq elements]

theorem Pattern.namesList_eq : ∀ patterns : List Pattern,
    Pattern.namesList patterns =
      ⟨patterns.flatMap Pattern.freeFvarNames, patterns.flatMap LanguageDef.patternBinderNames⟩
  | [] => rfl
  | head :: tail => by
      simp [Pattern.namesList, names_eq head, namesList_eq tail, PatternNames.append]

end

def Pattern.freeNamesOutside (bound : List String) (pattern : Pattern) : List String :=
  pattern.names.free.filter (fun name => !bound.contains name)

theorem LanguageDef.patternFvarNames_eq_traversal (bound : List String) :
    patternFvarNames bound = Pattern.freeNamesOutside bound := by
  funext pattern
  simp [patternFvarNames, Pattern.freeNamesOutside, pattern.names_eq]

theorem LanguageDef.patternBinderNames_eq_traversal :
    patternBinderNames = fun pattern => pattern.names.binders := by
  funext pattern
  simp [pattern.names_eq]

/-- Free names from the premise's patterns, with collection parameters
bound in the quantifier body. -/
def Premise.freeNamesOutside (bound : List String) : Premise → List String
  | .freshness condition => Pattern.freeNamesOutside bound condition.term
  | .congruence left right =>
      Pattern.freeNamesOutside bound left ++ Pattern.freeNamesOutside bound right
  | .scopedStep step =>
      Pattern.freeNamesOutside bound step.source ++ Pattern.freeNamesOutside bound step.target
  | .relationQuery _ arguments => arguments.flatMap (Pattern.freeNamesOutside bound)
  | .forAll _ name body => Premise.freeNamesOutside (name :: bound) body

private theorem premiseFreeNames_eq (premise : Premise) (bound : List String) :
    LanguageDef.premiseFvarNames bound premise = premise.freeNamesOutside bound := by
  induction premise generalizing bound with
  | forAll _ name body ih =>
      simpa only [LanguageDef.premiseFvarNames, Premise.freeNamesOutside] using ih (name :: bound)
  | freshness _ | congruence _ _ | scopedStep _ | relationQuery _ _ =>
      simp only [LanguageDef.premiseFvarNames, Premise.freeNamesOutside,
        LanguageDef.patternFvarNames_eq_traversal]

theorem LanguageDef.premiseFvarNames_eq_traversal (bound : List String) :
    premiseFvarNames bound = Premise.freeNamesOutside bound :=
  funext fun premise => premiseFreeNames_eq premise bound

/-- Names a premise can supply to a following rewrite. A quantified body
has local bindings and supplies no names. -/
def Premise.producedNamesOutside (bound : List String) : Premise → List String
  | .freshness _ | .forAll _ _ _ => []
  | .congruence _ target => Pattern.freeNamesOutside bound target
  | .scopedStep step => Pattern.freeNamesOutside bound step.target
  | .relationQuery _ arguments => arguments.flatMap (Pattern.freeNamesOutside bound)

theorem LanguageDef.premiseProducedFvarNames_eq_traversal (bound : List String) :
    premiseProducedFvarNames bound = Premise.producedNamesOutside bound := by
  funext premise
  cases premise <;>
    simp only [premiseProducedFvarNames, Premise.producedNamesOutside, patternFvarNames_eq_traversal]

end Mettapedia.OSLF.MeTTaIL.Syntax
