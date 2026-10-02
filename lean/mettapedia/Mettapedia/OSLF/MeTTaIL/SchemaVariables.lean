import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# The metavariables of a schema, by structural recursion

`Pattern.freeFvarNames` is defined by well-founded recursion, which the
kernel does not unfold on a literal pattern.  This module gives the same list
by structural recursion, so that a statement about the variables of an
authored rule can be evaluated, and proves the two agree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

namespace Pattern

mutual
  /-- The metavariables of a schema in order of occurrence, a collection's
  rest variable last. -/
  def schemaVariables : Pattern → List String
    | .bvar _ => []
    | .fvar name => [name]
    | .apply _ arguments => schemaVariablesList arguments
    | .lambda _ body => schemaVariables body
    | .multiLambda _ _ body => schemaVariables body
    | .subst body replacement => schemaVariables body ++ schemaVariables replacement
    | .collection _ elements rest => schemaVariablesList elements ++ rest.toList

  /-- The metavariables of a list of schemas. -/
  def schemaVariablesList : List Pattern → List String
    | [] => []
    | pattern :: patterns => schemaVariables pattern ++ schemaVariablesList patterns
end

/-- The list form is the concatenation of the element forms. -/
theorem schemaVariablesList_eq_flatMap (patterns : List Pattern) :
    schemaVariablesList patterns = patterns.flatMap schemaVariables := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [schemaVariablesList, recurse]

/-- The structural list is the list of free variable names. -/
theorem schemaVariables_eq_freeFvarNames (pattern : Pattern) :
    pattern.schemaVariables = pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [schemaVariables, freeFvarNames]
  | hfvar name => simp [schemaVariables, freeFvarNames]
  | happly constructor arguments recurse =>
      simp only [schemaVariables, freeFvarNames, schemaVariablesList_eq_flatMap]
      exact List.flatMap_congr recurse
  | hlambda binderName body recurse => simpa [schemaVariables, freeFvarNames] using recurse
  | hmultiLambda arity binderNames body recurse =>
      simpa [schemaVariables, freeFvarNames] using recurse
  | hsubst body replacement recurseBody recurseReplacement =>
      simp [schemaVariables, freeFvarNames, recurseBody, recurseReplacement]
  | hcollection collectionType elements rest recurse =>
      simp only [schemaVariables, freeFvarNames, schemaVariablesList_eq_flatMap]
      rw [List.flatMap_congr recurse]

end Pattern

end Mettapedia.OSLF.MeTTaIL.Syntax
