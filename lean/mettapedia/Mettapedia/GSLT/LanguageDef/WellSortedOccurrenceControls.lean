import Mettapedia.GSLT.LanguageDef.WellSortedOccurrence

/-!
# Distinct occurrence scopes for the same schema variable

One authored constructor contains the same fvar at depth zero, under an A
binder, and under a B binder. Typing descent retains all three scopes. The
negative controls reject a fabricated scope and distinguish an ambient
context from a permission to move an open value outside its binder.
-/

namespace Mettapedia.GSLT.LanguageDef.WellSorted.OccurrenceControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

set_option autoImplicit false

def a : TypeExpr := .base "A"
def b : TypeExpr := .base "B"

def triple : GrammarRule where
  label := "triple"
  category := "Pack"
  params := [.simple "outer" a, .simple "underA" (.arrow a a),
    .simple "underB" (.arrow b a)]
  syntaxPattern := []

def constantA : GrammarRule where
  label := "constantA"
  category := "A"
  params := []
  syntaxPattern := []

def language : LanguageDef :=
  { LanguageDef.empty "typed-occurrence-controls" with
    types := [TypeDecl.plain "A", TypeDecl.plain "B", TypeDecl.plain "Pack"]
    terms := [triple, constantA] }

theorem language_valid : language.validate = [] := by decide +kernel

def free : FreeTypeContext := FreeTypeContext.ofList [("x", a)]
def holeTerm : Pattern := .fvar "x"
def enclosed : Pattern := .lambda none holeTerm
def source : Pattern := .apply "triple" [holeTerm, enclosed, enclosed]

def outerSite : OneHoleContext := .apply "triple" [] .hole [enclosed, enclosed]
def aSite : OneHoleContext := .apply "triple" [holeTerm] (.lambda none .hole) [enclosed]
def bSite : OneHoleContext := .apply "triple" [holeTerm, enclosed] (.lambda none .hole) []

theorem variable_typed (bound : List TypeExpr) : HasType language free bound holeTerm a :=
  .fvar rfl

theorem source_arguments : ArgumentsHaveTypes language free []
    [holeTerm, enclosed, enclosed] triple.params := by
  apply ArgumentsHaveTypes.cons (parameter := .simple "outer" a) (expected := a)
  · trivial
  · rfl
  · exact variable_typed []
  · apply ArgumentsHaveTypes.cons (parameter := .simple "underA" (.arrow a a))
      (expected := .arrow a a)
    · trivial
    · rfl
    · exact .lambda (variable_typed [a])
    · apply ArgumentsHaveTypes.cons (parameter := .simple "underB" (.arrow b a))
        (expected := .arrow b a)
      · trivial
      · rfl
      · exact .lambda (variable_typed [b])
      · exact .nil

theorem source_typed : HasType language free [] source (.base "Pack") := by
  apply HasType.constructor (rule := triple)
  · simp [language]
  · simp [UsesBareCollection, triple]
  · exact source_arguments

theorem all_three_select_same_name :
    Selects holeTerm outerSite source ∧ Selects holeTerm aSite source ∧
      Selects holeTerm bSite source :=
  ⟨.apply .here, .apply (.lambda .here), .apply (.lambda .here)⟩

theorem outer_scope : TypedAt language free holeTerm outerSite [] (.base "Pack") [] a := by
  exact .application (rule := triple) (by simp [language])
    (by simp [UsesBareCollection, triple]) source_arguments
    (beforeParams := []) rfl rfl rfl (.here (variable_typed []))

theorem under_a_scope : TypedAt language free holeTerm aSite [] (.base "Pack") [a] a := by
  exact .application (rule := triple) (by simp [language])
    (by simp [UsesBareCollection, triple]) source_arguments
    (beforeParams := [.simple "outer" a]) rfl rfl rfl
    (.lambda (.here (variable_typed [a])))

theorem under_b_scope : TypedAt language free holeTerm bSite [] (.base "Pack") [b] a := by
  exact .application (rule := triple) (by simp [language])
    (by simp [UsesBareCollection, triple]) source_arguments
    (beforeParams := [.simple "outer" a, .simple "underA" (.arrow a a)]) rfl rfl rfl
    (.lambda (.here (variable_typed [b])))

theorem equal_depth_different_binder_types : ([a] : List TypeExpr).length = [b].length ∧
    ([a] : List TypeExpr) ≠ [b] := by decide

theorem sibling_occurrence_paths_distinct : aSite ≠ bSite := by decide

theorem composed_binder_scope :
    TypedAt language free holeTerm
      ((OneHoleContext.lambda none .hole).comp (.lambda none .hole)) []
      (.arrow b (.arrow a a)) [a, b] a := by
  apply TypedAt.comp (middleBound := [b]) (middleType := .arrow a a)
  · exact .lambda (.here (.lambda (variable_typed [a, b])))
  · exact .lambda (.here (variable_typed [a, b]))

/-- Merely typing an fvar at an arbitrary context is not a path certificate. -/
theorem cannot_replace_b_with_a :
    ¬ TypedAt language free holeTerm (.lambda none .hole) [] (.arrow b a) [a] a := by
  intro selected
  cases selected with
  | lambda body =>
      have equality := body.hole_indices.1
      simp [a, b] at equality

/-- The same occurrence scope admits both an open and a closed value of A.
Typing alone therefore does not identify the value's binder dependencies. -/
theorem ambient_scope_does_not_determine_dependencies :
    HasType language FreeTypeContext.empty [a] (.bvar 0) a ∧
      HasType language FreeTypeContext.empty [] (.apply "constantA" []) a := by
  constructor
  · exact .bvar rfl
  · exact .constructor (rule := constantA) (by simp [language])
      (by simp [UsesBareCollection, constantA]) .nil

/-- An open value cannot leave its binder just because the schema fvar also
has an occurrence at the outer scope. -/
theorem open_value_not_authorized_at_outer_scope :
    ¬ HasType language FreeTypeContext.empty [] (.bvar 0) a := by
  intro typed
  cases typed with
  | bvar lookup => simp at lookup

theorem extraction_retains_authored_lookup :
    ∃ scope result,
      TypedAt language free holeTerm bSite [] (.base "Pack") scope result ∧
      free "x" = some result :=
  source_typed.selected_fvar all_three_select_same_name.2.2

end Mettapedia.GSLT.LanguageDef.WellSorted.OccurrenceControls
