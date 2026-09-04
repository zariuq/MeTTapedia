import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Explicit pattern-equality decision service

Some authored transformations must branch on structural equality without
making their rewrite systems overlap. This module provides a two-constructor
result language and an explicit total relation environment. Authored rules
query the decision and then dispatch on the result constructor.

The service decides only pattern identity. It performs no reduction and does
not inspect any language-specific constructor vocabulary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PatternEqualityDecision

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.TotalGSLT

def equal : Pattern :=
  .apply "pattern-equality-decision:equal" []

def different : Pattern :=
  .apply "pattern-equality-decision:different" []

private def ctor (label : String) : GrammarRule := {
  label
  category := "PatternEqualityDecision:Result"
  params := []
  syntaxPattern := [.terminal label]
  evalPolicy? := none
}

def language : LanguageDef := {
  name := "PatternEqualityDecision"
  types := ["PatternEqualityDecision:Result"]
  terms := [
    ctor "pattern-equality-decision:equal",
    ctor "pattern-equality-decision:different"]
  equations := []
  rewrites := []
}

theorem language_validate : language.validate = [] := by
  decide +kernel

def validated : ValidatedLanguageDef :=
  ⟨language, language_validate⟩

theorem no_equations : language.equations = [] := rfl
theorem no_rewrites : language.rewrites = [] := rfl

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language
    (ReductionRespectsEquations.of_equation_free rfl)

theorem theory_no_step (source target : Pattern) :
    ¬ theory.Step source target := by
  intro reduction
  unfold theory at reduction
  rw [languageGSLT_step] at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

def relationName : String :=
  "PatternEqualityDecision"

/-- The third relation argument is an output position. Its incoming shape is
irrelevant; relation matching binds it to exactly one decision constructor. -/
def relationTuples (relation : String) (arguments : List Pattern) :
    List (List Pattern) :=
  match relation, arguments with
  | "PatternEqualityDecision", [left, right, _] =>
      [[left, right, if left = right then equal else different]]
  | _, _ => []

def relationEnv : RelationEnv where
  tuples := relationTuples

theorem equal_exact (pattern output : Pattern) :
    relationTuples relationName [pattern, pattern, output] =
      [[pattern, pattern, equal]] := by
  simp [relationTuples, relationName]

theorem different_exact {left right output : Pattern}
    (differentPatterns : left ≠ right) :
    relationTuples relationName [left, right, output] =
      [[left, right, different]] := by
  simp [relationTuples, relationName, differentPatterns]

theorem result_is_total (left right output : Pattern) :
    (relationTuples relationName [left, right, output]).length = 1 := by
  simp [relationTuples, relationName]

theorem equal_ne_different : equal ≠ different := by
  decide

#print axioms language_validate
#print axioms theory_no_step
#print axioms language_supported
#print axioms equal_exact
#print axioms different_exact
#print axioms result_is_total
#print axioms equal_ne_different

end Mettapedia.GSLT.LanguageDef.PatternEqualityDecision
