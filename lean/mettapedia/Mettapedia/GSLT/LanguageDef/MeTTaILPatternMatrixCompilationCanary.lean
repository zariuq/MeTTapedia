import Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Transfer and mutation canary for MeTTaIL pattern-matrix compilation

This small rewrite language is independent of the PeTTa call guard.  It tests
three properties of the generic compiler at once:

* source order remains observable when two rules produce reducts;
* a repeated-variable row may pass structural selection while the canonical
  matcher rejects it;
* reordering authored rows changes residual execution in exactly the same way
  as it changes the source semantics.

Both source languages pass the ordinary `LanguageDef` validator.  The canary
therefore exercises the reusable compilation boundary rather than a private
fixture representation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilationCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep

namespace Matrix

export Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation.Matrix
  (lowerSubject syntacticOccurrenceAttempt compileLanguage
    compileLanguage_evalAll_eq_rewriteAt)

end Matrix

private def termType : TypeDecl := TypeDecl.plain "Term"

private def parameter (name : String) : TermParam :=
  .simple name (.base termType.name)

private def constructor (label : String) (parameters : List TermParam) :
    GrammarRule :=
  GrammarRule.mk label termType.name parameters [] none none

private def terms : List GrammarRule :=
  [ constructor "Left" []
  , constructor "Right" []
  , constructor "Unknown" []
  , constructor "Pair" [parameter "left", parameter "right"]
  , constructor "Specific" [parameter "value"]
  , constructor "Same" [parameter "value"]
  , constructor "Fallback" [parameter "left", parameter "right"]
  ]

private def specificRule : RewriteRule :=
  RewriteRule.mk "SpecificRule" [] []
    (.apply "Pair" [.apply "Left" [], .fvar "X"])
    (.apply "Specific" [.fvar "X"])

private def repeatedRule : RewriteRule :=
  RewriteRule.mk "RepeatedRule" [] []
    (.apply "Pair" [.fvar "X", .fvar "X"])
    (.apply "Same" [.fvar "X"])

private def fallbackRule : RewriteRule :=
  RewriteRule.mk "FallbackRule" [] []
    (.apply "Pair" [.fvar "X", .fvar "Y"])
    (.apply "Fallback" [.fvar "X", .fvar "Y"])

/-- The original authored order: specific, repeated-variable, fallback. -/
def language : LanguageDef :=
  LanguageDef.ofCore "PatternMatrixTransferCanary" [termType] terms []
    [specificRule, repeatedRule, fallbackRule]

/-- A load-bearing mutation that moves the fallback rule first. -/
def reorderedLanguage : LanguageDef :=
  LanguageDef.ofCore "PatternMatrixTransferCanaryReordered" [termType] terms []
    [fallbackRule, repeatedRule, specificRule]

private theorem term_category_of_mem {term : GrammarRule}
    (membership : term ∈ terms) : term.category = termType.name := by
  have categories : ∀ item ∈ terms, item.category = termType.name := by
    simp [terms, constructor]
  exact categories term membership

private theorem parameter_type_of_mem {term : GrammarRule}
    (termMembership : term ∈ terms) {param : TermParam}
    (paramMembership : param ∈ term.params) {typeName : String}
    (typeMembership : typeName ∈ param.typeExpr.baseNames) :
    typeName = termType.name := by
  have parameterTypes : ∀ item ∈ terms, ∀ itemParameter ∈ item.params,
      ∀ name ∈ itemParameter.typeExpr.baseNames,
        name = termType.name := by
    simp [terms, constructor, parameter, TermParam.typeExpr,
      TypeExpr.baseNames, termType, TypeDecl.plain]
  exact parameterTypes term termMembership param paramMembership typeName
    typeMembership

private theorem syntax_of_mem {term : GrammarRule}
    (membership : term ∈ terms) :
    term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param =>
        SyntaxItem.nonTerminal param.bodyName) := by
  have syntaxValid : ∀ item ∈ terms,
      item.syntaxPattern = [] ∨
        item.syntaxPattern = item.params.map (fun param =>
          SyntaxItem.nonTerminal param.bodyName) := by
    simp [terms, constructor]
  exact syntaxValid term membership

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes =>
    simp [language, LanguageDef.ofCore, LanguageDef.typeNames, termType,
      TypeDecl.plain]
  case hconstructors => decide
  case hrewrites => decide
  case hcategory =>
    intro term membership
    have category := term_category_of_mem (by
      simpa [language, LanguageDef.ofCore] using membership)
    simpa [language, LanguageDef.ofCore, LanguageDef.typeNames] using category
  case hparams =>
    intro term termMembership param paramMembership typeName typeMembership
    have parameterType := parameter_type_of_mem
      (by simpa [language, LanguageDef.ofCore] using termMembership)
      paramMembership typeMembership
    simpa [language, LanguageDef.ofCore, LanguageDef.typeNames] using
      parameterType
  case hsyntax =>
    intro term membership
    apply syntax_of_mem
    simpa [language, LanguageDef.ofCore] using membership
  case hrewriteValid =>
    intro rule membership
    simp only [language, LanguageDef.ofCore, List.mem_cons,
      List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl | rfl
    all_goals
      simp +decide [LanguageDef.validateRewrite, language, terms, constructor,
        parameter, termType, specificRule, repeatedRule, fallbackRule,
        LanguageDef.validatePatternConstructors,
        LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames,
        LanguageDef.typeNames]

theorem reorderedLanguage_validate : reorderedLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  case hequations => rfl
  case htypes =>
    simp [reorderedLanguage, LanguageDef.ofCore, LanguageDef.typeNames,
      termType, TypeDecl.plain]
  case hconstructors => decide
  case hrewrites => decide
  case hcategory =>
    intro term membership
    have category := term_category_of_mem (by
      simpa [reorderedLanguage, LanguageDef.ofCore] using membership)
    simpa [reorderedLanguage, LanguageDef.ofCore, LanguageDef.typeNames] using
      category
  case hparams =>
    intro term termMembership param paramMembership typeName typeMembership
    have parameterType := parameter_type_of_mem
      (by simpa [reorderedLanguage, LanguageDef.ofCore] using termMembership)
      paramMembership typeMembership
    simpa [reorderedLanguage, LanguageDef.ofCore, LanguageDef.typeNames] using
      parameterType
  case hsyntax =>
    intro term membership
    apply syntax_of_mem
    simpa [reorderedLanguage, LanguageDef.ofCore] using membership
  case hrewriteValid =>
    intro rule membership
    simp only [reorderedLanguage, LanguageDef.ofCore, List.mem_cons,
      List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl | rfl
    all_goals
      simp +decide [LanguageDef.validateRewrite, reorderedLanguage, terms,
        constructor, parameter, termType, specificRule, repeatedRule,
        fallbackRule, LanguageDef.validatePatternConstructors,
        LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames,
        LanguageDef.typeNames]

def validatedLanguage : ValidatedLanguageDef :=
  ⟨language, language_validate⟩

def validatedReorderedLanguage : ValidatedLanguageDef :=
  ⟨reorderedLanguage, reorderedLanguage_validate⟩

private abbrev base : BasePremiseEvaluator :=
  fun _ _ _ => []

/-- Run the total generic compiler with the canonical syntactic rule
continuation at root-rewrite depth one. -/
def run (definition : LanguageDef) (source : Pattern) : List Pattern :=
  (Matrix.compileLanguage definition).evalAll
    (Matrix.syntacticOccurrenceAttempt base definition
      (rewriteAt RuleInterpretation.syntactic base definition 0) source)
    [Matrix.lowerSubject source]

/-- Residual execution is exactly source execution for every language, not
only for the two canary values. -/
theorem run_eq_rewriteAt (definition : LanguageDef) (source : Pattern) :
    run definition source =
      rewriteAt RuleInterpretation.syntactic base definition 1 source := by
  simpa [run] using
    (Matrix.compileLanguage_evalAll_eq_rewriteAt base definition 0 source)

private def unequalPair : Pattern :=
  .apply "Pair" [.apply "Left" [], .apply "Right" []]

private def specificResult : Pattern :=
  .apply "Specific" [.apply "Right" []]

private def fallbackResult : Pattern :=
  .apply "Fallback" [.apply "Left" [], .apply "Right" []]

/-- Positive control: both successful reducts appear in authored order; the
intervening repeated-variable rule contributes no result. -/
theorem original_results :
    run language unequalPair = [specificResult, fallbackResult] := by
  rw [run_eq_rewriteAt]
  decide +kernel

/-- Mutation control: changing only the authored row order changes the
residual result order accordingly. -/
theorem reordered_results :
    run reorderedLanguage unequalPair = [fallbackResult, specificResult] := by
  rw [run_eq_rewriteAt]
  decide +kernel

/-- The source-order mutation is operationally observable. -/
theorem row_order_is_load_bearing :
    run language unequalPair != run reorderedLanguage unequalPair := by
  rw [original_results, reordered_results]
  decide

/-- Negative control: an unrelated constructor has no source or compiled
reduct. -/
theorem unknown_rejected :
    run language (.apply "Unknown" []) = [] := by
  rw [run_eq_rewriteAt]
  decide +kernel

#print axioms run_eq_rewriteAt
#print axioms original_results
#print axioms reordered_results
#print axioms row_order_is_load_bearing
#print axioms unknown_rejected

end Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilationCanary
