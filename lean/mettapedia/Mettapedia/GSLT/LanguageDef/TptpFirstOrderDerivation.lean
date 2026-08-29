import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.TptpFirstOrderDocument
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# First-order TSTP derivation data

This inert language is the normalized derivation-data extension of
`TptpFirstOrderDocument`.  The document presentation is retained as an exact
prefix: formulae, roles, names, spans, and generic syntax data have one
spelling.  The extension adds the recursive source records and useful
information standardized by TPTP/TSTP, including nested anonymous inference
records, alternative sources, assumptions, semantic statuses, and introduced
symbols.

The status and rule-name values remain authored strings.  TPTP and the SZS
ontology evolve, so this carrier must preserve new values without pretending
that it already knows their logical meaning.  A verifier interprets them only
through an explicitly supplied, separately validated calculus environment.

The node list is an authored topological-order candidate, not a proof by
construction.  Unique names, parent availability, acyclicity, relevance,
root conditions, discharge, freshness, and inference validity belong to the
single-pass verifier.  This presentation performs no search and contains no
calculus-specific rewrite rule.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpFirstOrderDerivation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.OSLF.Framework.TypeSynthesis

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := none
}

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

/-- New carrier sorts contributed by the derivation layer. -/
def addedTypes : List TypeDecl := [
  "RuleName", "StatusValue", "IntroType", "FileName", "TheoryName",
  "CreatorName", "PrincipalSymbol", "PrincipalSymbols", "InfoItem",
  "InfoItems", "SourceOption", "Source", "Sources", "ParentDetails",
  "Parent", "Parents", "DerivationNode", "DerivationNodes", "Derivation"]

/-- New constructors contributed by the derivation layer.  Existing document
constructors are never copied or renamed here; `extension.apply` retains them
as the exact prefix of the composite presentation. -/
def addedTerms : List GrammarRule := [
  ctor "tstp:rule-name" "RuleName" [("value", "String")],
  ctor "tstp:status-value" "StatusValue" [("value", "String")],
  ctor "tstp:intro-type" "IntroType" [("value", "String")],
  ctor "tstp:file-name" "FileName" [("value", "String")],
  ctor "tstp:theory-name" "TheoryName" [("value", "String")],
  ctor "tstp:creator-name" "CreatorName" [("value", "String")],

  ctor "tstp:principal-symbol-function" "PrincipalSymbol"
    [("symbol", "SymbolName")],
  ctor "tstp:principal-symbol-variable" "PrincipalSymbol"
    [("variable", "VariableName")],
  ctor "tstp:principal-symbols-nil" "PrincipalSymbols" [],
  ctor "tstp:principal-symbols-cons" "PrincipalSymbols"
    [("first", "PrincipalSymbol"), ("rest", "PrincipalSymbols")],

  ctor "tstp:info-status" "InfoItem" [("status", "StatusValue")],
  ctor "tstp:info-assumptions" "InfoItem"
    [("assumptions", "FormulaNames")],
  ctor "tstp:info-new-symbols" "InfoItem"
    [("kind", "IntroType"), ("symbols", "PrincipalSymbols")],
  ctor "tstp:info-refutation" "InfoItem"
    [("file", "FileName"), ("formula", "OptionalFormulaName")],
  ctor "tstp:info-inference" "InfoItem"
    [("rule", "RuleName"), ("key", "String"), ("value", "SyntaxNode")],
  ctor "tstp:info-raw" "InfoItem" [("value", "SyntaxNode")],
  ctor "tstp:info-items-nil" "InfoItems" [],
  ctor "tstp:info-items-cons" "InfoItems"
    [("first", "InfoItem"), ("rest", "InfoItems")],

  ctor "tstp:source-none" "SourceOption" [],
  ctor "tstp:source-some" "SourceOption" [("source", "Source")],
  ctor "tstp:source-name" "Source" [("name", "FormulaName")],
  ctor "tstp:source-inference" "Source"
    [("rule", "RuleName"), ("info", "InfoItems"),
     ("parents", "Parents")],
  ctor "tstp:source-introduced" "Source"
    [("kind", "IntroType"), ("info", "InfoItems"),
     ("parents", "Parents")],
  ctor "tstp:source-file" "Source"
    [("file", "FileName"), ("formula", "OptionalFormulaName")],
  ctor "tstp:source-theory" "Source"
    [("theory", "TheoryName"), ("info", "InfoItems")],
  ctor "tstp:source-creator" "Source"
    [("creator", "CreatorName"), ("info", "InfoItems"),
     ("parents", "Parents")],
  ctor "tstp:source-unknown" "Source" [],
  ctor "tstp:source-alternatives" "Source" [("sources", "Sources")],
  ctor "tstp:sources-nil" "Sources" [],
  ctor "tstp:sources-cons" "Sources"
    [("first", "Source"), ("rest", "Sources")],

  ctor "tstp:parent-details-none" "ParentDetails" [],
  ctor "tstp:parent-details-some" "ParentDetails"
    [("value", "SyntaxNode")],
  ctor "tstp:parent" "Parent"
    [("source", "Source"), ("details", "ParentDetails")],
  ctor "tstp:parents-nil" "Parents" [],
  ctor "tstp:parents-cons" "Parents"
    [("first", "Parent"), ("rest", "Parents")],

  ctor "tstp:derivation-node" "DerivationNode"
    [("occurrence", "OccurrenceId"), ("dialect", "Dialect"),
     ("name", "FormulaName"), ("role", "Role"),
     ("formula", "Formula"), ("source", "SourceOption"),
     ("usefulInfo", "InfoItems"), ("span", "SourceSpan")],
  ctor "tstp:derivation-nodes-nil" "DerivationNodes" [],
  ctor "tstp:derivation-nodes-cons" "DerivationNodes"
    [("first", "DerivationNode"), ("rest", "DerivationNodes")],
  ctor "tstp:derivation" "Derivation"
    [("source", "SourceDigest"), ("nodes", "DerivationNodes")]
]

private def base : CalculusLanguageDef :=
  CalculusLanguageDef.extend TptpFirstOrderDocument.language {}

/-- The derivation carrier is an explicit append-only extension, not a second
manually synchronized copy of the first-order document language. -/
def extension : CalculusLanguageExtension := {
  newTypes := addedTypes
  newTerms := addedTerms
  rename := some "TptpFirstOrderDerivation"
}

def calculusLanguage : CalculusLanguageDef := extension.apply base

def language : LanguageDef := calculusLanguage.toLanguageDef

theorem extension_disjoint : extension.disjointFrom base = true := by
  decide +kernel

theorem appendOnly :
    AppendOnlyCalculusRefinement base calculusLanguage :=
  extension.apply_appendOnly base

theorem document_types_exact_prefix :
    TptpFirstOrderDocument.language.types.IsPrefix language.types := by
  change TptpFirstOrderDocument.language.types.IsPrefix calculusLanguage.types
  exact appendOnly.types

theorem document_terms_exact_prefix :
    TptpFirstOrderDocument.language.terms.IsPrefix language.terms := by
  change TptpFirstOrderDocument.language.terms.IsPrefix calculusLanguage.terms
  exact appendOnly.terms

theorem language_validate : language.validate = [] := by
  decide +kernel

theorem language_inventory :
    language.types.length = 46 ∧ language.terms.length = 99 ∧
      language.rewrites.length = 0 := by
  decide

theorem nested_inference_crossing :
    ("tstp:source-some", "Source", "SourceOption") ∈
      unaryCrossings language := by
  decide

theorem formula_derivation_crossing :
    ("tstp:source-name", "FormulaName", "Source") ∈
      unaryCrossings language := by
  decide

theorem no_unchecked_derivation_crossing :
    ("tstp:unchecked-formula", "Formula", "Derivation") ∉
      unaryCrossings language := by
  decide

private def demoRule (name : String) : Pattern :=
  a "tstp:rule-name" [a name]

private def demoStatus : Pattern :=
  a "tstp:info-items-cons"
    [a "tstp:info-status" [a "tstp:status-value" [a "thm"]],
     a "tstp:info-items-nil"]

private def namedParent (name : String) : Pattern :=
  a "tstp:parent"
    [a "tstp:source-name"
       [a "tptp-fo:formula-name-atomic"
          [a "tptp-fo:symbol-name"
             [a "tptp-fo:symbol-lower", a name]]],
     a "tstp:parent-details-none"]

private def parentList (parent : Pattern) : Pattern :=
  a "tstp:parents-cons" [parent, a "tstp:parents-nil"]

/-- E-style nested anonymous inference records are represented without
flattening or inventing a named intermediate node. -/
def nestedInferenceSource : Pattern :=
  a "tstp:source-inference"
    [demoRule "cn", demoStatus,
     parentList
       (a "tstp:parent"
         [a "tstp:source-inference"
            [demoRule "rw", demoStatus,
             parentList (namedParent "c_0_7")],
          a "tstp:parent-details-none"])]

theorem nested_inference_inhabits_source :
    checkHasType language WellSorted.FreeTypeContext.empty [] nestedInferenceSource
      (.base "Source") = true := by
  decide +kernel

/-- A formula body is not silently accepted where a parent source is
required. -/
theorem formula_not_parent_source :
    checkHasType language WellSorted.FreeTypeContext.empty []
      (a "tptp-fo:formula-atom"
        [a "tptp-fo:atom-predicate"
          [a "tptp-fo:symbol-name"
            [a "tptp-fo:symbol-lower", a "p"],
           a "tptp-fo:terms-nil"]])
      (.base "Source") = false := by
  decide +kernel

/-- Rule names in nested sources are operational data and are not collapsed
by the carrier. -/
theorem nested_rule_names_are_distinct :
    a "tstp:source-inference"
        [demoRule "rw", demoStatus, a "tstp:parents-nil"] ≠
      a "tstp:source-inference"
        [demoRule "cn", demoStatus, a "tstp:parents-nil"] := by
  decide

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language
    (ReductionRespectsEquations.of_no_equations rfl)

theorem theory_no_step (source target : Pattern) :
    ¬ theory.Step source target := by
  intro reduction
  change langReducesUsing RelationEnv.empty language source target at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

def stepDecision : EffectiveStructure.StepDecision theory where
  decideStep _ _ := false
  correct := by
    intro source target
    simp only [Bool.false_eq_true, false_iff]
    exact theory_no_step source target

def oslf := langOSLF language "Derivation"

theorem galois :
    GaloisConnection (langDiamond language) (langBox language) :=
  langGalois language

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms extension_disjoint
#print axioms document_types_exact_prefix
#print axioms document_terms_exact_prefix
#print axioms language_validate
#print axioms nested_inference_crossing
#print axioms formula_derivation_crossing
#print axioms no_unchecked_derivation_crossing
#print axioms nested_inference_inhabits_source
#print axioms formula_not_parent_source
#print axioms nested_rule_names_are_distinct
#print axioms theory_no_step
#print axioms galois
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFirstOrderDerivation
