import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Scoped first-order clause data

This is the semantic target of parsing and clausification stages, not a
concrete-syntax grammar and not an ATP implementation.  Variables carry their
source-clause occurrence explicitly, so clauses are standardized apart by
construction.  Source digests, formula names, roles, annotations, and spans
remain data instead of being erased by an ATP projection.

The carrier intentionally has no rewrite rules.  Transformations into it and
proof calculi over it are separate GSLTs.
-/

namespace Mettapedia.GSLT.LanguageDef.FirstOrderClauseData

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

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

/-- A source-preserving, explicitly scoped first-order clause carrier. -/
def language : LanguageDef := {
  name := "FirstOrderClauseData"
  types := [
    { name := "String", carrier := .builtinString },
    { name := "Integer", carrier := .builtinInt },
    "SourceDigest", "OccurrenceId", "FormulaName", "Role",
    "SymbolKind", "SymbolName", "VariableName", "VariableId",
    "NumericKind", "Term", "Terms", "Atom", "Literal", "Literals",
    "SyntaxNode", "SyntaxNodes", "Annotation", "SourceSpan",
    "Clause", "Clauses", "Problem"]
  terms := [
    ctor "fo-cnf:source-digest" "SourceDigest" [("value", "String")],
    ctor "fo-cnf:occurrence" "OccurrenceId"
      [("source", "SourceDigest"), ("index", "Integer")],
    ctor "fo-cnf:formula-name-atomic" "FormulaName"
      [("value", "SymbolName")],
    ctor "fo-cnf:formula-name-integer" "FormulaName"
      [("lexeme", "String")],
    ctor "fo-cnf:role" "Role"
      [("base", "String"), ("refinement", "Annotation")],

    ctor "fo-cnf:symbol-lower" "SymbolKind" [],
    ctor "fo-cnf:symbol-quoted" "SymbolKind" [],
    ctor "fo-cnf:symbol-defined" "SymbolKind" [],
    ctor "fo-cnf:symbol-system" "SymbolKind" [],
    ctor "fo-cnf:symbol-name" "SymbolName"
      [("kind", "SymbolKind"), ("value", "String")],

    ctor "fo-cnf:variable-name" "VariableName" [("value", "String")],
    ctor "fo-cnf:variable-id" "VariableId"
      [("scope", "OccurrenceId"), ("name", "VariableName")],

    ctor "fo-cnf:number-integer" "NumericKind" [],
    ctor "fo-cnf:number-rational" "NumericKind" [],
    ctor "fo-cnf:number-real" "NumericKind" [],
    ctor "fo-cnf:term-variable" "Term" [("variable", "VariableId")],
    ctor "fo-cnf:term-function" "Term"
      [("function", "SymbolName"), ("arguments", "Terms")],
    ctor "fo-cnf:term-number" "Term"
      [("kind", "NumericKind"), ("lexeme", "String")],
    ctor "fo-cnf:term-distinct" "Term" [("lexeme", "String")],
    ctor "fo-cnf:terms-nil" "Terms" [],
    ctor "fo-cnf:terms-cons" "Terms"
      [("first", "Term"), ("rest", "Terms")],

    ctor "fo-cnf:atom-predicate" "Atom"
      [("predicate", "SymbolName"), ("arguments", "Terms")],
    ctor "fo-cnf:atom-equality" "Atom"
      [("left", "Term"), ("right", "Term")],
    ctor "fo-cnf:literal-positive" "Literal" [("atom", "Atom")],
    ctor "fo-cnf:literal-negative" "Literal" [("atom", "Atom")],
    ctor "fo-cnf:literals-nil" "Literals" [],
    ctor "fo-cnf:literals-cons" "Literals"
      [("first", "Literal"), ("rest", "Literals")],

    ctor "fo-cnf:syntax-atom" "SyntaxNode" [("value", "String")],
    ctor "fo-cnf:syntax-string" "SyntaxNode" [("value", "String")],
    ctor "fo-cnf:syntax-integer" "SyntaxNode" [("value", "Integer")],
    ctor "fo-cnf:syntax-list" "SyntaxNode" [("items", "SyntaxNodes")],
    ctor "fo-cnf:syntax-nodes-nil" "SyntaxNodes" [],
    ctor "fo-cnf:syntax-nodes-cons" "SyntaxNodes"
      [("first", "SyntaxNode"), ("rest", "SyntaxNodes")],
    ctor "fo-cnf:annotation-none" "Annotation" [],
    ctor "fo-cnf:annotation-tree" "Annotation" [("tree", "SyntaxNode")],
    ctor "fo-cnf:source-span" "SourceSpan"
      [("start", "Integer"), ("stop", "Integer")],
    ctor "fo-cnf:source-span-unknown" "SourceSpan" [],

    ctor "fo-cnf:clause" "Clause"
      [("occurrence", "OccurrenceId"), ("name", "FormulaName"),
       ("role", "Role"), ("literals", "Literals"),
       ("annotation", "Annotation"), ("span", "SourceSpan")],
    ctor "fo-cnf:clauses-nil" "Clauses" [],
    ctor "fo-cnf:clauses-cons" "Clauses"
      [("first", "Clause"), ("rest", "Clauses")],
    ctor "fo-cnf:problem" "Problem"
      [("source", "SourceDigest"), ("clauses", "Clauses")]
  ]
  equations := []
  rewrites := []
}

theorem language_validate : language.validate = [] := by
  decide +kernel

theorem language_inventory :
    language.types.length = 23 ∧ language.terms.length = 41 ∧
      language.rewrites.length = 0 := by
  decide

theorem variable_id_term_crossing :
    ("fo-cnf:term-variable", "VariableId", "Term") ∈
      unaryCrossings language := by
  decide

theorem atom_literal_crossing :
    ("fo-cnf:literal-positive", "Atom", "Literal") ∈
      unaryCrossings language := by
  decide

theorem no_variable_direct_literal_crossing :
    ("fo-cnf:invented-variable-literal", "VariableId", "Literal") ∉
      unaryCrossings language := by
  decide

/-- The carrier is inert: computation belongs to separately authored
transformation and proof-calculus GSLTs. -/
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

def stepDecision : EffectiveStructure.StepDecision theory where
  decideStep _ _ := false
  correct := by
    intro source target
    simp only [Bool.false_eq_true, false_iff]
    exact theory_no_step source target

def oslf := langOSLF language "Problem"

theorem galois :
    GaloisConnection (langDiamond language) (langBox language) :=
  langGalois language

private def demoSource : Pattern :=
  a "fo-cnf:source-digest" [a "fo-cnf:demo-digest"]
private def demoOccurrence : Pattern :=
  a "fo-cnf:occurrence" [demoSource, a "fo-cnf:demo-index"]
private def otherOccurrence : Pattern :=
  a "fo-cnf:occurrence" [demoSource, a "fo-cnf:other-index"]
private def demoVariableName : Pattern :=
  a "fo-cnf:variable-name" [a "fo-cnf:demo-variable-name"]
private def demoVariable : Pattern :=
  a "fo-cnf:variable-id" [demoOccurrence, demoVariableName]
private def demoTerm : Pattern :=
  a "fo-cnf:term-variable" [demoVariable]

theorem distinct_scopes_do_not_collapse :
    a "fo-cnf:term-variable"
        [a "fo-cnf:variable-id" [otherOccurrence, demoVariableName]] ≠
      demoTerm := by
  decide

theorem demo_term_is_normal :
    rewriteAt (engineBasePremises RelationEnv.empty)
        language 1 demoTerm = [] := by
  decide +kernel

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms language_validate
#print axioms variable_id_term_crossing
#print axioms no_variable_direct_literal_crossing
#print axioms theory_no_step
#print axioms galois
#print axioms distinct_scopes_do_not_collapse
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.FirstOrderClauseData
