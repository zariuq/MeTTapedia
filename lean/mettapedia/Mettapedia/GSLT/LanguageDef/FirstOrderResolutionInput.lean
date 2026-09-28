import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Explicit first-order resolution input

This inert carrier is the normalized input boundary of a first-order
resolution calculus.  It deliberately keeps object variables as ground data,
including their source-clause scope, rather than confusing them with evaluator
variables.  The projection from source-preserving clause data may erase raw
annotations and byte spans, but it retains the source digest, occurrence,
formula name, and role needed to audit every input clause.

An input reached through include directives has an included occurrence: its
own source digest and index, and the occurrence of the include directive that
reached it.  The include path is part of the input's identity, so a file
included twice gives two inputs with separate variable scopes.

A clause obtained by clausifying a formula has a clausal occurrence: the
formula's occurrence and the clause's position in the formula's clausal form.
Symbols introduced by clausification have their own kinds, Skolem functions
and definitional predicates, whose values are their introduction indices, so an
introduced symbol is never spelled like a source symbol.

Search policy and proof checking are separate GSLTs.  This language supplies
neither an implicit unifier nor a native arithmetic or ATP oracle.
-/

namespace Mettapedia.GSLT.LanguageDef.FirstOrderResolutionInput

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

/-- Ground, scoped, source-auditable input to first-order resolution. -/
def language : LanguageDef := {
  name := "FirstOrderResolutionInput"
  types := [
    { name := "String", carrier := .builtinString },
    { name := "Integer", carrier := .builtinInt },
    "SourceDigest", "OccurrenceId", "FormulaName", "Role",
    "SymbolKind", "SymbolName", "VariableName", "VariableId",
    "NumericKind", "Term", "Terms", "Atom", "Literal", "Literals",
    "Clause", "Clauses", "Problem"]
  terms := [
    ctor "fo-resolution:source-digest" "SourceDigest" [("value", "String")],
    ctor "fo-resolution:occurrence" "OccurrenceId"
      [("source", "SourceDigest"), ("index", "Integer")],
    ctor "fo-resolution:included-occurrence" "OccurrenceId"
      [("source", "SourceDigest"), ("index", "Integer"),
       ("via", "OccurrenceId")],
    ctor "fo-resolution:clausal-occurrence" "OccurrenceId"
      [("formula", "OccurrenceId"), ("index", "Integer")],
    ctor "fo-resolution:formula-name-atomic" "FormulaName"
      [("value", "SymbolName")],
    ctor "fo-resolution:formula-name-integer" "FormulaName"
      [("lexeme", "String")],
    ctor "fo-resolution:role" "Role" [("base", "String")],

    ctor "fo-resolution:symbol-lower" "SymbolKind" [],
    ctor "fo-resolution:symbol-quoted" "SymbolKind" [],
    ctor "fo-resolution:symbol-defined" "SymbolKind" [],
    ctor "fo-resolution:symbol-system" "SymbolKind" [],
    ctor "fo-resolution:symbol-skolem" "SymbolKind" [],
    ctor "fo-resolution:symbol-definition" "SymbolKind" [],
    ctor "fo-resolution:symbol-name" "SymbolName"
      [("kind", "SymbolKind"), ("value", "String")],

    ctor "fo-resolution:variable-name" "VariableName" [("value", "String")],
    ctor "fo-resolution:variable-id" "VariableId"
      [("scope", "OccurrenceId"), ("name", "VariableName")],

    ctor "fo-resolution:number-integer" "NumericKind" [],
    ctor "fo-resolution:number-rational" "NumericKind" [],
    ctor "fo-resolution:number-real" "NumericKind" [],
    ctor "fo-resolution:term-variable" "Term" [("variable", "VariableId")],
    ctor "fo-resolution:term-function" "Term"
      [("function", "SymbolName"), ("arguments", "Terms")],
    ctor "fo-resolution:term-number" "Term"
      [("kind", "NumericKind"), ("lexeme", "String")],
    ctor "fo-resolution:term-distinct" "Term" [("lexeme", "String")],
    ctor "fo-resolution:terms-nil" "Terms" [],
    ctor "fo-resolution:terms-cons" "Terms"
      [("first", "Term"), ("rest", "Terms")],

    ctor "fo-resolution:atom-predicate" "Atom"
      [("predicate", "SymbolName"), ("arguments", "Terms")],
    ctor "fo-resolution:atom-equality" "Atom"
      [("left", "Term"), ("right", "Term")],
    ctor "fo-resolution:literal-positive" "Literal" [("atom", "Atom")],
    ctor "fo-resolution:literal-negative" "Literal" [("atom", "Atom")],
    ctor "fo-resolution:literals-nil" "Literals" [],
    ctor "fo-resolution:literals-cons" "Literals"
      [("first", "Literal"), ("rest", "Literals")],

    ctor "fo-resolution:clause" "Clause"
      [("occurrence", "OccurrenceId"), ("name", "FormulaName"),
       ("role", "Role"), ("literals", "Literals")],
    ctor "fo-resolution:clauses-nil" "Clauses" [],
    ctor "fo-resolution:clauses-cons" "Clauses"
      [("first", "Clause"), ("rest", "Clauses")],
    ctor "fo-resolution:problem" "Problem"
      [("source", "SourceDigest"), ("clauses", "Clauses")]
  ]
  equations := []
  rewrites := []
}

theorem language_validate : language.validate = [] := by
  decide +kernel

theorem language_inventory :
    language.types.length = 19 ∧ language.terms.length = 35 ∧
      language.rewrites.length = 0 := by
  decide

theorem variable_id_term_crossing :
    ("fo-resolution:term-variable", "VariableId", "Term") ∈
      unaryCrossings language := by
  decide

theorem atom_literal_crossing :
    ("fo-resolution:literal-positive", "Atom", "Literal") ∈
      unaryCrossings language := by
  decide

theorem no_unscoped_variable_term_crossing :
    ("fo-resolution:unscoped-variable", "VariableName", "Term") ∉
      unaryCrossings language := by
  decide

/-- Resolution input is data.  Calculus steps belong to another presentation. -/
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
  a "fo-resolution:source-digest" [a "fo-resolution:demo-digest"]
private def firstOccurrence : Pattern :=
  a "fo-resolution:occurrence" [demoSource, a "fo-resolution:first-index"]
private def secondOccurrence : Pattern :=
  a "fo-resolution:occurrence" [demoSource, a "fo-resolution:second-index"]
private def demoName : Pattern :=
  a "fo-resolution:variable-name" [a "fo-resolution:demo-name"]

theorem occurrence_scopes_are_not_collapsed :
    a "fo-resolution:variable-id" [firstOccurrence, demoName] ≠
      a "fo-resolution:variable-id" [secondOccurrence, demoName] := by
  decide

private def includedSource : Pattern :=
  a "fo-resolution:source-digest" [a "fo-resolution:included-digest"]
private def includedOnce : Pattern :=
  a "fo-resolution:included-occurrence"
    [includedSource, a "fo-resolution:first-index", firstOccurrence]
private def includedTwice : Pattern :=
  a "fo-resolution:included-occurrence"
    [includedSource, a "fo-resolution:first-index", secondOccurrence]

/-- One input of an included file, reached through two include directives,
is two inputs whose variables are distinct. -/
theorem include_paths_are_not_collapsed :
    a "fo-resolution:variable-id" [includedOnce, demoName] ≠
      a "fo-resolution:variable-id" [includedTwice, demoName] := by
  decide

/-- An included input is not the root-level input with the same digest and
index. -/
theorem included_occurrence_is_not_root_occurrence :
    includedOnce ≠
      a "fo-resolution:occurrence"
        [includedSource, a "fo-resolution:first-index"] := by
  decide

private def firstClausal : Pattern :=
  a "fo-resolution:clausal-occurrence"
    [firstOccurrence, a "fo-resolution:first-index"]
private def secondClausal : Pattern :=
  a "fo-resolution:clausal-occurrence"
    [firstOccurrence, a "fo-resolution:second-index"]

/-- Two clauses of one formula's clausal form have distinct variables. -/
theorem clausal_occurrences_are_not_collapsed :
    a "fo-resolution:variable-id" [firstClausal, demoName] ≠
      a "fo-resolution:variable-id" [secondClausal, demoName] := by
  decide

/-- A clause of a formula's clausal form is not the formula's own
occurrence. -/
theorem clausal_occurrence_is_not_formula_occurrence :
    firstClausal ≠ firstOccurrence := by
  decide

private def demoValue : Pattern := a "fo-resolution:demo-value"

/-- An introduced Skolem function is never a source symbol with the same
value. -/
theorem skolem_symbol_is_not_source_symbol :
    a "fo-resolution:symbol-name" [a "fo-resolution:symbol-skolem", demoValue] ≠
      a "fo-resolution:symbol-name" [a "fo-resolution:symbol-lower", demoValue] := by
  decide

/-- An introduced definitional predicate is never an introduced Skolem
function with the same value. -/
theorem definition_symbol_is_not_skolem_symbol :
    a "fo-resolution:symbol-name" [a "fo-resolution:symbol-definition", demoValue] ≠
      a "fo-resolution:symbol-name" [a "fo-resolution:symbol-skolem", demoValue] := by
  decide

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
#print axioms no_unscoped_variable_term_crossing
#print axioms theory_no_step
#print axioms galois
#print axioms occurrence_scopes_are_not_collapsed
#print axioms include_paths_are_not_collapsed
#print axioms included_occurrence_is_not_root_occurrence
#print axioms clausal_occurrences_are_not_collapsed
#print axioms clausal_occurrence_is_not_formula_occurrence
#print axioms skolem_symbol_is_not_source_symbol
#print axioms definition_symbol_is_not_skolem_symbol
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.FirstOrderResolutionInput
