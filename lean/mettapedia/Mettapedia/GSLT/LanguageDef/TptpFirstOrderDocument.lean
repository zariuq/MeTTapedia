import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# TPTP first-order semantic document

This inert carrier is the source-preserving semantic result of parsing the
FOF/CNF/include fragment of TPTP.  It is deliberately richer than clause data:
quantifiers and every first-order connective remain explicit, and CNF inputs
are represented as formula inputs rather than being silently privileged.

Clausification, include resolution, role policy, and proof checking are
separate transformations or calculi.  Raw annotations and source locations
remain attached to input occurrences so later erasure is explicit.

`VariableId` deliberately identifies a variable spelling within one input
occurrence.  It is not a binder identity: nested quantifiers may reuse the same
qualified spelling.  The binder-resolved input to capture-avoiding
transformations must refine these names with fresh binder identities.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpFirstOrderDocument

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

/-- Source-preserving formulas, CNF inputs, and include declarations. -/
def language : LanguageDef := {
  name := "TptpFirstOrderDocument"
  types := [
    { name := "String", carrier := .builtinString },
    { name := "Integer", carrier := .builtinInt },
    "SourceDigest", "OccurrenceId", "FormulaName", "FormulaNames",
    "OptionalFormulaName", "Role", "Dialect", "SymbolKind", "SymbolName",
    "VariableName", "VariableId", "Variables", "NumericKind", "Term",
    "Terms", "Atom", "Formula", "SyntaxNode", "SyntaxNodes", "Annotation",
    "SourceSpan", "IncludeSelection", "Input", "Inputs", "Document"]
  terms := [
    ctor "tptp-fo:source-digest" "SourceDigest" [("value", "String")],
    ctor "tptp-fo:occurrence" "OccurrenceId"
      [("source", "SourceDigest"), ("index", "Integer")],
    ctor "tptp-fo:formula-name-atomic" "FormulaName"
      [("value", "SymbolName")],
    ctor "tptp-fo:formula-name-integer" "FormulaName"
      [("lexeme", "String")],
    ctor "tptp-fo:formula-names-nil" "FormulaNames" [],
    ctor "tptp-fo:formula-names-cons" "FormulaNames"
      [("first", "FormulaName"), ("rest", "FormulaNames")],
    ctor "tptp-fo:formula-name-none" "OptionalFormulaName" [],
    ctor "tptp-fo:formula-name-some" "OptionalFormulaName"
      [("name", "FormulaName")],
    ctor "tptp-fo:role" "Role"
      [("base", "String"), ("refinement", "Annotation")],
    ctor "tptp-fo:dialect-fof" "Dialect" [],
    ctor "tptp-fo:dialect-cnf" "Dialect" [],

    ctor "tptp-fo:symbol-lower" "SymbolKind" [],
    ctor "tptp-fo:symbol-quoted" "SymbolKind" [],
    ctor "tptp-fo:symbol-defined" "SymbolKind" [],
    ctor "tptp-fo:symbol-system" "SymbolKind" [],
    ctor "tptp-fo:symbol-name" "SymbolName"
      [("kind", "SymbolKind"), ("value", "String")],
    ctor "tptp-fo:variable-name" "VariableName" [("value", "String")],
    ctor "tptp-fo:variable-id" "VariableId"
      [("scope", "OccurrenceId"), ("name", "VariableName")],
    ctor "tptp-fo:variables-nil" "Variables" [],
    ctor "tptp-fo:variables-cons" "Variables"
      [("first", "VariableId"), ("rest", "Variables")],

    ctor "tptp-fo:number-integer" "NumericKind" [],
    ctor "tptp-fo:number-rational" "NumericKind" [],
    ctor "tptp-fo:number-real" "NumericKind" [],
    ctor "tptp-fo:term-variable" "Term" [("variable", "VariableId")],
    ctor "tptp-fo:term-function" "Term"
      [("function", "SymbolName"), ("arguments", "Terms")],
    ctor "tptp-fo:term-number" "Term"
      [("kind", "NumericKind"), ("lexeme", "String")],
    ctor "tptp-fo:term-distinct" "Term" [("lexeme", "String")],
    ctor "tptp-fo:terms-nil" "Terms" [],
    ctor "tptp-fo:terms-cons" "Terms"
      [("first", "Term"), ("rest", "Terms")],
    ctor "tptp-fo:atom-predicate" "Atom"
      [("predicate", "SymbolName"), ("arguments", "Terms")],
    ctor "tptp-fo:atom-equality" "Atom"
      [("left", "Term"), ("right", "Term")],

    ctor "tptp-fo:formula-atom" "Formula" [("atom", "Atom")],
    ctor "tptp-fo:formula-not" "Formula" [("body", "Formula")],
    ctor "tptp-fo:formula-and" "Formula"
      [("left", "Formula"), ("right", "Formula")],
    ctor "tptp-fo:formula-or" "Formula"
      [("left", "Formula"), ("right", "Formula")],
    ctor "tptp-fo:formula-iff" "Formula"
      [("left", "Formula"), ("right", "Formula")],
    ctor "tptp-fo:formula-implies" "Formula"
      [("left", "Formula"), ("right", "Formula")],
    ctor "tptp-fo:formula-reverse-implies" "Formula"
      [("left", "Formula"), ("right", "Formula")],
    ctor "tptp-fo:formula-xor" "Formula"
      [("left", "Formula"), ("right", "Formula")],
    ctor "tptp-fo:formula-nor" "Formula"
      [("left", "Formula"), ("right", "Formula")],
    ctor "tptp-fo:formula-nand" "Formula"
      [("left", "Formula"), ("right", "Formula")],
    ctor "tptp-fo:formula-forall" "Formula"
      [("variables", "Variables"), ("body", "Formula")],
    ctor "tptp-fo:formula-exists" "Formula"
      [("variables", "Variables"), ("body", "Formula")],

    ctor "tptp-fo:syntax-atom" "SyntaxNode" [("value", "String")],
    ctor "tptp-fo:syntax-string" "SyntaxNode" [("value", "String")],
    ctor "tptp-fo:syntax-integer" "SyntaxNode" [("value", "Integer")],
    ctor "tptp-fo:syntax-list" "SyntaxNode" [("items", "SyntaxNodes")],
    ctor "tptp-fo:syntax-nodes-nil" "SyntaxNodes" [],
    ctor "tptp-fo:syntax-nodes-cons" "SyntaxNodes"
      [("first", "SyntaxNode"), ("rest", "SyntaxNodes")],
    ctor "tptp-fo:annotation-none" "Annotation" [],
    ctor "tptp-fo:annotation-tree" "Annotation" [("tree", "SyntaxNode")],
    ctor "tptp-fo:source-span" "SourceSpan"
      [("start", "Integer"), ("stop", "Integer")],
    ctor "tptp-fo:source-span-unknown" "SourceSpan" [],

    ctor "tptp-fo:include-all" "IncludeSelection" [],
    ctor "tptp-fo:include-names" "IncludeSelection"
      [("names", "FormulaNames")],
    ctor "tptp-fo:formula-input" "Input"
      [("occurrence", "OccurrenceId"), ("dialect", "Dialect"),
       ("name", "FormulaName"), ("role", "Role"), ("formula", "Formula"),
       ("annotation", "Annotation"), ("span", "SourceSpan")],
    ctor "tptp-fo:include-input" "Input"
      [("occurrence", "OccurrenceId"), ("path", "SymbolName"),
       ("selection", "IncludeSelection"),
       ("qualifier", "OptionalFormulaName"), ("span", "SourceSpan")],
    ctor "tptp-fo:inputs-nil" "Inputs" [],
    ctor "tptp-fo:inputs-cons" "Inputs"
      [("first", "Input"), ("rest", "Inputs")],
    ctor "tptp-fo:document" "Document"
      [("source", "SourceDigest"), ("inputs", "Inputs")]
  ]
  equations := []
  rewrites := []
}

theorem language_validate : language.validate = [] := by
  decide +kernel

theorem language_inventory :
    language.types.length = 27 ∧ language.terms.length = 60 ∧
      language.rewrites.length = 0 := by
  decide

theorem atom_formula_crossing :
    ("tptp-fo:formula-atom", "Atom", "Formula") ∈
      unaryCrossings language := by
  decide

theorem symbol_formula_name_crossing :
    ("tptp-fo:formula-name-atomic", "SymbolName", "FormulaName") ∈
      unaryCrossings language := by
  decide

theorem no_unscoped_variable_formula_crossing :
    ("tptp-fo:invented-variable-formula", "VariableName", "Formula") ∉
      unaryCrossings language := by
  decide

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

def oslf := langOSLF language "Document"

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

#print axioms language_validate
#print axioms atom_formula_crossing
#print axioms symbol_formula_name_crossing
#print axioms no_unscoped_variable_formula_crossing
#print axioms theory_no_step
#print axioms galois
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFirstOrderDocument
