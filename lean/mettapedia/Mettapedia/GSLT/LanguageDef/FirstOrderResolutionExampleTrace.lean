import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.FirstOrderResolutionInput

/-!
# Private trace data for the first-order resolution example

This inert carrier is the private trace boundary of CeTTa's first-order
resolution example.  It is a glued extension of the resolution input presentation: the
nineteen input types and thirty-one input constructors are re-declared here
verbatim, in the same order and with the same field names, and the proof
structure is appended after them.  An embedded literal inside a certificate is
therefore literally a `fo-resolution:` value.  There is deliberately no second
spelling of terms, atoms, or literals, so no second interpretation of clause
data can ever drift from the first.

A certificate is data.  This language performs no search, supplies no unifier,
and has no reduction: a `Step` records the derived clause identity it
concludes, its two parents, and the resulting literal list.  Each parent names
which clause it is, which literal position within that clause is resolved upon
after the parent's substitution has been applied, and the substitution applied
to that parent.

Two independent per-parent substitutions are recorded rather than one shared
most-general unifier.  Each parent clause is universally quantified over its
own variables, so instantiating the two parents independently is sound, and it
removes any need for a separate standardization-apart step.  Nothing here is
trusted: a separate checker recomputes each resolvent from the recorded
parents and substitutions and compares it against the recorded literals.

Search policy, unification, and trace checking are separate authored MeTTa
example programs; they are not claimed here as GSLTs or as TPTP semantics.
This language supplies neither an implicit unifier nor a native arithmetic or
ATP oracle.
-/

namespace Mettapedia.GSLT.LanguageDef.FirstOrderResolutionExampleTrace

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

/-- Checked resolution certificates over the unchanged resolution input
presentation. -/
def language : LanguageDef := {
  name := "FirstOrderResolutionExampleTrace"
  types := [
    { name := "String", carrier := .builtinString },
    { name := "Integer", carrier := .builtinInt },
    "SourceDigest", "OccurrenceId", "FormulaName", "Role",
    "SymbolKind", "SymbolName", "VariableName", "VariableId",
    "NumericKind", "Term", "Terms", "Atom", "Literal", "Literals",
    "Clause", "Clauses", "Problem",
    "ClauseId", "Binding", "Bindings", "Substitution",
    "Parent", "Step", "Steps", "Certificate"]
  terms := [
    ctor "fo-resolution:source-digest" "SourceDigest" [("value", "String")],
    ctor "fo-resolution:occurrence" "OccurrenceId"
      [("source", "SourceDigest"), ("index", "Integer")],
    ctor "fo-resolution:formula-name-atomic" "FormulaName"
      [("value", "SymbolName")],
    ctor "fo-resolution:formula-name-integer" "FormulaName"
      [("lexeme", "String")],
    ctor "fo-resolution:role" "Role" [("base", "String")],

    ctor "fo-resolution:symbol-lower" "SymbolKind" [],
    ctor "fo-resolution:symbol-quoted" "SymbolKind" [],
    ctor "fo-resolution:symbol-defined" "SymbolKind" [],
    ctor "fo-resolution:symbol-system" "SymbolKind" [],
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
      [("source", "SourceDigest"), ("clauses", "Clauses")],

    ctor "fo-proof:input-clause" "ClauseId" [("occurrence", "OccurrenceId")],
    ctor "fo-proof:derived-clause" "ClauseId" [("index", "Integer")],

    ctor "fo-proof:binding" "Binding"
      [("variable", "VariableId"), ("term", "Term")],
    ctor "fo-proof:bindings-nil" "Bindings" [],
    ctor "fo-proof:bindings-cons" "Bindings"
      [("first", "Binding"), ("rest", "Bindings")],
    ctor "fo-proof:substitution" "Substitution" [("bindings", "Bindings")],

    ctor "fo-proof:parent" "Parent"
      [("clause", "ClauseId"), ("index", "Integer"),
       ("substitution", "Substitution")],
    ctor "fo-proof:step" "Step"
      [("conclusion", "ClauseId"), ("left", "Parent"),
       ("right", "Parent"), ("literals", "Literals")],
    ctor "fo-proof:steps-nil" "Steps" [],
    ctor "fo-proof:steps-cons" "Steps"
      [("first", "Step"), ("rest", "Steps")],
    ctor "fo-proof:certificate" "Certificate"
      [("source", "SourceDigest"), ("steps", "Steps"),
       ("empty", "ClauseId")]
  ]
  equations := []
  rewrites := []
}

theorem language_validate : language.validate = [] := by
  decide +kernel

theorem language_inventory :
    language.types.length = 27 ∧ language.terms.length = 42 ∧
      language.rewrites.length = 0 := by
  decide

/-! ## The resolution input presentation is included unchanged -/

theorem resolution_input_terms_included :
    ∀ rule ∈ FirstOrderResolutionInput.language.terms,
      rule ∈ language.terms := by
  decide +kernel

theorem resolution_input_types_included :
    ∀ declaration ∈ FirstOrderResolutionInput.language.types,
      declaration ∈ language.types := by
  decide

private def certificateRule : GrammarRule :=
  ctor "fo-proof:certificate" "Certificate"
    [("source", "SourceDigest"), ("steps", "Steps"), ("empty", "ClauseId")]

/-- Non-vacuity companion: the rejected constructor really is authored here. -/
theorem certificate_constructor_mem : certificateRule ∈ language.terms := by
  decide +kernel

/-- The extension is strict.  Cross-language rejection at presentation level:
a resolution input document can never carry a certificate. -/
theorem certificate_constructor_not_in_resolution_input :
    certificateRule ∉ FirstOrderResolutionInput.language.terms := by
  decide

/-! ## Sort crossings -/

theorem occurrence_clause_id_crossing :
    ("fo-proof:input-clause", "OccurrenceId", "ClauseId") ∈
      unaryCrossings language := by
  decide

theorem bindings_substitution_crossing :
    ("fo-proof:substitution", "Bindings", "Substitution") ∈
      unaryCrossings language := by
  decide

/-- A certificate cannot assert a resolvent without naming its parents: there
is deliberately no constructor taking a literal list straight to a step. -/
theorem no_unchecked_resolvent_crossing :
    ("fo-proof:unchecked-resolvent", "Literals", "Step") ∉
      unaryCrossings language := by
  decide

/-- Certificates are data.  Checking them belongs to another presentation. -/
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

def oslf := langOSLF language "Certificate"

theorem galois :
    GaloisConnection (langDiamond language) (langBox language) :=
  langGalois language

/-! ## Step identity is not collapsed -/

private def demoSource : Pattern :=
  a "fo-resolution:source-digest" [a "fo-proof:demo-digest"]
private def demoOccurrence : Pattern :=
  a "fo-resolution:occurrence" [demoSource, a "fo-proof:first-index"]
private def demoVariable : Pattern :=
  a "fo-resolution:variable-id"
    [demoOccurrence,
     a "fo-resolution:variable-name" [a "fo-proof:demo-variable-name"]]
private def demoTerm : Pattern :=
  a "fo-resolution:term-variable" [demoVariable]

private def inputClause : Pattern :=
  a "fo-proof:input-clause" [demoOccurrence]
private def derivedClause : Pattern :=
  a "fo-proof:derived-clause" [a "fo-proof:second-index"]
private def demoConclusion : Pattern :=
  a "fo-proof:derived-clause" [a "fo-proof:first-index"]

private def identitySubstitution : Pattern :=
  a "fo-proof:substitution" [a "fo-proof:bindings-nil"]
private def instantiatingSubstitution : Pattern :=
  a "fo-proof:substitution"
    [a "fo-proof:bindings-cons"
      [a "fo-proof:binding" [demoVariable, demoTerm],
       a "fo-proof:bindings-nil"]]

private def leftParentIdentity : Pattern :=
  a "fo-proof:parent"
    [inputClause, a "fo-proof:first-index", identitySubstitution]
private def leftParentInstantiated : Pattern :=
  a "fo-proof:parent"
    [inputClause, a "fo-proof:first-index", instantiatingSubstitution]
private def rightParentInput : Pattern :=
  a "fo-proof:parent"
    [inputClause, a "fo-proof:second-index", identitySubstitution]
private def rightParentDerived : Pattern :=
  a "fo-proof:parent"
    [derivedClause, a "fo-proof:second-index", identitySubstitution]
private def demoLiterals : Pattern := a "fo-resolution:literals-nil"

/-- The substitution recorded for a parent is part of the step's identity. -/
theorem steps_differing_in_substitution_are_distinct :
    a "fo-proof:step"
        [demoConclusion, leftParentIdentity, rightParentInput, demoLiterals] ≠
      a "fo-proof:step"
        [demoConclusion, leftParentInstantiated, rightParentInput,
         demoLiterals] := by
  decide

/-- Which clause a parent names is part of the step's identity. -/
theorem steps_differing_in_parent_identity_are_distinct :
    a "fo-proof:step"
        [demoConclusion, leftParentIdentity, rightParentInput, demoLiterals] ≠
      a "fo-proof:step"
        [demoConclusion, leftParentIdentity, rightParentDerived,
         demoLiterals] := by
  decide

/-! ## Canonical wire projection -/

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
#print axioms resolution_input_terms_included
#print axioms resolution_input_types_included
#print axioms certificate_constructor_mem
#print axioms certificate_constructor_not_in_resolution_input
#print axioms occurrence_clause_id_crossing
#print axioms bindings_substitution_crossing
#print axioms no_unchecked_resolvent_crossing
#print axioms theory_no_step
#print axioms galois
#print axioms steps_differing_in_substitution_are_distinct
#print axioms steps_differing_in_parent_identity_are_distinct
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.FirstOrderResolutionExampleTrace
