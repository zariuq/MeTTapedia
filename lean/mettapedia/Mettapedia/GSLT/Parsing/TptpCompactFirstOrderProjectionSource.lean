import Mettapedia.GSLT.Parsing.TptpOfficialCompositionSource
import Mettapedia.GSLT.LanguageDef.TptpFirstOrderDocument
import Mathlib.Tactic

/-!
# Source-connected compact TPTP first-order projection

The public first-order view selects FOF, CNF, and include records from an
ordered compact-record stream.  Every source record advances the occurrence
counter, including records outside the first-order view.  Consequently a
variable scope and an include identity refer to the record's position in the
source document rather than to its position in a filtered output.

This module gives the top-level projection a direct typed semantics.  It
proves ordered filtering, exact occurrence assignment, preservation of source
metadata, duplicate preservation, and reflection of every projected value to
the supported compact record from which it came.  Formula payloads remain
source-shaped values paired with their occurrence scope.  The final section
quotes the live authored presentation and checks the document, stream,
formula, span, annotation, and include clauses used by that semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TptpCompactFirstOrderProjectionSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing.TptpOfficialCompositionSource
  (Span app equation?)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

structure Occurrence where
  digest : String
  index : Nat
  deriving DecidableEq, Repr

inductive Dialect where
  | fof
  | cnf
  deriving DecidableEq, Repr

inductive CompactInput where
  | fof (name role formula annotation : SExpr) (span : Span)
  | cnf (name role formula annotation : SExpr) (span : Span)
  | include (path selection qualifier : SExpr) (span : Span)
  | tff (value : SExpr)
  | thf (value : SExpr)
  | tcf (value : SExpr)
  | tpi (value : SExpr)
  deriving DecidableEq, Repr

structure ScopedFormula where
  source : SExpr
  scope : Occurrence
  deriving DecidableEq, Repr

inductive PublicInput where
  | formula (occurrence : Occurrence) (dialect : Dialect)
      (name role : SExpr) (formula : ScopedFormula)
      (annotation : SExpr) (span : Span)
  | include (occurrence : Occurrence) (path selection qualifier : SExpr)
      (span : Span)
  deriving DecidableEq, Repr

def PublicInput.occurrence : PublicInput → Occurrence
  | .formula occurrence _ _ _ _ _ _ => occurrence
  | .include occurrence _ _ _ _ => occurrence

def supported : CompactInput → Bool
  | .fof _ _ _ _ _ | .cnf _ _ _ _ _ | .include _ _ _ _ => true
  | .tff _ | .thf _ | .tcf _ | .tpi _ => false

def projectOne (digest : String) (index : Nat) :
    CompactInput → Option PublicInput
  | .fof name role formula annotation span =>
      let occurrence := { digest, index }
      some (.formula occurrence .fof name role
        { source := formula, scope := occurrence } annotation span)
  | .cnf name role formula annotation span =>
      let occurrence := { digest, index }
      some (.formula occurrence .cnf name role
        { source := formula, scope := occurrence } annotation span)
  | .include path selection qualifier span =>
      some (.include { digest, index } path selection qualifier span)
  | .tff _ | .thf _ | .tcf _ | .tpi _ => none

def projectInputs (digest : String) : Nat → List CompactInput → List PublicInput
  | _, [] => []
  | index, input :: tail =>
      match projectOne digest index input with
      | some projected => projected :: projectInputs digest (index + 1) tail
      | none => projectInputs digest (index + 1) tail

def supportedInputs : List CompactInput → List CompactInput
  | [] => []
  | input :: tail =>
      if supported input then input :: supportedInputs tail
      else supportedInputs tail

def PublicInput.erase : PublicInput → CompactInput
  | .formula _ Dialect.fof name role body annotation span =>
      .fof name role body.source annotation span
  | .formula _ Dialect.cnf name role body annotation span =>
      .cnf name role body.source annotation span
  | .include _ path selection qualifier span =>
      .include path selection qualifier span

def selectedOccurrences (digest : String) : Nat → List CompactInput → List Occurrence
  | _, [] => []
  | index, input :: tail =>
      if supported input then
        { digest, index } :: selectedOccurrences digest (index + 1) tail
      else
        selectedOccurrences digest (index + 1) tail

theorem projectInputs_append (digest : String) (start : Nat)
    (first second : List CompactInput) :
    projectInputs digest start (first ++ second) =
      projectInputs digest start first ++
        projectInputs digest (start + first.length) second := by
  induction first generalizing start with
  | nil => simp [projectInputs]
  | cons input tail ih =>
      have nextStart : start + 1 + tail.length = start + (tail.length + 1) := by
        omega
      cases input <;>
        simp only [List.cons_append, projectInputs, projectOne,
          List.length_cons, List.cons_append, ih, nextStart]

theorem erase_projectInputs (digest : String) (start : Nat)
    (inputs : List CompactInput) :
    (projectInputs digest start inputs).map PublicInput.erase =
      supportedInputs inputs := by
  induction inputs generalizing start with
  | nil => rfl
  | cons input tail ih =>
      cases input <;>
        simp [projectInputs, projectOne, PublicInput.erase, supportedInputs,
          supported, ih]

theorem occurrences_projectInputs (digest : String) (start : Nat)
    (inputs : List CompactInput) :
    (projectInputs digest start inputs).map PublicInput.occurrence =
      selectedOccurrences digest start inputs := by
  induction inputs generalizing start with
  | nil => rfl
  | cons input tail ih =>
      cases input <;>
        simp [projectInputs, projectOne, PublicInput.occurrence,
          selectedOccurrences, supported, ih]

theorem projected_value_reflects_to_supported_source
    (digest : String) (start : Nat) (inputs : List CompactInput)
    (projected : PublicInput)
    (member : projected ∈ projectInputs digest start inputs) :
    projected.erase ∈ supportedInputs inputs := by
  have mapped : projected.erase ∈
      (projectInputs digest start inputs).map PublicInput.erase :=
    List.mem_map.mpr ⟨projected, member, rfl⟩
  simpa [erase_projectInputs] using mapped

def PublicInput.scopeCorrect : PublicInput → Prop
  | .formula occurrence _ _ _ body _ _ => body.scope = occurrence
  | .include _ _ _ _ _ => True

theorem projected_formula_scope_is_occurrence
    {digest : String} {index : Nat} {input : CompactInput}
    {projected : PublicInput}
    (projection : projectOne digest index input = some projected) :
    projected.scopeCorrect := by
  cases input <;> simp [projectOne] at projection
  all_goals (subst projected; simp [PublicInput.scopeCorrect])

theorem fof_metadata_preserved (digest : String) (index : Nat)
    (name role formula annotation : SExpr) (span : Span) :
    projectOne digest index (.fof name role formula annotation span) =
      some (.formula { digest, index } .fof name role
        { source := formula, scope := { digest, index } } annotation span) := rfl

theorem cnf_metadata_preserved (digest : String) (index : Nat)
    (name role formula annotation : SExpr) (span : Span) :
    projectOne digest index (.cnf name role formula annotation span) =
      some (.formula { digest, index } .cnf name role
        { source := formula, scope := { digest, index } } annotation span) := rfl

theorem include_metadata_preserved (digest : String) (index : Nat)
    (path selection qualifier : SExpr) (span : Span) :
    projectOne digest index (.include path selection qualifier span) =
      some (.include { digest, index } path selection qualifier span) := rfl

theorem duplicate_occurrences_remain_distinct (digest : String) (start : Nat)
    (name role formula annotation : SExpr) (span : Span) :
    (projectInputs digest start
      [.fof name role formula annotation span,
       .fof name role formula annotation span]).map PublicInput.occurrence =
      [{ digest, index := start }, { digest, index := start + 1 }] := by
  rfl

theorem skipped_input_still_advances_occurrence (digest : String) (start : Nat)
    (skipped name role formula annotation : SExpr) (span : Span) :
    projectInputs digest start
      [.tff skipped, .fof name role formula annotation span] =
      [.formula { digest, index := start + 1 } .fof name role
        { source := formula, scope := { digest, index := start + 1 } }
        annotation span] := by
  rfl

/-! ## Exact authored-source qualification contract -/

def AuthoredProjectionSourceExact (projectionSyntax : SExpr) : Prop :=
    equation? projectionSyntax 0 =
    some
      (app "tptp-view-v1:first-order-document"
        [app "TPTP:SourceDocument"
          [.atom "?identity", .atom "?digest", .atom "?text",
           app "tptp-rec:file" [.atom "?inputs", .atom "?file-span"]]],
       app "tptp-fo:document"
        [app "tptp-fo:source-digest" [.atom "?digest"],
         app "tptp-view-v1:fo-inputs"
          [.atom "?inputs", .atom "?digest", .atom "0"]]) ∧
    equation? projectionSyntax 3 =
    some
      (app "tptp-view-v1:fo-inputs"
        [app "tptp-rec:inputs-cons"
          [app "tptp-rec:fof"
            [.atom "?name", .atom "?role", .atom "?formula",
             .atom "?annotation", .atom "?span"], .atom "?tail"],
         .atom "?digest", .atom "?index"],
       app "tptp-fo:inputs-cons"
        [app "tptp-view-v1:fo-input"
          [app "tptp-rec:fof"
            [.atom "?name", .atom "?role", .atom "?formula",
             .atom "?annotation", .atom "?span"],
           .atom "?digest", .atom "?index"],
         app "tptp-view-v1:fo-inputs"
          [.atom "?tail", .atom "?digest",
           app "+" [.atom "?index", .atom "1"]]]) ∧
    equation? projectionSyntax 6 =
    some
      (app "tptp-view-v1:fo-inputs"
        [app "tptp-rec:inputs-cons"
          [app "tptp-rec:tff"
            [.atom "?a", .atom "?b", .atom "?c", .atom "?d", .atom "?e"],
           .atom "?tail"], .atom "?digest", .atom "?index"],
       app "tptp-view-v1:fo-inputs"
        [.atom "?tail", .atom "?digest",
         app "+" [.atom "?index", .atom "1"]]) ∧
    equation? projectionSyntax 10 =
    some
      (app "tptp-view-v1:fo-input"
        [app "tptp-rec:fof"
          [.atom "?name", .atom "?role", .atom "?formula",
           .atom "?annotation", .atom "?span"],
         .atom "?digest", .atom "?index"],
       app "tptp-fo:formula-input"
        [app "tptp-fo:occurrence"
          [app "tptp-fo:source-digest" [.atom "?digest"], .atom "?index"],
         app "tptp-fo:dialect-fof" [],
         app "tptp-view-v1:fo-name" [.atom "?name"],
         app "tptp-view-v1:fo-role" [.atom "?role"],
         app "tptp-view-v1:fo-formula"
          [.atom "?formula",
           app "tptp-fo:occurrence"
            [app "tptp-fo:source-digest" [.atom "?digest"], .atom "?index"]],
         app "tptp-view-v1:fo-annotation" [.atom "?annotation"],
         app "tptp-view-v1:fo-span" [.atom "?span"]]) ∧
    equation? projectionSyntax 12 =
    some
      (app "tptp-view-v1:fo-input"
        [app "tptp-rec:include"
          [.atom "?file", .atom "?selection", .atom "?qualifier", .atom "?span"],
         .atom "?digest", .atom "?index"],
       app "tptp-fo:include-input"
        [app "tptp-fo:occurrence"
          [app "tptp-fo:source-digest" [.atom "?digest"], .atom "?index"],
         app "tptp-view-v1:fo-include-path" [.atom "?file"],
         app "tptp-view-v1:fo-selection" [.atom "?selection"],
         app "tptp-view-v1:fo-qualifier" [.atom "?qualifier"],
         app "tptp-view-v1:fo-span" [.atom "?span"]]) ∧
    equation? projectionSyntax 44 =
    some
      (app "tptp-view-v1:fo-term"
        [app "tptp-rec:var"
          [app "tptp-rec:word-upper" [.atom "?name"]], .atom "?scope"],
       app "tptp-fo:term-variable"
        [app "tptp-fo:variable-id"
          [.atom "?scope", app "tptp-fo:variable-name" [.atom "?name"]]]) ∧
    equation? projectionSyntax 74 =
    some
      (app "tptp-view-v1:fo-formula"
        [app "tptp-rec:and" [.atom "?left", .atom "?right"], .atom "?scope"],
       app "tptp-fo:formula-and"
        [app "tptp-view-v1:fo-formula" [.atom "?left", .atom "?scope"],
         app "tptp-view-v1:fo-formula" [.atom "?right", .atom "?scope"]]) ∧
    equation? projectionSyntax 95 =
    some
      (app "tptp-view-v1:fo-span"
        [app "tptp-rec:span" [.atom "?start", .atom "?stop"]],
       app "tptp-fo:source-span" [.atom "?start", .atom "?stop"]) ∧
    equation? projectionSyntax 98 =
    some
      (app "tptp-view-v1:fo-annotation"
        [app "tptp-rec:annotation" [.atom "?source", .atom "?optional"]],
       app "tptp-fo:annotation-tree"
        [app "tptp-view-v1:fo-syntax"
          [app "tptp-view-v1:syntax"
            [app "tptp-rec:annotation" [.atom "?source", .atom "?optional"]]]])

#print axioms projectInputs_append
#print axioms erase_projectInputs
#print axioms occurrences_projectInputs
#print axioms projected_value_reflects_to_supported_source
#print axioms projected_formula_scope_is_occurrence
#print axioms duplicate_occurrences_remain_distinct
#print axioms skipped_input_still_advances_occurrence

end Mettapedia.GSLT.Parsing.TptpCompactFirstOrderProjectionSource
