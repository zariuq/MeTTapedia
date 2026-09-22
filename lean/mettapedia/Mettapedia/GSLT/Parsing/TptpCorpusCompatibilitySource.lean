import Mettapedia.GSLT.Parsing.PlainBnfStructuredValueCodec
import Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
import Mathlib.Tactic

/-!
# Source-connected TPTP corpus-compatibility refinement

The optional corpus-compatibility profile extends four rules of the pinned
official TPTP grammar.  Its NativeType program discovers each unique target as
a zipper over the complete structured grammar.  The transformation consumes
that zipper only after checking its target and reconstructing the carried
source.

This module gives that protocol a direct typed semantics.  It proves that a
successful judgment identifies the named rule in the exact source, that the
consumer preserves document/authority metadata and every non-target entry,
and that removing the known appended alternatives recovers the source.  The
final section selects the relevant equations from both live authored files, so
the model is tied to the programs used to construct the frozen reader.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TptpCorpusCompatibilitySource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
open Mettapedia.GSLT.Parsing.PlainBnfStructuredValueCodec
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def app (head : String) (arguments : List SExpr) : SExpr :=
  .list (.atom head :: arguments)

def equation? (authored : SExpr) (occurrence : Nat) : Option (SExpr × SExpr) := do
  let row ←
    Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.rawRewriteAt?
      authored occurrence
  match row.head, row.body with
  | .list [.atom "metta-equation", left, right], [] => some (left, right)
  | _, _ => none

structure GrammarInput where
  document : Document
  authority : GrammarAuthority
  deriving DecidableEq, Repr

structure RuleEntry where
  name : String
  expression : Expression
  span : SourceSpan
  deriving DecidableEq, Repr

namespace RuleEntry

def entry (rule : RuleEntry) : Entry :=
  .rule rule.name rule.expression rule.span

end RuleEntry

structure TargetJudgment where
  source : GrammarInput
  target : String
  prefixReverse : List Entry
  rule : RuleEntry
  suffix : List Entry
  deriving DecidableEq, Repr

inductive Discovery where
  | found (judgment : TargetJudgment)
  | missing (target : String)
  | duplicate (target : String)
  deriving DecidableEq, Repr

/-! ## Structural NativeType discovery -/

def scanAfter (target : String) (source : GrammarInput)
    (prefixReverse : List Entry) (selected : RuleEntry)
    (remaining suffix : List Entry) : Discovery :=
  match remaining with
  | [] => .found { source, target, prefixReverse, rule := selected, suffix }
  | .rule name _ _ :: tail =>
      if name = target then .duplicate target
      else scanAfter target source prefixReverse selected tail suffix
  | .comment _ _ :: tail =>
      scanAfter target source prefixReverse selected tail suffix
  | .blank _ :: tail =>
      scanAfter target source prefixReverse selected tail suffix
termination_by remaining.length

def scanBefore (target : String) (source : GrammarInput)
    (prefixReverse remaining : List Entry) : Discovery :=
  match remaining with
  | [] => .missing target
  | .rule name expression span :: tail =>
      if name = target then
        scanAfter target source prefixReverse { name, expression, span } tail tail
      else
        scanBefore target source
          (.rule name expression span :: prefixReverse) tail
  | .comment text span :: tail =>
      scanBefore target source (.comment text span :: prefixReverse) tail
  | .blank span :: tail =>
      scanBefore target source (.blank span :: prefixReverse) tail
termination_by remaining.length

def inferTarget (target : String) (source : GrammarInput) : Discovery :=
  scanBefore target source [] source.document.entries

def ruleMatches (target : String) : Entry → Bool
  | .rule name _ _ => name == target
  | .comment _ _ | .blank _ => false

def targetCount (target : String) (entries : List Entry) : Nat :=
  entries.countP (ruleMatches target)

@[simp] theorem scanAfter_found_iff_no_later_target
    (target : String) (source : GrammarInput) (prefixReverse : List Entry)
    (selected : RuleEntry) (remaining suffix : List Entry) :
    scanAfter target source prefixReverse selected remaining suffix =
        .found { source, target, prefixReverse, rule := selected, suffix } ↔
      targetCount target remaining = 0 := by
  induction remaining with
  | nil => simp [scanAfter, targetCount]
  | cons entry tail ih =>
      cases entry with
      | rule name expression span =>
          by_cases equal : name = target
          · simp [scanAfter, targetCount, ruleMatches, equal]
          · simp [scanAfter, targetCount, ruleMatches, equal, ih]
      | comment text span => simp [scanAfter, targetCount, ruleMatches, ih]
      | blank span => simp [scanAfter, targetCount, ruleMatches, ih]

theorem scanAfter_found_fields
    {target : String} {source : GrammarInput} {prefixReverse : List Entry}
    {selected : RuleEntry} {remaining suffix : List Entry}
    {judgment : TargetJudgment}
    (found : scanAfter target source prefixReverse selected remaining suffix =
      .found judgment) :
    judgment = { source, target, prefixReverse, rule := selected, suffix } := by
  induction remaining with
  | nil => simpa [scanAfter] using found.symm
  | cons entry tail ih =>
      cases entry with
      | rule name _expression _span =>
          by_cases equal : name = target
          · simp [scanAfter, equal] at found
          · apply ih
            simpa [scanAfter, equal] using found
      | comment _text _span =>
          apply ih
          simpa [scanAfter] using found
      | blank _span =>
          apply ih
          simpa [scanAfter] using found

theorem scanBefore_found_reconstruct
    {target : String} {source : GrammarInput} {prefixReverse remaining : List Entry}
    {judgment : TargetJudgment}
    (invariant : source.document.entries = prefixReverse.reverse ++ remaining)
    (found : scanBefore target source prefixReverse remaining = .found judgment) :
    judgment.source = source ∧ judgment.target = target ∧
      judgment.rule.name = target ∧
      source.document.entries =
        judgment.prefixReverse.reverse ++
          judgment.rule.entry :: judgment.suffix := by
  induction remaining generalizing prefixReverse with
  | nil => simp [scanBefore] at found
  | cons entry tail ih =>
      cases entry with
      | rule name expression span =>
          by_cases equal : name = target
          · rw [scanBefore, if_pos equal] at found
            have fields := scanAfter_found_fields found
            rcases fields with rfl
            refine ⟨rfl, rfl, equal, ?_⟩
            simpa [RuleEntry.entry, List.reverse_cons, List.append_assoc,
              equal] using invariant
          · rw [scanBefore, if_neg equal] at found
            apply ih (prefixReverse := .rule name expression span :: prefixReverse)
            · simpa [List.reverse_cons, List.append_assoc] using invariant
            · exact found
      | comment text span =>
          simp [scanBefore] at found
          apply ih (prefixReverse := .comment text span :: prefixReverse)
          · simpa [List.reverse_cons, List.append_assoc] using invariant
          · exact found
      | blank span =>
          simp [scanBefore] at found
          apply ih (prefixReverse := .blank span :: prefixReverse)
          · simpa [List.reverse_cons, List.append_assoc] using invariant
          · exact found

theorem inferTarget_found_reconstruct
    {target : String} {source : GrammarInput} {judgment : TargetJudgment}
    (found : inferTarget target source = .found judgment) :
    judgment.source = source ∧ judgment.target = target ∧
      judgment.rule.name = target ∧
      source.document.entries =
        judgment.prefixReverse.reverse ++
          judgment.rule.entry :: judgment.suffix := by
  apply scanBefore_found_reconstruct
    (prefixReverse := []) (remaining := source.document.entries)
  · simp
  · exact found

@[simp] theorem inferTarget_empty (target : String) (source : GrammarInput)
    (empty : source.document.entries = []) :
    inferTarget target source = .missing target := by
  simp [inferTarget, empty, scanBefore]

theorem inferTarget_duplicate_example
    (target : String) (source : GrammarInput)
    (first second : RuleEntry) (tail : List Entry)
    (firstName : first.name = target) (secondName : second.name = target)
    (entries : source.document.entries = first.entry :: second.entry :: tail) :
    inferTarget target source = .duplicate target := by
  simp [inferTarget, entries, scanBefore, scanAfter, RuleEntry.entry,
    firstName, secondName]

/-! ## NTT-consuming compatibility transform -/

def extendExpression (additions : List Alternative)
    (expression : Expression) : Expression :=
  { expression with alternatives := expression.alternatives ++ additions }

def extendRule (additions : List Alternative) (rule : RuleEntry) : RuleEntry :=
  { rule with expression := extendExpression additions rule.expression }

def reconstructedEntries (judgment : TargetJudgment) : List Entry :=
  judgment.prefixReverse.reverse ++ judgment.rule.entry :: judgment.suffix

def extendedEntries (additions : List Alternative)
    (judgment : TargetJudgment) : List Entry :=
  judgment.prefixReverse.reverse ++
    (extendRule additions judgment.rule).entry :: judgment.suffix

def consumeJudgment (additions : List Alternative)
    (judgment : TargetJudgment) : Option GrammarInput :=
  if judgment.target = judgment.rule.name ∧
      judgment.source.document.entries = reconstructedEntries judgment then
    some {
      document := {
        entries := extendedEntries additions judgment
        span := judgment.source.document.span }
      authority := judgment.source.authority }
  else
    none

theorem consumeJudgment_of_inferred
    {target : String} {source : GrammarInput} {judgment : TargetJudgment}
    (found : inferTarget target source = .found judgment)
    (additions : List Alternative) :
    consumeJudgment additions judgment = some {
      document := {
        entries := extendedEntries additions judgment
        span := source.document.span }
      authority := source.authority } := by
  obtain ⟨sourceExact, targetExact, nameExact, reconstruct⟩ :=
    inferTarget_found_reconstruct found
  simp [consumeJudgment, reconstructedEntries, targetExact, nameExact,
    reconstruct, sourceExact]

theorem consume_preserves_authority
    {additions : List Alternative} {judgment : TargetJudgment}
    {output : GrammarInput}
    (consumed : consumeJudgment additions judgment = some output) :
    output.authority = judgment.source.authority := by
  simp [consumeJudgment] at consumed
  rcases consumed with ⟨_, rfl⟩
  rfl

theorem consume_preserves_document_span
    {additions : List Alternative} {judgment : TargetJudgment}
    {output : GrammarInput}
    (consumed : consumeJudgment additions judgment = some output) :
    output.document.span = judgment.source.document.span := by
  simp [consumeJudgment] at consumed
  rcases consumed with ⟨_, rfl⟩
  rfl

theorem consume_preserves_non_target_entries
    {additions : List Alternative} {judgment : TargetJudgment}
    {output : GrammarInput}
    (consumed : consumeJudgment additions judgment = some output) :
    output.document.entries =
      judgment.prefixReverse.reverse ++
        (extendRule additions judgment.rule).entry :: judgment.suffix := by
  simp [consumeJudgment, extendedEntries] at consumed
  rcases consumed with ⟨_, rfl⟩
  rfl

@[simp] theorem extendRule_name (additions : List Alternative)
    (rule : RuleEntry) : (extendRule additions rule).name = rule.name := rfl

@[simp] theorem extendRule_span (additions : List Alternative)
    (rule : RuleEntry) : (extendRule additions rule).span = rule.span := rfl

@[simp] theorem extendRule_expression_span (additions : List Alternative)
    (rule : RuleEntry) :
    (extendRule additions rule).expression.span = rule.expression.span := rfl

@[simp] theorem extendRule_alternatives (additions : List Alternative)
    (rule : RuleEntry) :
    (extendRule additions rule).expression.alternatives =
      rule.expression.alternatives ++ additions := rfl

/-! ## A structural inverse (reflection) -/

def stripPrefix {α : Type} [DecidableEq α] : List α → List α → Option (List α)
  | [], values => some values
  | expected :: expectedTail, value :: valueTail =>
      if expected = value then stripPrefix expectedTail valueTail else none
  | _ :: _, [] => none

@[simp] theorem stripPrefix_append {α : Type} [DecidableEq α]
    (expected values : List α) :
    stripPrefix expected (expected ++ values) = some values := by
  induction expected with
  | nil => rfl
  | cons head tail ih => simp [stripPrefix, ih]

def removeSuffix {α : Type} [DecidableEq α]
    (suffix values : List α) : Option (List α) := do
  let reversePrefix ← stripPrefix suffix.reverse values.reverse
  some reversePrefix.reverse

@[simp] theorem removeSuffix_append {α : Type} [DecidableEq α]
    (values suffix : List α) :
    removeSuffix suffix (values ++ suffix) = some values := by
  simp [removeSuffix, List.reverse_append]

def unextendExpression (additions : List Alternative)
    (expression : Expression) : Option Expression := do
  let original ← removeSuffix additions expression.alternatives
  some { alternatives := original, span := expression.span }

def unextendRule (additions : List Alternative)
    (rule : RuleEntry) : Option RuleEntry := do
  let original ← unextendExpression additions rule.expression
  some { name := rule.name, expression := original, span := rule.span }

@[simp] theorem unextendRule_extendRule (additions : List Alternative)
    (rule : RuleEntry) :
    unextendRule additions (extendRule additions rule) = some rule := by
  cases rule with
  | mk name expression span =>
      cases expression
      simp [unextendRule, unextendExpression, extendRule, extendExpression]

def reflectAtJudgment (additions : List Alternative)
    (judgment : TargetJudgment) (output : GrammarInput) : Option GrammarInput := do
  if output.authority != judgment.source.authority ∨
      output.document.span != judgment.source.document.span then
    none
  else
    let frontLength := judgment.prefixReverse.length
    let (front, rest) := output.document.entries.splitAt frontLength
    if front != judgment.prefixReverse.reverse then
      none
    else
      match rest with
      | .rule name expression span :: suffix =>
          if suffix != judgment.suffix then none
          else do
            let original ← unextendRule additions { name, expression, span }
            some {
              document := {
                entries := front ++ original.entry :: suffix
                span := output.document.span }
              authority := output.authority }
      | _ => none

theorem reflectAtJudgment_consume
    {target : String} {source : GrammarInput} {judgment : TargetJudgment}
    (found : inferTarget target source = .found judgment)
    (additions : List Alternative) :
    (consumeJudgment additions judgment).bind
        (reflectAtJudgment additions judgment) = some source := by
  obtain ⟨sourceExact, targetExact, nameExact, reconstruct⟩ :=
    inferTarget_found_reconstruct found
  have restored :
      unextendRule additions {
        name := judgment.rule.name
        expression := (extendRule additions judgment.rule).expression
        span := judgment.rule.span } = some judgment.rule := by
    simpa [extendRule] using unextendRule_extendRule additions judgment.rule
  have rebuilt :
      ({
        document := {
          entries := judgment.prefixReverse.reverse ++
            .rule judgment.rule.name judgment.rule.expression judgment.rule.span ::
              judgment.suffix
          span := source.document.span }
        authority := source.authority } : GrammarInput) = source := by
    cases source with
    | mk document authority =>
        cases document with
        | mk entries span => simp_all [RuleEntry.entry]
  rw [consumeJudgment_of_inferred found]
  simp only [Option.bind_some]
  simp [reflectAtJudgment, extendedEntries, List.splitAt_eq, RuleEntry.entry,
    sourceExact, restored, rebuilt]

theorem extendRule_injective (additions : List Alternative) :
    Function.Injective (extendRule additions) := by
  intro first second equal
  have reflected := congrArg (unextendRule additions) equal
  simpa using reflected

/-! ## Exact authored-source qualification contract -/

def sourceString (value : String) : SExpr :=
  .atom ("\"" ++ value ++ "\"")

def sourceText (value : String) : SExpr :=
  app "bnf-v1:string->text" [sourceString value]

def planNil : SExpr := app "tptp-corpus-v1:plan-nil" []

def planCons (target kind : String) (tail : SExpr) : SExpr :=
  app "tptp-corpus-v1:plan-cons" [sourceText target, .atom kind, tail]

def compatibilityPlan : SExpr :=
  planCons "tff_unitary_term" "tptp-corpus-v1:tff-prefix-term"
    (planCons "internal_source" "tptp-corpus-v1:introduced-two-arguments"
      (planCons "nhf_parameter" "tptp-corpus-v1:nhf-bare-parameter"
        (planCons "cnf_disjunction"
          "tptp-corpus-v1:parenthesized-cnf-infix-in-disjunction" planNil)))

def AuthoredCompatibilitySourceExact
    (nativeTypeSyntax compatibilitySyntax : SExpr) : Prop :=
    equation? compatibilitySyntax 0 =
    some
      (app "tptp-corpus-v1:extend-formula-terms" [.atom "?input"],
       app "tptp-corpus-v1:profile" [.atom "?input", compatibilityPlan]) ∧
    equation? nativeTypeSyntax 0 =
    some
      (app "tptp-corpus-ntt-v1:infer" [.atom "?target",
        app "bnf-v1:grammar-input"
          [app "bnf-v1:document" [.atom "?entries", .atom "?document-span"],
            .atom "?authority"]],
       app "tptp-corpus-ntt-v1:scan-before"
          [.atom "?target",
            app "bnf-v1:grammar-input"
              [app "bnf-v1:document" [.atom "?entries", .atom "?document-span"],
                .atom "?authority"],
            app "bnf-v1:entries-nil" [], .atom "?entries"]) ∧
    equation? nativeTypeSyntax 7 =
    some
      (app "tptp-corpus-ntt-v1:scan-after"
          [.atom "?target", .atom "?source", .atom "?prefix-reverse",
            .atom "?rule", app "bnf-v1:entries-nil" [], .atom "?suffix"],
       app "TPTP:CorpusCompatibilityTargetNativeTypeV1"
          [.atom "?source", .atom "?target", .atom "?prefix-reverse",
            .atom "?rule", .atom "?suffix"]) ∧
    equation? nativeTypeSyntax 12 =
    some
      (app "tptp-corpus-ntt-v1:scan-after-entry"
          [.atom "LangDef:SameValue", .atom "?target", .atom "?source",
            .atom "?prefix-reverse", .atom "?target-rule", .atom "?tail",
            .atom "?suffix"],
       app "TPTP:CorpusCompatibilityTargetDuplicateV1" [.atom "?target"]) ∧
    equation? compatibilitySyntax 2 =
    some
      (app "tptp-corpus-v1:profile"
          [.atom "?input",
            app "tptp-corpus-v1:plan-cons"
              [.atom "?target", .atom "?kind", .atom "?tail"]],
       app "tptp-corpus-v1:after-discovery"
          [app "tptp-corpus-ntt-v1:infer" [.atom "?target", .atom "?input"],
            .atom "?kind", .atom "?tail"]) ∧
    equation? compatibilitySyntax 3 =
    some
      (app "tptp-corpus-v1:after-discovery"
          [app "TPTP:CorpusCompatibilityTargetNativeTypeV1"
            [.atom "?source", .atom "?target", .atom "?prefix-reverse",
              .atom "?rule", .atom "?suffix"],
            .atom "?kind", .atom "?tail"],
       app "tptp-corpus-v1:after-extension"
          [app "tptp-corpus-v1:consume"
            [.atom "?kind",
              app "TPTP:CorpusCompatibilityTargetNativeTypeV1"
                [.atom "?source", .atom "?target", .atom "?prefix-reverse",
                  .atom "?rule", .atom "?suffix"]],
            .atom "?tail"])

#print axioms inferTarget_found_reconstruct
#print axioms consumeJudgment_of_inferred
#print axioms consume_preserves_non_target_entries
#print axioms reflectAtJudgment_consume
#print axioms extendRule_injective

end Mettapedia.GSLT.Parsing.TptpCorpusCompatibilitySource
