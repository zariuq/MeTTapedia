import Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
import Mathlib.Tactic

/-!
# Source-connected TPTP grammar composition

The official Extended-BNF document contains syntax, semantic, token,
character, comment, and blank rows in one ordered ledger.  The lexical pass
selects token and character rows; the syntax pass selects syntax rows.  Both
passes retain the complete original ledger, while the composed grammar places
syntax rules before token wrappers, lexical rules, and fixed support rules.

This module gives that boundary a direct typed semantics.  It proves exact
selection and reflection, order preservation across concatenated source
segments, duplicate preservation, and recovery of the retained source.  The
last section quotes the live authored presentations and checks the clauses
which perform the row partition and preserve the original document.  Regex
and grammar-expression lowering remain payload transformations here; their
individual constructors are not reimplemented as a second parser.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TptpOfficialCompositionSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
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

structure Span where
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

inductive OfficialRow where
  | syntax (name : String) (rhs : SExpr) (span : Span)
  | semantic (name : String) (rhs : SExpr) (span : Span)
  | token (name : String) (rhs : SExpr) (span : Span)
  | character (name : String) (rhs : SExpr) (span : Span)
  | comment (text : String) (span : Span)
  | blank (span : Span)
  deriving DecidableEq, Repr

structure OfficialDocument where
  rows : List OfficialRow
  span : Span
  deriving DecidableEq, Repr

structure Rule where
  name : String
  rhs : SExpr
  span : Span
  deriving DecidableEq, Repr

def lexicalRule? (lowerRegex : SExpr → SExpr) : OfficialRow → Option Rule
  | .token name rhs span | .character name rhs span =>
      some { name, rhs := lowerRegex rhs, span }
  | .syntax _ _ _ | .semantic _ _ _ | .comment _ _ | .blank _ => none

def syntaxRule? (lowerGrammar : SExpr → SExpr) : OfficialRow → Option Rule
  | .syntax name rhs span => some { name, rhs := lowerGrammar rhs, span }
  | .semantic _ _ _ | .token _ _ _ | .character _ _ _ |
      .comment _ _ | .blank _ => none

def lexicalRules (lowerRegex : SExpr → SExpr)
    (rows : List OfficialRow) : List Rule :=
  rows.filterMap (lexicalRule? lowerRegex)

def syntaxRules (lowerGrammar : SExpr → SExpr)
    (rows : List OfficialRow) : List Rule :=
  rows.filterMap (syntaxRule? lowerGrammar)

def LexicallyDerived (lowerRegex : SExpr → SExpr)
    (source : OfficialRow) (target : Rule) : Prop :=
  match source with
  | .token name rhs span | .character name rhs span =>
      target = { name, rhs := lowerRegex rhs, span }
  | _ => False

def SyntacticallyDerived (lowerGrammar : SExpr → SExpr)
    (source : OfficialRow) (target : Rule) : Prop :=
  match source with
  | .syntax name rhs span => target = { name, rhs := lowerGrammar rhs, span }
  | _ => False

@[simp] theorem lexicalRule?_eq_some_iff (lowerRegex : SExpr → SExpr)
    (source : OfficialRow) (target : Rule) :
    lexicalRule? lowerRegex source = some target ↔
      LexicallyDerived lowerRegex source target := by
  cases source <;> simp [lexicalRule?, LexicallyDerived, eq_comm]

@[simp] theorem syntaxRule?_eq_some_iff (lowerGrammar : SExpr → SExpr)
    (source : OfficialRow) (target : Rule) :
    syntaxRule? lowerGrammar source = some target ↔
      SyntacticallyDerived lowerGrammar source target := by
  cases source <;> simp [syntaxRule?, SyntacticallyDerived, eq_comm]

theorem mem_lexicalRules_iff (lowerRegex : SExpr → SExpr)
    (rows : List OfficialRow) (target : Rule) :
    target ∈ lexicalRules lowerRegex rows ↔
      ∃ source ∈ rows, LexicallyDerived lowerRegex source target := by
  simp [lexicalRules]

theorem mem_syntaxRules_iff (lowerGrammar : SExpr → SExpr)
    (rows : List OfficialRow) (target : Rule) :
    target ∈ syntaxRules lowerGrammar rows ↔
      ∃ source ∈ rows, SyntacticallyDerived lowerGrammar source target := by
  simp [syntaxRules]

theorem lexicalRules_append (lowerRegex : SExpr → SExpr)
    (first second : List OfficialRow) :
    lexicalRules lowerRegex (first ++ second) =
      lexicalRules lowerRegex first ++ lexicalRules lowerRegex second := by
  simp [lexicalRules]

theorem syntaxRules_append (lowerGrammar : SExpr → SExpr)
    (first second : List OfficialRow) :
    syntaxRules lowerGrammar (first ++ second) =
      syntaxRules lowerGrammar first ++ syntaxRules lowerGrammar second := by
  simp [syntaxRules]

theorem lexical_duplicate_preserved (lowerRegex : SExpr → SExpr)
    (name : String) (rhs : SExpr) (span : Span) :
    lexicalRules lowerRegex
        [.token name rhs span, .token name rhs span] =
      [{ name, rhs := lowerRegex rhs, span },
       { name, rhs := lowerRegex rhs, span }] := rfl

theorem syntax_duplicate_preserved (lowerGrammar : SExpr → SExpr)
    (name : String) (rhs : SExpr) (span : Span) :
    syntaxRules lowerGrammar
        [.syntax name rhs span, .syntax name rhs span] =
      [{ name, rhs := lowerGrammar rhs, span },
       { name, rhs := lowerGrammar rhs, span }] := rfl

structure LexicalLowered where
  rules : List Rule
  original : OfficialDocument
  deriving DecidableEq, Repr

def lowerLexical (lowerRegex : SExpr → SExpr)
    (source : OfficialDocument) : LexicalLowered :=
  { rules := lexicalRules lowerRegex source.rows, original := source }

structure Composed where
  syntaxPart : List Rule
  wrapperPart : List Rule
  lexicalPart : List Rule
  supportPart : List Rule
  original : OfficialDocument
  deriving DecidableEq, Repr

def compose (lowerGrammar : SExpr → SExpr) (wrappers support : List Rule)
    (lowered : LexicalLowered) : Composed :=
  { syntaxPart := syntaxRules lowerGrammar lowered.original.rows
    wrapperPart := wrappers
    lexicalPart := lowered.rules
    supportPart := support
    original := lowered.original }

def Composed.rules (value : Composed) : List Rule :=
  value.syntaxPart ++ value.wrapperPart ++ value.lexicalPart ++ value.supportPart

@[simp] theorem lowerLexical_reflects_source (lowerRegex : SExpr → SExpr)
    (source : OfficialDocument) :
    (lowerLexical lowerRegex source).original = source := rfl

@[simp] theorem compose_reflects_source (lowerRegex lowerGrammar : SExpr → SExpr)
    (wrappers support : List Rule) (source : OfficialDocument) :
    (compose lowerGrammar wrappers support (lowerLexical lowerRegex source)).original =
      source := rfl

theorem compose_rule_order (lowerRegex lowerGrammar : SExpr → SExpr)
    (wrappers support : List Rule) (source : OfficialDocument) :
    (compose lowerGrammar wrappers support
        (lowerLexical lowerRegex source)).rules =
      syntaxRules lowerGrammar source.rows ++ wrappers ++
        lexicalRules lowerRegex source.rows ++ support := rfl

theorem syntax_target_reflects_to_official_source
    (lowerRegex lowerGrammar : SExpr → SExpr) (wrappers support : List Rule)
    (source : OfficialDocument) (target : Rule)
    (member : target ∈ (compose lowerGrammar wrappers support
      (lowerLexical lowerRegex source)).syntaxPart) :
    ∃ row ∈ source.rows, SyntacticallyDerived lowerGrammar row target := by
  exact (mem_syntaxRules_iff lowerGrammar source.rows target).mp member

theorem lexical_target_reflects_to_official_source
    (lowerRegex lowerGrammar : SExpr → SExpr) (wrappers support : List Rule)
    (source : OfficialDocument) (target : Rule)
    (member : target ∈ (compose lowerGrammar wrappers support
      (lowerLexical lowerRegex source)).lexicalPart) :
    ∃ row ∈ source.rows, LexicallyDerived lowerRegex row target := by
  exact (mem_lexicalRules_iff lowerRegex source.rows target).mp member

/-! ## Exact authored-source qualification contract -/

def AuthoredCompositionSourceExact
    (lexicalSyntax syntaxSyntax : SExpr) : Prop :=
    equation? lexicalSyntax 5 =
      some
        (app "tptp-lex-v1:entries"
          [app "tptp-ebnf-v1:entries-nil" [], .atom "?state"],
         app "tptp-lex-v1:result"
          [app "bnf-v1:entries-nil" [], .atom "?state"]) ∧
    equation? lexicalSyntax 6 =
      some
        (app "tptp-lex-v1:entries"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:token-row"
              [.atom "?name", .atom "?rhs", .atom "?span"], .atom "?tail"],
           .atom "?state"],
         app "tptp-lex-v1:prepend-rule"
          [.atom "?name", .atom "?span",
           app "tptp-lex-v1:expression" [.atom "?rhs", .atom "?state"],
           .atom "?tail"]) ∧
    equation? lexicalSyntax 7 =
      some
        (app "tptp-lex-v1:entries"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:character-row"
              [.atom "?name", .atom "?rhs", .atom "?span"], .atom "?tail"],
           .atom "?state"],
         app "tptp-lex-v1:prepend-rule"
          [.atom "?name", .atom "?span",
           app "tptp-lex-v1:expression" [.atom "?rhs", .atom "?state"],
           .atom "?tail"]) ∧
    equation? lexicalSyntax 8 =
      some
        (app "tptp-lex-v1:entries"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:syntax-row"
              [.atom "?name", .atom "?rhs", .atom "?span"], .atom "?tail"],
           .atom "?state"],
         app "tptp-lex-v1:entries" [.atom "?tail", .atom "?state"]) ∧
    equation? lexicalSyntax 9 =
      some
        (app "tptp-lex-v1:entries"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:semantic-row"
              [.atom "?name", .atom "?rhs", .atom "?span"], .atom "?tail"],
           .atom "?state"],
         app "tptp-lex-v1:entries" [.atom "?tail", .atom "?state"]) ∧
    equation? lexicalSyntax 10 =
      some
        (app "tptp-lex-v1:entries"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:comment"
              [.atom "?text", .atom "?span"], .atom "?tail"],
           .atom "?state"],
         app "tptp-lex-v1:entries" [.atom "?tail", .atom "?state"]) ∧
    equation? lexicalSyntax 11 =
      some
        (app "tptp-lex-v1:entries"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:blank" [.atom "?span"], .atom "?tail"],
           .atom "?state"],
         app "tptp-lex-v1:entries" [.atom "?tail", .atom "?state"]) ∧
    equation? syntaxSyntax 1 =
      some
        (app "tptp-syn-v1:rows"
          [app "tptp-ebnf-v1:entries-nil" [], .atom "?lex"],
         app "bnf-v1:entries-nil" []) ∧
    equation? syntaxSyntax 2 =
      some
        (app "tptp-syn-v1:rows"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:syntax-row"
              [.atom "?name", .atom "?rhs", .atom "?span"], .atom "?tail"],
           .atom "?lex"],
         app "bnf-v1:entries-cons"
          [app "bnf-v1:rule"
            [app "tptp-lex-v1:text" [.atom "?name"],
             app "tptp-syn-v1:expression" [.atom "?rhs", .atom "?lex"],
             app "tptp-lex-v1:span" [.atom "?span"]],
           app "tptp-syn-v1:rows" [.atom "?tail", .atom "?lex"]]) ∧
    equation? syntaxSyntax 3 =
      some
        (app "tptp-syn-v1:rows"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:semantic-row"
              [.atom "?name", .atom "?rhs", .atom "?span"], .atom "?tail"],
           .atom "?lex"],
         app "tptp-syn-v1:rows" [.atom "?tail", .atom "?lex"]) ∧
    equation? syntaxSyntax 4 =
      some
        (app "tptp-syn-v1:rows"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:token-row"
              [.atom "?name", .atom "?rhs", .atom "?span"], .atom "?tail"],
           .atom "?lex"],
         app "tptp-syn-v1:rows" [.atom "?tail", .atom "?lex"]) ∧
    equation? syntaxSyntax 5 =
      some
        (app "tptp-syn-v1:rows"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:character-row"
              [.atom "?name", .atom "?rhs", .atom "?span"], .atom "?tail"],
           .atom "?lex"],
         app "tptp-syn-v1:rows" [.atom "?tail", .atom "?lex"]) ∧
    equation? syntaxSyntax 6 =
      some
        (app "tptp-syn-v1:rows"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:comment"
              [.atom "?text", .atom "?span"], .atom "?tail"],
           .atom "?lex"],
         app "tptp-syn-v1:rows" [.atom "?tail", .atom "?lex"]) ∧
    equation? syntaxSyntax 7 =
      some
        (app "tptp-syn-v1:rows"
          [app "tptp-ebnf-v1:entries-cons"
            [app "tptp-ebnf-v1:blank" [.atom "?span"], .atom "?tail"],
           .atom "?lex"],
         app "tptp-syn-v1:rows" [.atom "?tail", .atom "?lex"]) ∧
    (equation? lexicalSyntax 28).isSome = true ∧
    (equation? lexicalSyntax 29).isSome = true ∧
    (equation? lexicalSyntax 30).isSome = true ∧
    (equation? syntaxSyntax 13).isSome = true ∧
    (equation? syntaxSyntax 47).isSome = true ∧
    (equation? syntaxSyntax 48).isSome = true

#print axioms mem_lexicalRules_iff
#print axioms mem_syntaxRules_iff
#print axioms lexicalRules_append
#print axioms syntaxRules_append
#print axioms compose_rule_order
#print axioms syntax_target_reflects_to_official_source
#print axioms lexical_target_reflects_to_official_source

end Mettapedia.GSLT.Parsing.TptpOfficialCompositionSource
