import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-!
# Maximal-token MM2 syntax

This module factors the MM2 program and expression-body grammar into two
states: between tokens, and immediately after a bare symbol or variable.
The latter state admits only whitespace, an adjacent expression, or the
enclosing end condition.  Consequently a successful whole-input derivation
cannot stop a bare token while its next character still belongs to that
token.

The construction is compiled only through the generic LanguageDef and
ParserPack compilers.  Its exact CST lowering, UTF-8 boundary, runtime
agreement, and connection to the MM2 execution GSLT are established in the
companion modules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

private def ctor (label category : String)
    (parameters : List (String × String))
    (syntaxPattern : List SyntaxItem := []) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern
}

private def terminal (token : String) : SyntaxItem := .terminal token
private def nonterminal (parameter : String) : SyntaxItem :=
  .nonTerminal parameter

/-- Authored MM2 grammar whose control state enforces maximal bare tokens. -/
def language : LanguageDef := {
  name := "MM2MaximalTokenSyntaxV1"
  types := [
    "MM2Program", "MM2ProgramAfterOpen", "MM2Atoms",
    "MM2AtomsAfterOpen", "MM2Expression", "MM2ClosedAtom",
    "MM2OpenAtom", "MM2LineComment", "MM2EOFComment",
    "MM2CommentTail", "MM2BareHead", "MM2BareTail", "MM2BareChar",
    "MM2Variable", "MM2VariableChars", "MM2VariableChar",
    "MM2QuotedSymbol", "MM2QuotedChars", "MM2QuotedChar",
    "MM2EscapedChar", "MM2Whitespace", "MM2CommentChar", "MM2LineFeed"]
  terms := [
    ctor "mm2:program-empty" "MM2Program" [],
    ctor "mm2:program-whitespace" "MM2Program"
      [("character", "MM2Whitespace"), ("rest", "MM2Program")]
      [nonterminal "character", nonterminal "rest"],
    ctor "mm2:program-line-comment" "MM2Program"
      [("comment", "MM2LineComment"), ("rest", "MM2Program")]
      [nonterminal "comment", nonterminal "rest"],
    ctor "mm2:program-eof-comment" "MM2Program"
      [("comment", "MM2EOFComment")]
      [nonterminal "comment"],
    ctor "mm2:program-closed" "MM2Program"
      [("atom", "MM2ClosedAtom"), ("rest", "MM2Program")]
      [nonterminal "atom", nonterminal "rest"],
    ctor "mm2:program-open" "MM2Program"
      [("atom", "MM2OpenAtom"), ("rest", "MM2ProgramAfterOpen")]
      [nonterminal "atom", nonterminal "rest"],

    ctor "mm2:program-after-open-end" "MM2ProgramAfterOpen" [],
    ctor "mm2:program-after-open-whitespace" "MM2ProgramAfterOpen"
      [("character", "MM2Whitespace"), ("rest", "MM2Program")]
      [nonterminal "character", nonterminal "rest"],
    ctor "mm2:program-after-open-expression" "MM2ProgramAfterOpen"
      [("expression", "MM2Expression"), ("rest", "MM2Program")]
      [nonterminal "expression", nonterminal "rest"],

    ctor "mm2:expression" "MM2Expression" [("atoms", "MM2Atoms")]
      [terminal "(", nonterminal "atoms", terminal ")"],

    ctor "mm2:atoms-empty" "MM2Atoms" [],
    ctor "mm2:atoms-whitespace" "MM2Atoms"
      [("character", "MM2Whitespace"), ("rest", "MM2Atoms")]
      [nonterminal "character", nonterminal "rest"],
    ctor "mm2:atoms-line-comment" "MM2Atoms"
      [("comment", "MM2LineComment"), ("rest", "MM2Atoms")]
      [nonterminal "comment", nonterminal "rest"],
    ctor "mm2:atoms-closed" "MM2Atoms"
      [("atom", "MM2ClosedAtom"), ("rest", "MM2Atoms")]
      [nonterminal "atom", nonterminal "rest"],
    ctor "mm2:atoms-open" "MM2Atoms"
      [("atom", "MM2OpenAtom"), ("rest", "MM2AtomsAfterOpen")]
      [nonterminal "atom", nonterminal "rest"],

    ctor "mm2:atoms-after-open-end" "MM2AtomsAfterOpen" [],
    ctor "mm2:atoms-after-open-whitespace" "MM2AtomsAfterOpen"
      [("character", "MM2Whitespace"), ("rest", "MM2Atoms")]
      [nonterminal "character", nonterminal "rest"],
    ctor "mm2:atoms-after-open-expression" "MM2AtomsAfterOpen"
      [("expression", "MM2Expression"), ("rest", "MM2Atoms")]
      [nonterminal "expression", nonterminal "rest"],

    ctor "mm2:closed-atom-quoted" "MM2ClosedAtom"
      [("quoted", "MM2QuotedSymbol")] [nonterminal "quoted"],
    ctor "mm2:closed-atom-expression" "MM2ClosedAtom"
      [("expression", "MM2Expression")] [nonterminal "expression"],
    ctor "mm2:open-atom-bare" "MM2OpenAtom"
      [("head", "MM2BareHead"), ("tail", "MM2BareTail")]
      [nonterminal "head", nonterminal "tail"],
    ctor "mm2:open-atom-variable" "MM2OpenAtom"
      [("variable", "MM2Variable")] [nonterminal "variable"],

    ctor "mm2:line-comment" "MM2LineComment"
      [("tail", "MM2CommentTail"), ("lineFeed", "MM2LineFeed")]
      [terminal ";", nonterminal "tail", nonterminal "lineFeed"],
    ctor "mm2:eof-comment" "MM2EOFComment"
      [("tail", "MM2CommentTail")]
      [terminal ";", nonterminal "tail"],
    ctor "mm2:comment-tail-empty" "MM2CommentTail" [],
    ctor "mm2:comment-tail-cons" "MM2CommentTail"
      [("character", "MM2CommentChar"), ("rest", "MM2CommentTail")]
      [nonterminal "character", nonterminal "rest"],

    ctor "mm2:bare-tail-empty" "MM2BareTail" [],
    ctor "mm2:bare-tail-cons" "MM2BareTail"
      [("character", "MM2BareChar"), ("rest", "MM2BareTail")]
      [nonterminal "character", nonterminal "rest"],

    ctor "mm2:variable" "MM2Variable"
      [("characters", "MM2VariableChars")]
      [terminal "$", nonterminal "characters"],
    ctor "mm2:variable-chars-empty" "MM2VariableChars" [],
    ctor "mm2:variable-chars-cons" "MM2VariableChars"
      [("character", "MM2VariableChar"), ("rest", "MM2VariableChars")]
      [nonterminal "character", nonterminal "rest"],

    ctor "mm2:quoted-symbol" "MM2QuotedSymbol"
      [("characters", "MM2QuotedChars")]
      [terminal "\"", nonterminal "characters", terminal "\""],
    ctor "mm2:quoted-chars-empty" "MM2QuotedChars" [],
    ctor "mm2:quoted-chars-plain" "MM2QuotedChars"
      [("character", "MM2QuotedChar"), ("rest", "MM2QuotedChars")]
      [nonterminal "character", nonterminal "rest"],
    ctor "mm2:quoted-chars-escaped" "MM2QuotedChars"
      [("character", "MM2EscapedChar"), ("rest", "MM2QuotedChars")]
      [terminal "\\", nonterminal "character", nonterminal "rest"]
  ]
  equations := []
  rewrites := []
}

theorem inventory :
    language.types.length = 23 ∧ language.terms.length = 35 := by
  decide

def compiledRules : List CompiledRule :=
  (compileRules? mm2SyntaxBinding language).getD []

theorem compile_rules_exact :
    compileRules? mm2SyntaxBinding language = some compiledRules := by
  decide +kernel

def parserPackPlanOption : Option CompiledParserPackPlan :=
  compileParserPackPlan? mm2TerminalScalars? mm2ParserProfile compiledRules

def parserPackPlan : CompiledParserPackPlan :=
  parserPackPlanOption.get (by decide)

theorem compile_parser_pack_exact :
    parserPackPlanOption = some parserPackPlan := by
  decide +kernel

def parserPackAgreement :
    ParserPackPlanAgreement mm2TerminalScalars? mm2ParserProfile
      compiledRules parserPackPlan :=
  ParserPackPlanAgreement.of_compilation compile_parser_pack_exact

theorem parser_pack_inventory :
    parserPackPlan.lexical.productions.length = 8 ∧
      parserPackPlan.structural.length = 35 := by
  decide +kernel

/-- Exact lexical production inventory consumed by derivation builders. -/
def lexicalSignatures :
    List (String × String × TerminalMatcher) := mm2LexicalSignatures

/-- Exact structural production inventory produced from the authored grammar. -/
def structuralSignatures :
    List (String × String × List PackItem) := [
  ("MM2Program", "mm2:program-empty", [.terminal .eof]),
  ("MM2Program", "mm2:program-whitespace",
    [.nonterminal "MM2Whitespace", .nonterminal "MM2Program",
     .terminal .eof]),
  ("MM2Program", "mm2:program-line-comment",
    [.nonterminal "MM2LineComment", .nonterminal "MM2Program",
     .terminal .eof]),
  ("MM2Program", "mm2:program-eof-comment",
    [.nonterminal "MM2EOFComment", .terminal .eof]),
  ("MM2Program", "mm2:program-closed",
    [.nonterminal "MM2ClosedAtom", .nonterminal "MM2Program",
     .terminal .eof]),
  ("MM2Program", "mm2:program-open",
    [.nonterminal "MM2OpenAtom", .nonterminal "MM2ProgramAfterOpen",
     .terminal .eof]),
  ("MM2ProgramAfterOpen", "mm2:program-after-open-end", []),
  ("MM2ProgramAfterOpen", "mm2:program-after-open-whitespace",
    [.nonterminal "MM2Whitespace", .nonterminal "MM2Program"]),
  ("MM2ProgramAfterOpen", "mm2:program-after-open-expression",
    [.nonterminal "MM2Expression", .nonterminal "MM2Program"]),
  ("MM2Expression", "mm2:expression",
    [.terminal (.char 40), .nonterminal "MM2Atoms", .terminal (.char 41)]),
  ("MM2Atoms", "mm2:atoms-empty", []),
  ("MM2Atoms", "mm2:atoms-whitespace",
    [.nonterminal "MM2Whitespace", .nonterminal "MM2Atoms"]),
  ("MM2Atoms", "mm2:atoms-line-comment",
    [.nonterminal "MM2LineComment", .nonterminal "MM2Atoms"]),
  ("MM2Atoms", "mm2:atoms-closed",
    [.nonterminal "MM2ClosedAtom", .nonterminal "MM2Atoms"]),
  ("MM2Atoms", "mm2:atoms-open",
    [.nonterminal "MM2OpenAtom", .nonterminal "MM2AtomsAfterOpen"]),
  ("MM2AtomsAfterOpen", "mm2:atoms-after-open-end", []),
  ("MM2AtomsAfterOpen", "mm2:atoms-after-open-whitespace",
    [.nonterminal "MM2Whitespace", .nonterminal "MM2Atoms"]),
  ("MM2AtomsAfterOpen", "mm2:atoms-after-open-expression",
    [.nonterminal "MM2Expression", .nonterminal "MM2Atoms"]),
  ("MM2ClosedAtom", "mm2:closed-atom-quoted",
    [.nonterminal "MM2QuotedSymbol"]),
  ("MM2ClosedAtom", "mm2:closed-atom-expression",
    [.nonterminal "MM2Expression"]),
  ("MM2OpenAtom", "mm2:open-atom-bare",
    [.nonterminal "MM2BareHead", .nonterminal "MM2BareTail"]),
  ("MM2OpenAtom", "mm2:open-atom-variable",
    [.nonterminal "MM2Variable"]),
  ("MM2LineComment", "mm2:line-comment",
    [.terminal (.char 59), .nonterminal "MM2CommentTail",
     .nonterminal "MM2LineFeed"]),
  ("MM2EOFComment", "mm2:eof-comment",
    [.terminal (.char 59), .nonterminal "MM2CommentTail"]),
  ("MM2CommentTail", "mm2:comment-tail-empty", []),
  ("MM2CommentTail", "mm2:comment-tail-cons",
    [.nonterminal "MM2CommentChar", .nonterminal "MM2CommentTail"]),
  ("MM2BareTail", "mm2:bare-tail-empty", []),
  ("MM2BareTail", "mm2:bare-tail-cons",
    [.nonterminal "MM2BareChar", .nonterminal "MM2BareTail"]),
  ("MM2Variable", "mm2:variable",
    [.terminal (.char 36), .nonterminal "MM2VariableChars"]),
  ("MM2VariableChars", "mm2:variable-chars-empty", []),
  ("MM2VariableChars", "mm2:variable-chars-cons",
    [.nonterminal "MM2VariableChar", .nonterminal "MM2VariableChars"]),
  ("MM2QuotedSymbol", "mm2:quoted-symbol",
    [.terminal (.char 34), .nonterminal "MM2QuotedChars",
     .terminal (.char 34)]),
  ("MM2QuotedChars", "mm2:quoted-chars-empty", []),
  ("MM2QuotedChars", "mm2:quoted-chars-plain",
    [.nonterminal "MM2QuotedChar", .nonterminal "MM2QuotedChars"]),
  ("MM2QuotedChars", "mm2:quoted-chars-escaped",
    [.terminal (.char 92), .nonterminal "MM2EscapedChar",
     .nonterminal "MM2QuotedChars"])]

theorem parser_pack_signatures_exact :
    (parserPackPlan.lexical.productions.map fun row =>
      (row.resultSort, row.label, row.matcher)) = lexicalSignatures ∧
    (parserPackPlan.structural.map fun row =>
      (row.resultSort, row.label, row.items)) = structuralSignatures := by
  decide +kernel

theorem parser_pack_source_exact :
    parserPackPlan.structural.map (fun production => production.source) =
      language.terms := by
  have compiledStructural :
      compileStructuralProductions? mm2TerminalScalars?
          mm2ParserProfile.startSort compiledRules =
        some parserPackPlan.structural := by
    decide +kernel
  calc
    parserPackPlan.structural.map (fun production => production.source) =
        compiledRules.map (fun rule => rule.source) :=
      compileStructuralProductions_source mm2TerminalScalars?
        mm2ParserProfile.startSort compiledRules
        parserPackPlan.structural compiledStructural
    _ = language.terms :=
      compileRules_sourceRules mm2SyntaxBinding language compiledRules
        compile_rules_exact

theorem language_valid : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals decide +kernel

#print axioms compile_rules_exact
#print axioms compile_parser_pack_exact
#print axioms parser_pack_inventory
#print axioms parser_pack_signatures_exact
#print axioms parser_pack_source_exact
#print axioms language_valid

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax
