import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
import Mettapedia.GSLT.Parsing.PresentationExprSemantics
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# MM2 concrete syntax, generated ParserPack, and native types

This module authors the ordinary MM2 reader language as a `LanguageDef`.
The syntax compiler derives the scannerless ParserPack plan from that source;
the existing MORK executor remains a separate semantic stage over parsed
atoms.

The grammar retains comments, quoted reader tokens, variables, nested
expressions, empty expressions, and top-level occurrence order.  Compact MORK
representation limits are checked later by the syntax-to-atom lowering rather
than being duplicated as sixty-four grammar categories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax

private def ctor (label category : String)
    (parameters : List (String × String))
    (syntaxPattern : List SyntaxItem := []) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := syntaxPattern
}

private def terminal (token : String) : SyntaxItem := .terminal token
private def nonterminal (parameter : String) : SyntaxItem :=
  .nonTerminal parameter

/-! ## Authored syntax GSLT -/

/-- Ordinary MM2 reader syntax.  Repetition is expressed by authored
right-recursive rows so ordered token and atom occurrences remain visible. -/
def mm2Syntax : LanguageDef := {
  name := "MM2ConcreteSyntaxV1"
  types := [
    "MM2Program", "MM2Atom", "MM2Atoms", "MM2Expression",
    "MM2Gap", "MM2GapUnit", "MM2FinalGap", "MM2LineComment",
    "MM2EOFComment", "MM2CommentTail",
    "MM2Symbol", "MM2BareHead", "MM2BareTail", "MM2BareChar",
    "MM2Variable", "MM2VariableChars", "MM2VariableChar",
    "MM2QuotedSymbol", "MM2QuotedChars", "MM2QuotedChar",
    "MM2EscapedChar", "MM2Whitespace", "MM2CommentChar", "MM2LineFeed"]
  terms := [
    ctor "mm2:program-empty" "MM2Program" [("gap", "MM2FinalGap")]
      [nonterminal "gap"],
    ctor "mm2:program-cons" "MM2Program"
      [("gap", "MM2Gap"), ("atom", "MM2Atom"),
       ("rest", "MM2Program")]
      [nonterminal "gap", nonterminal "atom", nonterminal "rest"],

    ctor "mm2:atom-symbol" "MM2Atom" [("symbol", "MM2Symbol")]
      [nonterminal "symbol"],
    ctor "mm2:atom-variable" "MM2Atom" [("variable", "MM2Variable")]
      [nonterminal "variable"],
    ctor "mm2:atom-expression" "MM2Atom"
      [("expression", "MM2Expression")] [nonterminal "expression"],

    ctor "mm2:expression" "MM2Expression"
      [("gap", "MM2Gap"), ("atoms", "MM2Atoms")]
      [terminal "(", nonterminal "gap", nonterminal "atoms", terminal ")"],
    ctor "mm2:atoms-empty" "MM2Atoms" [],
    ctor "mm2:atoms-cons" "MM2Atoms"
      [("atom", "MM2Atom"), ("gap", "MM2Gap"),
       ("rest", "MM2Atoms")]
      [nonterminal "atom", nonterminal "gap", nonterminal "rest"],

    ctor "mm2:gap-empty" "MM2Gap" [],
    ctor "mm2:gap-cons" "MM2Gap"
      [("unit", "MM2GapUnit"), ("rest", "MM2Gap")]
      [nonterminal "unit", nonterminal "rest"],
    ctor "mm2:gap-whitespace" "MM2GapUnit"
      [("character", "MM2Whitespace")] [nonterminal "character"],
    ctor "mm2:gap-comment" "MM2GapUnit"
      [("comment", "MM2LineComment")]
      [nonterminal "comment"],

    ctor "mm2:final-gap-regular" "MM2FinalGap" [("gap", "MM2Gap")]
      [nonterminal "gap"],
    ctor "mm2:final-gap-comment" "MM2FinalGap"
      [("gap", "MM2Gap"), ("comment", "MM2EOFComment")]
      [nonterminal "gap", nonterminal "comment"],

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

    ctor "mm2:symbol-bare" "MM2Symbol"
      [("head", "MM2BareHead"), ("tail", "MM2BareTail")]
      [nonterminal "head", nonterminal "tail"],
    ctor "mm2:symbol-quoted" "MM2Symbol"
      [("quoted", "MM2QuotedSymbol")] [nonterminal "quoted"],
    ctor "mm2:bare-tail-empty" "MM2BareTail" [],
    ctor "mm2:bare-tail-cons" "MM2BareTail"
      [("character", "MM2BareChar"), ("rest", "MM2BareTail")]
      [nonterminal "character", nonterminal "rest"],

    ctor "mm2:variable" "MM2Variable"
      [("characters", "MM2VariableChars")]
      [terminal "$", nonterminal "characters"],
    ctor "mm2:variable-chars-empty" "MM2VariableChars" [],
    ctor "mm2:variable-chars-cons" "MM2VariableChars"
      [("character", "MM2VariableChar"),
       ("rest", "MM2VariableChars")]
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

theorem mm2Syntax_inventory :
    mm2Syntax.types.length = 24 ∧
      mm2Syntax.terms.length = 29 ∧
      mm2Syntax.rewrites = [] := by
  decide

/-! ## Authored lexical profile -/

/-- The MORK byte reader treats only space, tab, and line feed as whitespace.
The ParserPack carrier is Unicode scalar input, so UTF-8 realization remains
an explicit later correspondence theorem. -/
def mm2ParserProfile : ParserProfileLayer := {
  name := "MM2OrdinaryReaderV1"
  startSort := "MM2Program"
  classes := [
    { name := "MM2WhitespaceClass", kind := .points [9, 10, 32] },
    { name := "MM2BareHeadClass",
      kind := .except [0, 9, 10, 32, 34, 36, 40, 41, 59] },
    { name := "MM2BareCharClass", kind := .except [0, 9, 10, 32, 40, 41] },
    { name := "MM2VariableCharClass",
      kind := .except [0, 9, 10, 32, 40, 41] },
    { name := "MM2CommentCharClass", kind := .except [0, 10] },
    { name := "MM2QuotedCharClass", kind := .except [0, 34, 92] },
    { name := "MM2EscapedCharClass", kind := .except [0] },
    { name := "MM2LineFeedClass", kind := .points [10] }]
  states := [
    { resultSort := "MM2Whitespace", className := "MM2WhitespaceClass",
      ruleLabel := "mm2:lex-whitespace" },
    { resultSort := "MM2BareHead", className := "MM2BareHeadClass",
      ruleLabel := "mm2:lex-bare-head" },
    { resultSort := "MM2BareChar", className := "MM2BareCharClass",
      ruleLabel := "mm2:lex-bare-char" },
    { resultSort := "MM2VariableChar", className := "MM2VariableCharClass",
      ruleLabel := "mm2:lex-variable-char" },
    { resultSort := "MM2CommentChar", className := "MM2CommentCharClass",
      ruleLabel := "mm2:lex-comment-char" },
    { resultSort := "MM2QuotedChar", className := "MM2QuotedCharClass",
      ruleLabel := "mm2:lex-quoted-char" },
    { resultSort := "MM2EscapedChar", className := "MM2EscapedCharClass",
      ruleLabel := "mm2:lex-escaped-char" },
    { resultSort := "MM2LineFeed", className := "MM2LineFeedClass",
      ruleLabel := "mm2:lex-line-feed" }]
}

theorem mm2ParserProfile_inventory :
    mm2ParserProfile.classes.length = 8 ∧
      mm2ParserProfile.states.length = 8 := by
  decide

theorem lexical_boundaries :
    mm2ParserProfile.classAccepts? "MM2WhitespaceClass" 10 = some true ∧
      mm2ParserProfile.classAccepts? "MM2WhitespaceClass" 13 = some false ∧
      mm2ParserProfile.classAccepts? "MM2BareHeadClass" 36 = some false ∧
      mm2ParserProfile.classAccepts? "MM2BareCharClass" 36 = some true ∧
      mm2ParserProfile.classAccepts? "MM2CommentCharClass" 10 = some false ∧
      mm2ParserProfile.classAccepts? "MM2LineFeedClass" 10 = some true ∧
      mm2ParserProfile.classAccepts? "MM2LineFeedClass" 13 = some false ∧
      mm2ParserProfile.classAccepts? "MM2EscapedCharClass" 0 = some false ∧
      mm2ParserProfile.classAccepts? "MM2QuotedCharClass" 34 = some false := by
  decide

/-! ## Generic structural and ParserPack compilation -/

def mm2SyntaxBinding : Binding where
  literalRef := fun token =>
    match token with
    | "(" => some "mm2:literal-left-paren"
    | ")" => some "mm2:literal-right-paren"
    | "$" => some "mm2:literal-dollar"
    | ";" => some "mm2:literal-semicolon"
    | "\n" => some "mm2:literal-line-feed"
    | "\"" => some "mm2:literal-quotation"
    | "\\" => some "mm2:literal-reverse-solidus"
    | _ => none
  lexicalSortRef := mm2ParserProfile.lexicalRule?
  categoryRef := fun category => s!"mm2:category:{category}"
  ruleRef := fun label => s!"mm2:rule:{label}"

def compiledMM2SyntaxRules : List CompiledRule :=
  (compileRules? mm2SyntaxBinding mm2Syntax).getD []

theorem compile_mm2Syntax_exact :
    compileRules? mm2SyntaxBinding mm2Syntax =
      some compiledMM2SyntaxRules := by
  decide +kernel

theorem compiled_rules_source_exact :
    compiledMM2SyntaxRules.map (fun rule => rule.source) =
      mm2Syntax.terms :=
  compileRules_sourceRules mm2SyntaxBinding mm2Syntax
    compiledMM2SyntaxRules compile_mm2Syntax_exact

theorem compiled_rules_syntax_exact :
    compiledMM2SyntaxRules.map (fun rule =>
        rule.atoms.map StructuralAtom.sourceSyntax) =
      mm2Syntax.terms.map (fun rule => rule.syntaxPattern) :=
  compileRules_sourceSyntax mm2SyntaxBinding mm2Syntax
    compiledMM2SyntaxRules compile_mm2Syntax_exact

theorem compiled_derivation_iff_source_derivation
    (sort : String) (tokens : List String) (tree : Pattern) :
    CompiledDerives compiledMM2SyntaxRules sort tokens tree ↔
      Mettapedia.OSLF.Framework.GrammarDerives.Derives
        mm2Syntax sort tokens tree :=
  compileRules_derivation_iff compile_mm2Syntax_exact sort tokens tree

private def literalDefinitions : List Definition := [
  { name := "mm2:literal-left-paren", body := .char 40 },
  { name := "mm2:literal-right-paren", body := .char 41 },
  { name := "mm2:literal-dollar", body := .char 36 },
  { name := "mm2:literal-semicolon", body := .char 59 },
  { name := "mm2:literal-line-feed", body := .char 10 },
  { name := "mm2:literal-quotation", body := .char 34 },
  { name := "mm2:literal-reverse-solidus", body := .char 92 }]

private def lexicalDefinitions : List Definition := [
  { name := "mm2:lex-whitespace",
    body := .node "mm2:lex-whitespace" (.class "MM2WhitespaceClass") },
  { name := "mm2:lex-bare-head",
    body := .node "mm2:lex-bare-head" (.class "MM2BareHeadClass") },
  { name := "mm2:lex-bare-char",
    body := .node "mm2:lex-bare-char" (.class "MM2BareCharClass") },
  { name := "mm2:lex-variable-char",
    body := .node "mm2:lex-variable-char" (.class "MM2VariableCharClass") },
  { name := "mm2:lex-comment-char",
    body := .node "mm2:lex-comment-char" (.class "MM2CommentCharClass") },
  { name := "mm2:lex-quoted-char",
    body := .node "mm2:lex-quoted-char" (.class "MM2QuotedCharClass") },
  { name := "mm2:lex-escaped-char",
    body := .node "mm2:lex-escaped-char" (.class "MM2EscapedCharClass") },
  { name := "mm2:lex-line-feed",
    body := .node "mm2:lex-line-feed" (.class "MM2LineFeedClass") }]

def compiledMM2CategoryDefinitions : List Definition :=
  (compileCategoryDefinitions? mm2SyntaxBinding mm2Syntax
    compiledMM2SyntaxRules).getD []

theorem compile_mm2_categories_exact :
    compileCategoryDefinitions? mm2SyntaxBinding mm2Syntax
        compiledMM2SyntaxRules =
      some compiledMM2CategoryDefinitions := by
  decide +kernel

def mm2ScannerlessPresentation : Presentation := {
  name := "MM2OrdinaryReaderScannerlessV1"
  definitions := literalDefinitions ++ lexicalDefinitions ++
    compiledMM2SyntaxRules.map
      (CompiledRule.definition mm2SyntaxBinding) ++
    compiledMM2CategoryDefinitions
  members := []
}

def mm2TerminalScalarsFrom?
    (presentation : Presentation) (token : String) : Option (List Nat) := do
  let parserRef ← mm2SyntaxBinding.literalRef token
  presentation.literalCodepoints? parserRef

def mm2TerminalScalars? : String → Option (List Nat) :=
  mm2TerminalScalarsFrom? mm2ScannerlessPresentation

def mm2ParserPackPlanOption : Option CompiledParserPackPlan :=
  compileParserPackPlan? mm2TerminalScalars? mm2ParserProfile
    compiledMM2SyntaxRules

def mm2ParserPackPlan : CompiledParserPackPlan :=
  mm2ParserPackPlanOption.get (by decide)

theorem compile_mm2_parser_pack_exact :
    mm2ParserPackPlanOption = some mm2ParserPackPlan := by
  decide +kernel

def mm2ParserPackAgreement :
    ParserPackPlanAgreement mm2TerminalScalars? mm2ParserProfile
      compiledMM2SyntaxRules mm2ParserPackPlan :=
  ParserPackPlanAgreement.of_compilation compile_mm2_parser_pack_exact

theorem mm2_parser_pack_inventory :
    mm2ParserPackPlan.lexical.classes.length = 8 ∧
      mm2ParserPackPlan.lexical.productions.length = 8 ∧
      mm2ParserPackPlan.structural.length = 29 := by
  decide +kernel

/-- Exact physical lexical ABI consumed by derivation builders and external
parser backends.  Positions are retained because equal duplicate rows would
still be distinct parser choices. -/
def mm2LexicalSignatures :
    List (String × String × TerminalMatcher) := [
  ("MM2Whitespace", "mm2:lex-whitespace", .class "MM2WhitespaceClass"),
  ("MM2BareHead", "mm2:lex-bare-head", .class "MM2BareHeadClass"),
  ("MM2BareChar", "mm2:lex-bare-char", .class "MM2BareCharClass"),
  ("MM2VariableChar", "mm2:lex-variable-char",
    .class "MM2VariableCharClass"),
  ("MM2CommentChar", "mm2:lex-comment-char", .class "MM2CommentCharClass"),
  ("MM2QuotedChar", "mm2:lex-quoted-char", .class "MM2QuotedCharClass"),
  ("MM2EscapedChar", "mm2:lex-escaped-char", .class "MM2EscapedCharClass"),
  ("MM2LineFeed", "mm2:lex-line-feed", .class "MM2LineFeedClass")]

/-- Exact physical structural ABI derived from the 29 authored syntax rows. -/
def mm2StructuralSignatures :
    List (String × String × List PackItem) := [
  ("MM2Program", "mm2:program-empty",
    [.nonterminal "MM2FinalGap"]),
  ("MM2Program", "mm2:program-cons",
    [.nonterminal "MM2Gap", .nonterminal "MM2Atom",
     .nonterminal "MM2Program"]),
  ("MM2Atom", "mm2:atom-symbol", [.nonterminal "MM2Symbol"]),
  ("MM2Atom", "mm2:atom-variable", [.nonterminal "MM2Variable"]),
  ("MM2Atom", "mm2:atom-expression", [.nonterminal "MM2Expression"]),
  ("MM2Expression", "mm2:expression",
    [.terminal (.char 40), .nonterminal "MM2Gap",
     .nonterminal "MM2Atoms", .terminal (.char 41)]),
  ("MM2Atoms", "mm2:atoms-empty", []),
  ("MM2Atoms", "mm2:atoms-cons",
    [.nonterminal "MM2Atom", .nonterminal "MM2Gap",
     .nonterminal "MM2Atoms"]),
  ("MM2Gap", "mm2:gap-empty", []),
  ("MM2Gap", "mm2:gap-cons",
    [.nonterminal "MM2GapUnit", .nonterminal "MM2Gap"]),
  ("MM2GapUnit", "mm2:gap-whitespace",
    [.nonterminal "MM2Whitespace"]),
  ("MM2GapUnit", "mm2:gap-comment", [.nonterminal "MM2LineComment"]),
  ("MM2FinalGap", "mm2:final-gap-regular", [.nonterminal "MM2Gap"]),
  ("MM2FinalGap", "mm2:final-gap-comment",
    [.nonterminal "MM2Gap", .nonterminal "MM2EOFComment"]),
  ("MM2LineComment", "mm2:line-comment",
    [.terminal (.char 59), .nonterminal "MM2CommentTail",
     .nonterminal "MM2LineFeed"]),
  ("MM2EOFComment", "mm2:eof-comment",
    [.terminal (.char 59), .nonterminal "MM2CommentTail"]),
  ("MM2CommentTail", "mm2:comment-tail-empty", []),
  ("MM2CommentTail", "mm2:comment-tail-cons",
    [.nonterminal "MM2CommentChar", .nonterminal "MM2CommentTail"]),
  ("MM2Symbol", "mm2:symbol-bare",
    [.nonterminal "MM2BareHead", .nonterminal "MM2BareTail"]),
  ("MM2Symbol", "mm2:symbol-quoted", [.nonterminal "MM2QuotedSymbol"]),
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

theorem mm2_parser_pack_signatures_exact :
    (mm2ParserPackPlan.lexical.productions.map fun row =>
      (row.resultSort, row.label, row.matcher)) = mm2LexicalSignatures ∧
    (mm2ParserPackPlan.structural.map fun row =>
      (row.resultSort, row.label, row.items)) = mm2StructuralSignatures := by
  decide +kernel

theorem mm2_parser_pack_source_exact :
    mm2ParserPackPlan.structural.map (fun production => production.source) =
      mm2Syntax.terms := by
  have compiledStructural :
      compileStructuralProductions? mm2TerminalScalars?
          mm2ParserProfile.startSort compiledMM2SyntaxRules =
        some mm2ParserPackPlan.structural := by
    decide +kernel
  calc
    mm2ParserPackPlan.structural.map (fun production => production.source) =
        compiledMM2SyntaxRules.map (fun rule => rule.source) :=
      compileStructuralProductions_source mm2TerminalScalars?
        mm2ParserProfile.startSort compiledMM2SyntaxRules
        mm2ParserPackPlan.structural compiledStructural
    _ = mm2Syntax.terms := compiled_rules_source_exact

/-! ## Mandatory OSLF and native-type gate -/

abbrev mm2SyntaxTheory : Mettapedia.GSLT.GSLT :=
  langGSLT mm2Syntax

theorem mm2SyntaxTheory_no_step (source target : mm2SyntaxTheory.Term) :
    ¬ mm2SyntaxTheory.Step source target := by
  intro reduction
  change langSemanticReduces mm2Syntax source target at reduction
  have rawReduction : langReduces mm2Syntax source target :=
    (langSemanticReduces_iff_langReduces_of_equation_free
      (by rfl) source target).mp reduction
  change langReducesUsing RelationEnv.empty mm2Syntax source target at rawReduction
  unfold langReducesUsing at rawReduction
  rcases rawReduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

def mm2SyntaxOSLF := langOSLF mm2Syntax "MM2Program"

/-- Structural NTT requested from the exact authored program sort. -/
def programNativeType : langNativeType mm2Syntax "MM2Program" where
  sort := "MM2Program"
  pred := equationPredicateOfEquationFree (by rfl) fun term =>
    checkHasType mm2Syntax WellSorted.FreeTypeContext.empty [] term
      (.base "MM2Program") = true

private def emptyGap : Pattern := .apply "mm2:gap-empty" []
private def emptyFinalGap : Pattern :=
  .apply "mm2:final-gap-regular" [emptyGap]
private def emptyProgram : Pattern :=
  .apply "mm2:program-empty" [emptyFinalGap]
private def emptyAtomList : Pattern := .apply "mm2:atoms-empty" []

theorem empty_program_inhabits_native_type :
    programNativeType.pred.1 emptyProgram := by
  change checkHasType mm2Syntax WellSorted.FreeTypeContext.empty []
      emptyProgram (.base "MM2Program") = true
  decide +kernel

/-- Negative NTT control: an atom-list carrier cannot masquerade as a
top-level MM2 program. -/
theorem atom_list_does_not_inhabit_program_native_type :
    ¬ programNativeType.pred.1 emptyAtomList := by
  change ¬ (checkHasType mm2Syntax WellSorted.FreeTypeContext.empty []
      emptyAtomList (.base "MM2Program") = true)
  decide +kernel

theorem exact_target_native_type_empty
    (source target : mm2SyntaxTheory.Term) :
    ¬ (exactTargetNativeType mm2SyntaxTheory target).pred.1 source := by
  intro holds
  change gsltDiamond mm2SyntaxTheory _ source at holds
  rw [gsltDiamond_spec] at holds
  obtain ⟨middle, step, _⟩ := holds
  exact mm2SyntaxTheory_no_step source middle step

/-! ## Presentation-sensitivity controls -/

def missingExpressionMutation : LanguageDef :=
  { mm2Syntax with
    terms := mm2Syntax.terms.filter fun rule =>
      rule.label != "mm2:expression" }

theorem missing_expression_changes_compilation :
    compileRules? mm2SyntaxBinding missingExpressionMutation ≠
      compileRules? mm2SyntaxBinding mm2Syntax := by
  decide +kernel

def dollarAdmittingHeadMutation : ParserProfileLayer :=
  { mm2ParserProfile with
    classes := mm2ParserProfile.classes.map fun declaration =>
      if declaration.name == "MM2BareHeadClass" then
        { declaration with
          kind := .except [9, 10, 32, 34, 40, 41, 59] }
      else
        declaration }

theorem dollar_mutation_changes_parser_pack :
    compileParserPackPlan? mm2TerminalScalars? dollarAdmittingHeadMutation
        compiledMM2SyntaxRules ≠
      mm2ParserPackPlanOption := by
  decide +kernel

private def duplicateLeftParenMutation : Presentation :=
  { mm2ScannerlessPresentation with
    definitions :=
      { name := "mm2:literal-left-paren", body := .char 91 } ::
        mm2ScannerlessPresentation.definitions }

theorem duplicate_literal_rejects_parser_pack :
    compileParserPackPlan?
        (mm2TerminalScalarsFrom? duplicateLeftParenMutation)
        mm2ParserProfile compiledMM2SyntaxRules = none := by
  decide +kernel

#print axioms compiled_rules_source_exact
#print axioms compiled_rules_syntax_exact
#print axioms compiled_derivation_iff_source_derivation
#print axioms mm2_parser_pack_source_exact
#print axioms mm2_parser_pack_signatures_exact
#print axioms empty_program_inhabits_native_type
#print axioms atom_list_does_not_inhabit_program_native_type
#print axioms exact_target_native_type_empty
#print axioms missing_expression_changes_compilation
#print axioms dollar_mutation_changes_parser_pack
#print axioms duplicate_literal_rejects_parser_pack

end Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT
