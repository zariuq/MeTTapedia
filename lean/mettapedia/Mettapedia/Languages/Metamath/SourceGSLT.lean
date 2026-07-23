import Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction

/-!
# Metamath source grammar as one GSLT root

This module owns the declarative source grammar used to derive runnable
parser artifacts and generic grammar-inference presentations. Concrete
lexical syntax must be represented through ordinary GSLT data rather than
privileged fields on `LanguageDef`.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
open Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction

def labelTokenSort : String := "label_tok"
def symbolTokenSort : String := "symbol_tok"
def proofLabelTokenSort : String := "proof_label_tok"
def compressedWordTokenSort : String := "compressed_word_tok"
def includePathTokenSort : String := "include_path_tok"
def symbolListSort : String := "symbol_list"
def disjointSymbolListSort : String := "disjoint_symbol_list"
def proofListSort : String := "proof_list"
def proofHeaderListSort : String := "proof_header_list"
def compressedWordListSort : String := "compressed_word_list"
def statementSort : String := "statement"
def databaseSort : String := "database"
def outerStatementSort : String := "outer_statement"
def outerDatabaseSort : String := "outer_database"

def lexicalDeclarations : List LexicalDeclaration :=
  [LexicalDeclaration.lexicalClass "mm-label" labelTokenSort,
   LexicalDeclaration.lexicalClass "mm-symbol" symbolTokenSort,
   LexicalDeclaration.lexicalClass "mm-proof-label" proofLabelTokenSort,
   LexicalDeclaration.lexicalClass "mm-compressed-word" compressedWordTokenSort,
   LexicalDeclaration.lexicalClass "mm-include-path" includePathTokenSort]

/-! ## Authored concrete lexical policy

These finite codepoint sets are the concrete-syntax extension of the
structural `LanguageDef`.  They live beside the structural root so that the
parser exporter and the certificate checker consume the same authored data.
The generic `LanguageDef` remains free of lexer-specific fields.
-/

private def integersFrom (first count : Nat) : List Nat :=
  (List.range count).map (first + ·)

def whitespaceCodepoints : List Nat := [32, 9, 13, 10, 12]

def labelCodepoints : List Nat :=
  integersFrom 65 26 ++ integersFrom 97 26 ++ integersFrom 48 10 ++
    [46, 45, 95]

def mathSymbolCodepoints : List Nat :=
  (integersFrom 33 94).filter fun codepoint => codepoint != 36

def compressedCodepoints : List Nat :=
  integersFrom 65 26 ++ [63]

def commentNonDollarCodepoints : List Nat :=
  (integersFrom 33 94).filter fun codepoint => codepoint != 36

def commentDollarFollowCodepoints : List Nat :=
  (integersFrom 33 94).filter fun codepoint =>
    codepoint != 40 && codepoint != 41

/-- One authored fixed-token row, with names for both generated parser
representations.  `parserRef` names the scannerless GSLT definition;
`classifiedToken` is the atom emitted by the legacy classified-token adapter.
Keeping the three fields together prevents the two generated presentations
from acquiring independent literal tables. -/
structure LiteralBinding where
  spelling : String
  parserRef : String
  classifiedToken : String
  deriving DecidableEq, Repr

/-- Fixed structural tokens in source order.  Both parser presentations are
derived mechanically from this single table. -/
def literalBindings : List LiteralBinding :=
  [{ spelling := "$c", parserRef := "kw-constant", classifiedToken := "MM_C" },
   { spelling := "$v", parserRef := "kw-variable", classifiedToken := "MM_V" },
   { spelling := "$d", parserRef := "kw-disjoint", classifiedToken := "MM_D" },
   { spelling := "$f", parserRef := "kw-float", classifiedToken := "MM_F" },
   { spelling := "$e", parserRef := "kw-essential", classifiedToken := "MM_E" },
   { spelling := "$a", parserRef := "kw-axiom", classifiedToken := "MM_A" },
   { spelling := "$p", parserRef := "kw-theorem", classifiedToken := "MM_P" },
   { spelling := "$=", parserRef := "kw-proof", classifiedToken := "MM_EQPROOF" },
   { spelling := "$.", parserRef := "kw-end", classifiedToken := "MM_DOT" },
   { spelling := "${", parserRef := "kw-block-open", classifiedToken := "MM_SCOPE_OPEN" },
   { spelling := "$}", parserRef := "kw-block-close", classifiedToken := "MM_SCOPE_CLOSE" },
   { spelling := "$[", parserRef := "kw-include-open", classifiedToken := "MM_INCLUDE_OPEN" },
   { spelling := "$]", parserRef := "kw-include-close", classifiedToken := "MM_INCLUDE_CLOSE" },
   { spelling := "(", parserRef := "left-paren", classifiedToken := "MM_LP" },
   { spelling := ")", parserRef := "right-paren", classifiedToken := "MM_RP" },
   { spelling := "?", parserRef := "unknown-proof", classifiedToken := "MM_UNKNOWN" }]

/-- Lexical token sorts and their generated parser-definition names. -/
def lexicalParserBindings : List (String × String) :=
  [(labelTokenSort, "label-token"),
   (proofLabelTokenSort, "proof-label-token"),
   (symbolTokenSort, "symbol-token"),
   (compressedWordTokenSort, "compressed-token"),
   (includePathTokenSort, "include-token")]

private def lookupPairBinding? (bindings : List (String × String))
    (key : String) : Option String :=
  match bindings.find? fun binding => binding.1 == key with
  | none => none
  | some binding => some binding.2

private def literalBinding? (token : String) : Option LiteralBinding :=
  literalBindings.find? fun binding => binding.spelling == token

def literalReference (token : String) : Option String :=
  (literalBinding? token).map (·.parserRef)

/-- Classified-token atom generated for a fixed structural spelling. -/
def literalClassifiedToken (token : String) : Option String :=
  (literalBinding? token).map (·.classifiedToken)

def lexicalReference (sort : String) : Option String :=
  lookupPairBinding? lexicalParserBindings sort

/-- Fixed structural tokens admitted by the source grammar. -/
def literalTokens : List String := literalBindings.map (·.spelling)

private def serializedCodepoints (text : String) : List Nat :=
  text.toUTF8.toList.map UInt8.toNat

private def nonemptyMembersOf (allowed : List Nat) (text : String) : Bool :=
  !text.isEmpty && (serializedCodepoints text).all (· ∈ allowed)

/-- Recheck one producer-supplied lexical observation against the authored
finite codepoint policy.  The same spelling may inhabit several classes; its
structural role is fixed by the checked grammar derivation. -/
def lexicallyValidToken (token : ClassifiedToken) : Bool :=
  token.literalName.isNone &&
    match token.className with
    | "" => literalTokens.contains token.serialized
    | "mm-label" => nonemptyMembersOf labelCodepoints token.serialized
    | "mm-symbol" => nonemptyMembersOf mathSymbolCodepoints token.serialized
    | "mm-proof-label" =>
        nonemptyMembersOf labelCodepoints token.serialized
    | "mm-compressed-word" =>
        nonemptyMembersOf compressedCodepoints token.serialized
    | "mm-include-path" =>
        nonemptyMembersOf mathSymbolCodepoints token.serialized
    | _ => false

/-- Every lexical observation in a source ledger is independently checked;
class names are evidence to verify, never authority supplied by a parser. -/
def lexicallyValidSource (source : ClassifiedSource) : Bool :=
  source.tokens.all lexicallyValidToken

private def parameter (name sort : String) : TermParam :=
  .simple name (.base sort)

private def production (label category : String)
    (params : List TermParam) (syntaxPattern : List SyntaxItem) : GrammarRule :=
  { label, category, params, syntaxPattern }

def sourceProductions : List GrammarRule :=
  [production "symbols_one" symbolListSort
    [parameter "symbol" symbolTokenSort]
    [.nonTerminal "symbol"],
   production "symbols_more" symbolListSort
    [parameter "symbol" symbolTokenSort, parameter "rest" symbolListSort]
    [.nonTerminal "symbol", .nonTerminal "rest"],
   production "disjoint_symbols_two" disjointSymbolListSort
    [parameter "first" symbolTokenSort, parameter "second" symbolTokenSort]
    [.nonTerminal "first", .nonTerminal "second"],
   production "disjoint_symbols_more" disjointSymbolListSort
    [parameter "first" symbolTokenSort,
     parameter "rest" disjointSymbolListSort]
    [.nonTerminal "first", .nonTerminal "rest"],
   production "proof_one" proofListSort
    [parameter "label" proofLabelTokenSort]
    [.nonTerminal "label"],
   production "proof_more" proofListSort
    [parameter "label" proofLabelTokenSort, parameter "rest" proofListSort]
    [.nonTerminal "label", .nonTerminal "rest"],
   production "proof_unknown_one" proofListSort []
    [.terminal "?"],
   production "proof_unknown_more" proofListSort
    [parameter "rest" proofListSort]
    [.terminal "?", .nonTerminal "rest"],
   production "header_empty" proofHeaderListSort [] [],
   production "header_more" proofHeaderListSort
    [parameter "label" proofLabelTokenSort,
     parameter "rest" proofHeaderListSort]
    [.nonTerminal "label", .nonTerminal "rest"],
   production "compressed_one" compressedWordListSort
    [parameter "word" compressedWordTokenSort]
    [.nonTerminal "word"],
   production "compressed_more" compressedWordListSort
    [parameter "word" compressedWordTokenSort,
     parameter "rest" compressedWordListSort]
    [.nonTerminal "word", .nonTerminal "rest"],

   production "statement_const" outerStatementSort
    [parameter "symbols" symbolListSort]
    [.terminal "$c", .nonTerminal "symbols", .terminal "$."],
   production "statement_var" statementSort
    [parameter "symbols" symbolListSort]
    [.terminal "$v", .nonTerminal "symbols", .terminal "$."],
   production "statement_disjoint" statementSort
    [parameter "symbols" disjointSymbolListSort]
    [.terminal "$d", .nonTerminal "symbols", .terminal "$."],
   production "statement_float" statementSort
    [parameter "label" labelTokenSort,
     parameter "typecode" symbolTokenSort,
     parameter "variable" symbolTokenSort]
    [.nonTerminal "label", .terminal "$f", .nonTerminal "typecode",
     .nonTerminal "variable", .terminal "$."],
   production "statement_essential" statementSort
    [parameter "label" labelTokenSort, parameter "formula" symbolListSort]
    [.nonTerminal "label", .terminal "$e", .nonTerminal "formula",
     .terminal "$."],
   production "statement_axiom" statementSort
    [parameter "label" labelTokenSort, parameter "formula" symbolListSort]
    [.nonTerminal "label", .terminal "$a", .nonTerminal "formula",
     .terminal "$."],
   production "statement_theorem_normal" statementSort
    [parameter "label" labelTokenSort,
     parameter "formula" symbolListSort,
     parameter "proof" proofListSort]
    [.nonTerminal "label", .terminal "$p", .nonTerminal "formula",
     .terminal "$=", .nonTerminal "proof", .terminal "$."],
   production "statement_theorem_compressed" statementSort
    [parameter "label" labelTokenSort,
     parameter "formula" symbolListSort,
     parameter "header" proofHeaderListSort,
     parameter "body" compressedWordListSort]
    [.nonTerminal "label", .terminal "$p", .nonTerminal "formula",
     .terminal "$=", .terminal "(", .nonTerminal "header",
     .terminal ")", .nonTerminal "body", .terminal "$."],
   production "statement_include" outerStatementSort
    [parameter "path" includePathTokenSort]
    [.terminal "$[", .nonTerminal "path", .terminal "$]"],
   production "statement_block" statementSort
    [parameter "inside" databaseSort]
    [.terminal "${", .nonTerminal "inside", .terminal "$}"],

   production "database_empty" databaseSort [] [],
   production "database_more" databaseSort
    [parameter "statement" statementSort, parameter "rest" databaseSort]
    [.nonTerminal "statement", .nonTerminal "rest"],

   production "outer_statement_inner" outerStatementSort
    [parameter "statement" statementSort]
    [.nonTerminal "statement"],
   production "outer_database_empty" outerDatabaseSort [] [],
   production "outer_database_more" outerDatabaseSort
    [parameter "statement" outerStatementSort,
     parameter "rest" outerDatabaseSort]
    [.nonTerminal "statement", .nonTerminal "rest"]]

def sourceGrammar : LanguageDef :=
  { name := "metamath-source-v0"
    types :=
      [labelTokenSort, symbolTokenSort, proofLabelTokenSort,
       compressedWordTokenSort, includePathTokenSort, symbolListSort,
       disjointSymbolListSort, proofListSort, proofHeaderListSort,
       compressedWordListSort, statementSort, databaseSort,
       outerStatementSort, outerDatabaseSort]
    terms := sourceProductions
    equations := []
    rewrites := [] }

/-- The authored root contains syntax only.  Metamath state transitions and
declarative provability enter later through a separate checked bridge. -/
theorem sourceGrammar_syntax_only :
    sourceGrammar.equations = [] ∧ sourceGrammar.rewrites = [] := by
  exact ⟨rfl, rfl⟩

theorem sourceGrammar_valid : sourceGrammar.validate = [] := by
  simp [LanguageDef.validate, sourceGrammar, sourceProductions,
    production, parameter, labelTokenSort, symbolTokenSort,
    proofLabelTokenSort, compressedWordTokenSort, includePathTokenSort,
    symbolListSort, disjointSymbolListSort, proofListSort,
    proofHeaderListSort, compressedWordListSort, statementSort, databaseSort,
    outerStatementSort, outerDatabaseSort,
    LanguageDef.typeNames, TypeDecl.plain, TermParam.bodyName,
    TermParam.binderNames, TermParam.typeExpr, TypeExpr.baseNames]

theorem sourceGrammar_supported :
    grammarSupportedForInference sourceGrammar = true := by
  decide

theorem sourceGrammar_has_all_productions :
    sourceGrammar.terms.length = 27 := by
  decide

theorem sourceGrammar_has_all_lexical_classes :
    lexicalDeclarations.length = 5 := by
  decide

theorem normalTheoremProduction_present :
    sourceProductions.any (fun rule =>
      rule.label == "statement_theorem_normal") = true := by
  decide

theorem normalProofUnknownProductions_present :
    sourceProductions.any (fun rule => rule.label == "proof_unknown_one") = true ∧
      sourceProductions.any (fun rule => rule.label == "proof_unknown_more") = true := by
  decide

private def normalProofUnknownFixture : ClassifiedSource :=
  { identity := "metamath-normal-proof-unknown"
    tokens :=
      [{ serialized := "th", literalName := none, className := "mm-label" },
       { serialized := "$p", literalName := none, className := "" },
       { serialized := "wff", literalName := none, className := "mm-symbol" },
       { serialized := "$=", literalName := none, className := "" },
       { serialized := "?", literalName := none, className := "" },
       { serialized := "$.", literalName := none, className := "" }] }

private def oneSymbolDisjointFixture : ClassifiedSource :=
  { identity := "metamath-one-symbol-disjoint"
    tokens :=
      [{ serialized := "$d", literalName := none, className := "" },
       { serialized := "x", literalName := none, className := "mm-symbol" },
       { serialized := "$.", literalName := none, className := "" }] }

private def includeInsideBlockFixture : ClassifiedSource :=
  { identity := "metamath-include-inside-block"
    tokens :=
      [{ serialized := "${", literalName := none, className := "" },
       { serialized := "$[", literalName := none, className := "" },
       { serialized := "child.mm", literalName := none,
         className := "mm-include-path" },
       { serialized := "$]", literalName := none, className := "" },
       { serialized := "$}", literalName := none, className := "" }] }

private def constantInsideBlockFixture : ClassifiedSource :=
  { identity := "metamath-constant-inside-block"
    tokens :=
      [{ serialized := "${", literalName := none, className := "" },
       { serialized := "$c", literalName := none, className := "" },
       { serialized := "wff", literalName := none, className := "mm-symbol" },
       { serialized := "$.", literalName := none, className := "" },
       { serialized := "$}", literalName := none, className := "" }] }

theorem normalProofUnknown_derives :
    ∃ tree,
      Derives
        (lexicalizedLanguage sourceGrammar lexicalDeclarations
          normalProofUnknownFixture)
        outerDatabaseSort normalProofUnknownFixture.ledger.tokens tree := by
  let language :=
    lexicalizedLanguage sourceGrammar lexicalDeclarations
      normalProofUnknownFixture
  let tokens := normalProofUnknownFixture.ledger.tokens
  have nonempty :
      (enumDerives language 10 outerDatabaseSort tokens).isEmpty = false := by
    decide
  cases derivations : enumDerives language 10 outerDatabaseSort tokens with
  | nil => simp [derivations] at nonempty
  | cons tree rest =>
      exact ⟨tree, enumDerives_sound language 10 outerDatabaseSort tokens tree <|
        by simp [derivations]⟩

/-- A `$d` statement has at least two symbols, as required by Appendix E. -/
theorem oneSymbolDisjoint_rejected :
    enumDerives
      (lexicalizedLanguage sourceGrammar lexicalDeclarations
        oneSymbolDisjointFixture)
      10 outerDatabaseSort oneSymbolDisjointFixture.ledger.tokens = [] := by
  decide

/-- Includes are preprocessing commands and cannot occur inside a block. -/
theorem includeInsideBlock_rejected :
    enumDerives
      (lexicalizedLanguage sourceGrammar lexicalDeclarations
        includeInsideBlockFixture)
      12 outerDatabaseSort includeInsideBlockFixture.ledger.tokens = [] := by
  decide

/-- Constant declarations are restricted to the outermost scope. -/
theorem constantInsideBlock_rejected :
    enumDerives
      (lexicalizedLanguage sourceGrammar lexicalDeclarations
        constantInsideBlockFixture)
      12 outerDatabaseSort constantInsideBlockFixture.ledger.tokens = [] := by
  decide

/-- Public source-adequacy boundary for the concrete Metamath grammar.
Successful admission and compact generic checking reconstruct a derivation of
the exact serialized source under this module's one grammar root and ordered
lexical declarations. -/
theorem checkedMetamathSourceBlocks_sound
    (source : ClassifiedSource)
    (presentation : ValidatedPresentation)
    (admitted :
      admitLexicalDAGPresentation sourceGrammar lexicalDeclarations source =
        some presentation)
    (rootId : Nat) (blocks : List (List DAGNode))
    (checked : checkDAGBlocks presentation
      (dagRootJudgment source.ledger outerDatabaseSort) rootId blocks = true) :
    ∃ tree,
      Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
        outerDatabaseSort source.ledger.tokens tree :=
  admittedLexicalDAGBlocks_root_sound sourceGrammar lexicalDeclarations source
    presentation admitted outerDatabaseSort rootId blocks checked

/-- Exact-erasure strengthening for the concrete Metamath source grammar.
The compact accepted object determines one raw proof, one typed derivation
whose erasure is that proof, and a grammar derivation of the exact source. -/
theorem checkedMetamathSourceBlocks_exact
    (source : ClassifiedSource)
    (presentation : ValidatedPresentation)
    (admitted :
      admitLexicalDAGPresentation sourceGrammar lexicalDeclarations source =
        some presentation)
    (rootId : Nat) (blocks : List (List DAGNode))
    (checked : checkDAGBlocks presentation
      (dagRootJudgment source.ledger outerDatabaseSort) rootId blocks = true) :
    ∃ (proof : RawProof)
        (derivation : Derivation presentation
          (dagRootJudgment source.ledger outerDatabaseSort))
        (tree : Pattern),
      expandDAGBlocks? presentation
          (dagRootJudgment source.ledger outerDatabaseSort) rootId blocks =
            some proof ∧
        derivation.erase = proof ∧
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
          outerDatabaseSort source.ledger.tokens tree :=
  admittedLexicalDAGBlocks_root_exact sourceGrammar lexicalDeclarations source
    presentation admitted outerDatabaseSort rootId blocks checked

end Mettapedia.Languages.Metamath.SourceGSLT
