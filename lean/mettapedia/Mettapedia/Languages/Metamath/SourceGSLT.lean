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
def proofListSort : String := "proof_list"
def proofHeaderListSort : String := "proof_header_list"
def compressedWordListSort : String := "compressed_word_list"
def statementSort : String := "statement"
def databaseSort : String := "database"

def lexicalDeclarations : List LexicalDeclaration :=
  [LexicalDeclaration.lexicalClass "mm-label" labelTokenSort,
   LexicalDeclaration.lexicalClass "mm-symbol" symbolTokenSort,
   LexicalDeclaration.lexicalClass "mm-proof-label" proofLabelTokenSort,
   LexicalDeclaration.lexicalClass "mm-compressed-word" compressedWordTokenSort,
   LexicalDeclaration.lexicalClass "mm-include-path" includePathTokenSort]

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

   production "statement_const" statementSort
    [parameter "symbols" symbolListSort]
    [.terminal "$c", .nonTerminal "symbols", .terminal "$."],
   production "statement_var" statementSort
    [parameter "symbols" symbolListSort]
    [.terminal "$v", .nonTerminal "symbols", .terminal "$."],
   production "statement_disjoint" statementSort
    [parameter "symbols" symbolListSort]
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
   production "statement_include" statementSort
    [parameter "path" includePathTokenSort]
    [.terminal "$[", .nonTerminal "path", .terminal "$]"],
   production "statement_block" statementSort
    [parameter "inside" databaseSort]
    [.terminal "${", .nonTerminal "inside", .terminal "$}"],

   production "database_empty" databaseSort [] [],
   production "database_more" databaseSort
    [parameter "statement" statementSort, parameter "rest" databaseSort]
    [.nonTerminal "statement", .nonTerminal "rest"]]

def sourceGrammar : LanguageDef :=
  { name := "metamath-source-v0"
    types :=
      [labelTokenSort, symbolTokenSort, proofLabelTokenSort,
       compressedWordTokenSort, includePathTokenSort, symbolListSort,
       proofListSort, proofHeaderListSort, compressedWordListSort,
       statementSort, databaseSort]
    terms := sourceProductions
    equations := []
    rewrites := [] }

theorem sourceGrammar_valid : sourceGrammar.validate = [] := by
  simp [LanguageDef.validate, sourceGrammar, sourceProductions,
    production, parameter, labelTokenSort, symbolTokenSort,
    proofLabelTokenSort, compressedWordTokenSort, includePathTokenSort,
    symbolListSort, proofListSort, proofHeaderListSort,
    compressedWordListSort, statementSort, databaseSort,
    LanguageDef.typeNames, TypeDecl.plain, TermParam.bodyName,
    TermParam.binderNames, TermParam.typeExpr, TypeExpr.baseNames]

theorem sourceGrammar_supported :
    grammarSupportedForInference sourceGrammar = true := by
  decide

theorem sourceGrammar_has_all_productions :
    sourceGrammar.terms.length = 22 := by
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

theorem normalProofUnknown_derives :
    ∃ tree,
      Derives
        (lexicalizedLanguage sourceGrammar lexicalDeclarations
          normalProofUnknownFixture)
        databaseSort normalProofUnknownFixture.ledger.tokens tree := by
  let language :=
    lexicalizedLanguage sourceGrammar lexicalDeclarations
      normalProofUnknownFixture
  let tokens := normalProofUnknownFixture.ledger.tokens
  have nonempty : (enumDerives language 8 databaseSort tokens).isEmpty = false := by
    decide
  cases derivations : enumDerives language 8 databaseSort tokens with
  | nil => simp [derivations] at nonempty
  | cons tree rest =>
      exact ⟨tree, enumDerives_sound language 8 databaseSort tokens tree <|
        by simp [derivations]⟩

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
      (dagRootJudgment source.ledger databaseSort) rootId blocks = true) :
    ∃ tree,
      Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
        databaseSort source.ledger.tokens tree :=
  admittedLexicalDAGBlocks_root_sound sourceGrammar lexicalDeclarations source
    presentation admitted databaseSort rootId blocks checked

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
      (dagRootJudgment source.ledger databaseSort) rootId blocks = true) :
    ∃ (proof : RawProof)
        (derivation : Derivation presentation
          (dagRootJudgment source.ledger databaseSort))
        (tree : Pattern),
      expandDAGBlocks? presentation
          (dagRootJudgment source.ledger databaseSort) rootId blocks =
            some proof ∧
        derivation.erase = proof ∧
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
          databaseSort source.ledger.tokens tree :=
  admittedLexicalDAGBlocks_root_exact sourceGrammar lexicalDeclarations source
    presentation admitted databaseSort rootId blocks checked

end Mettapedia.Languages.Metamath.SourceGSLT
