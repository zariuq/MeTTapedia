import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
import Mettapedia.Languages.Metamath.SourceGSLT

/-!
# Scannerless parser generated from the Metamath source GSLT

The structural definitions in this presentation are compiled from
`SourceGSLT.sourceGrammar`.  This module supplies only the concrete lexical
policy specified by Metamath Appendix E: ASCII token classes, comments,
whitespace, and fixed keyword spellings.

The exported artifact is consumed by GSLT2Parse.  It is not a second authored
grammar: `compiledRules_preserve_source` and `compiledRules_preserve_syntax`
tie every generated structural rule back to the ordered `LanguageDef` root.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTParserExport

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
open Mettapedia.Languages.Metamath.SourceGSLT
open Mettapedia.OSLF.Framework.GrammarDerives

def sourceBinding : Binding where
  literalRef := literalReference
  lexicalSortRef := lexicalReference
  categoryRef := fun category => "mm-category-" ++ category
  ruleRef := fun label => "mm-production-" ++ label

def compiledSourceRules : List CompiledRule :=
  (compileRules? sourceBinding sourceGrammar).getD []

theorem sourceRules_compile :
    compileRules? sourceBinding sourceGrammar = some compiledSourceRules := by
  rfl

/-- No source production is invented, omitted, duplicated, or reordered. -/
theorem compiledRules_preserve_source :
    compiledSourceRules.map (fun rule => rule.source) = sourceGrammar.terms :=
  compileRules_sourceRules sourceBinding sourceGrammar compiledSourceRules
    sourceRules_compile

/-- No terminal or nonterminal occurrence is invented, omitted, duplicated,
or reordered inside any source production. -/
theorem compiledRules_preserve_syntax :
    compiledSourceRules.map (fun rule =>
        rule.atoms.map StructuralAtom.sourceSyntax) =
      sourceGrammar.terms.map (fun rule => rule.syntaxPattern) :=
  compileRules_sourceSyntax sourceBinding sourceGrammar compiledSourceRules
    sourceRules_compile

/-- At the ordered-token boundary, derivability in the generated structural
rule IR is equivalent to derivability in the authored `SourceGSLT` grammar.
Raw-byte lexical recognition is intentionally outside this theorem. -/
theorem compiledDerivation_iff_sourceDerivation
    (sort : String) (tokens : List String)
    (tree : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    CompiledDerives compiledSourceRules sort tokens tree ↔
      Derives sourceGrammar sort tokens tree :=
  compileRules_derivation_iff sourceRules_compile sort tokens tree

/-- Positive boundary witness: the authored empty outer database survives
structural compilation. -/
theorem emptyOuterDatabase_compiled :
    CompiledDerives compiledSourceRules outerDatabaseSort []
      (.apply "outer_database_empty" []) := by
  apply (compiledDerivation_iff_sourceDerivation outerDatabaseSort []
    (.apply "outer_database_empty" [])).2
  exact enumDerives_sound sourceGrammar 1 outerDatabaseSort []
    (.apply "outer_database_empty" []) (by decide)

/-- Negative boundary witness: compilation cannot invent a production label. -/
theorem inventedEmptyProduction_rejected :
    ¬ CompiledDerives compiledSourceRules outerDatabaseSort []
      (.apply "invented-empty-production" []) := by
  intro compiled
  have source :
      Derives sourceGrammar outerDatabaseSort []
        (.apply "invented-empty-production" []) :=
    (compiledDerivation_iff_sourceDerivation outerDatabaseSort []
      (.apply "invented-empty-production" [])).1 compiled
  have enumerated :
      (.apply "invented-empty-production" []) ∈
        enumDerives sourceGrammar 1 outerDatabaseSort [] :=
    (mem_enumDerives_iff sourceGrammar 1 outerDatabaseSort []
      (.apply "invented-empty-production" [])).2 ⟨source, by decide⟩
  have absent :
      (.apply "invented-empty-production" []) ∉
        enumDerives sourceGrammar 1 outerDatabaseSort [] := by
    decide
  exact absent enumerated

def compiledCategoryDefinitions : List Definition :=
  (compileCategoryDefinitions? sourceBinding sourceGrammar
    compiledSourceRules).getD []

theorem sourceCategories_compile :
    compileCategoryDefinitions? sourceBinding sourceGrammar
      compiledSourceRules = some compiledCategoryDefinitions := by
  rfl

private def literal (text : String) : Expr :=
  .literal (text.toUTF8.toList.map UInt8.toNat)

private def lexicalName (name : String) : String :=
  name ++ "-lexeme"

private def separatedLexeme (name : String) (body : Expr) : Definition :=
  { name := lexicalName name
    body := .left body (.ref "token-separator") }

private def separatedToken (name : String) : Definition :=
  { name
    body := .left (.ref (lexicalName name)) (.ref "skip") }

private def keywordDefinitions
    (name spelling : String) : List Definition :=
  [separatedLexeme name (literal spelling), separatedToken name]

private def members (className : String)
    (codepoints : List Nat) : List ClassMember :=
  codepoints.map fun codepoint => { className, codepoint }

def lexicalMembers : List ClassMember :=
  members "whitespace" whitespaceCodepoints ++
  members "label-char" labelCodepoints ++
  members "math-symbol-char" mathSymbolCodepoints ++
  members "compressed-char" compressedCodepoints ++
  members "comment-non-dollar" commentNonDollarCodepoints ++
  members "comment-dollar-follow" commentDollarFollowCodepoints

set_option maxRecDepth 100000 in
theorem lexicalMemberCount : lexicalMembers.length = 375 := by
  decide

private def lexicalCoreDefinitions : List Definition :=
  [{ name := "token-separator"
     body := .alt (.class "whitespace") .eof },
   { name := "comment"
     body := .node "comment" <|
       .right (literal "$(") <|
       .right (.ref "whitespace1") <|
       .right (.star (.seq (.ref "comment-chunk") (.ref "whitespace1"))) <|
       .seq (literal "$)") (.class "whitespace") },
   { name := "comment-chunk"
     body := .alt
       (.plus (.ref "comment-pair-unit"))
       (.seq (.star (.ref "comment-pair-unit")) (.char 36)) },
   { name := "comment-pair-unit"
     body := .alt
       (.class "comment-non-dollar")
       (.seq (.char 36) (.class "comment-dollar-follow")) },
   { name := "skip"
     body := .star (.ref "skip-unit") },
   { name := "skip-unit"
     body := .alt (.class "whitespace") (.ref "comment") },
   { name := "whitespace1"
     body := .plus (.class "whitespace") },
   separatedLexeme "label-token"
     (.node "label-token" (.plus (.class "label-char"))),
   separatedToken "label-token",
   separatedLexeme "proof-label-token"
     (.node "proof-label-token" (.plus (.class "label-char"))),
   separatedToken "proof-label-token",
   separatedLexeme "symbol-token"
     (.node "symbol-token" (.plus (.class "math-symbol-char"))),
   separatedToken "symbol-token",
   separatedLexeme "include-token"
     (.node "include-token" (.plus (.class "math-symbol-char"))),
   separatedToken "include-token",
   separatedLexeme "compressed-token"
     (.node "compressed-token" (.plus (.class "compressed-char"))),
   separatedToken "compressed-token"]

def lexicalDefinitions : List Definition :=
  lexicalCoreDefinitions ++
    literalBindings.flatMap fun binding =>
      keywordDefinitions binding.parserRef binding.spelling

def structuralDefinitions : List Definition :=
  compiledSourceRules.map (CompiledRule.definition sourceBinding) ++
    compiledCategoryDefinitions

def rootDefinition : Definition :=
  { name := "database"
    body := .node "database" <|
      .right (.ref "skip") <|
      .left (.ref (sourceBinding.categoryRef outerDatabaseSort)) .eof }

def parserPresentation : Presentation :=
  { name := "MetamathAppendixEV1"
    definitions := lexicalDefinitions ++ structuralDefinitions ++
      [rootDefinition]
    members := lexicalMembers }

def renderedPresentation : String := parserPresentation.render

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      IO.FS.writeFile outputPath renderedPresentation
      IO.println s!"wrote {renderedPresentation.toUTF8.size} bytes to {outputPath}"
      pure 0
  | _ =>
      IO.eprintln "usage: SourceGSLTParserExport <output.metta>"
      pure 1

end Mettapedia.Languages.Metamath.SourceGSLTParserExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.SourceGSLTParserExport.main arguments
