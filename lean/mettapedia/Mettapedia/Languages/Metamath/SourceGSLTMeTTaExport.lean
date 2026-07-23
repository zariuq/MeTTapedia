import Mettapedia.Languages.Metamath.SourceGSLT

namespace Mettapedia.Languages.Metamath.SourceGSLTMeTTaExport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction
open Mettapedia.Languages.Metamath.SourceGSLT

private def parameterSort? : List TermParam → String → Option String
  | [], _ => none
  | .simple parameterName (.base sort) :: parameters, name =>
      if parameterName = name then some sort else parameterSort? parameters name
  | _ :: parameters, name => parameterSort? parameters name

private def renderSyntaxItem (rule : GrammarRule) : SyntaxItem → Option String
  | .terminal token => do
      let classifiedToken ← literalClassifiedToken token
      pure s!"(Tm {classifiedToken})"
  | .nonTerminal name => do
      let sort ← parameterSort? rule.params name
      pure s!"(Hl {sort})"
  | .separator _ | .delimiter _ _ | .op _ => none

private def renderSyntaxItems (rule : GrammarRule) :
    List SyntaxItem → Option String
  | [] => some "()"
  | items => do
      let rendered ← items.mapM (renderSyntaxItem rule)
      pure s!"({String.intercalate "" rendered})"

private def renderProduction (rule : GrammarRule) : Option String := do
  let rightHandSide ← renderSyntaxItems rule rule.syntaxPattern
  pure s!"  (Prod {rule.label} {rule.category} {rightHandSide})"

private def renderLexicalDeclaration : LexicalDeclaration → String
  | .literal atomName sort => s!"  (VarD {atomName} {sort})"
  | .lexicalClass className sort => s!"  (LexD {className} {sort})"

private def lexicalClassForSort? (sort : String) : Option String :=
  match lexicalDeclarations.find? fun declaration =>
      match declaration with
      | .literal _ _ => false
      | .lexicalClass _ declarationSort => declarationSort == sort with
  | none => none
  | some (.literal _ _) => none
  | some (.lexicalClass className _) => some className

private def renderParserLexicalBinding
    (binding : String × String) : Option String := do
  let className ← lexicalClassForSort? binding.1
  pure s!"  (ParserLexicalBinding {binding.1} {binding.2} {className})"

private def render? : Option String := do
  let productions ← sourceGrammar.terms.mapM renderProduction
  let parserBindings ←
    lexicalParserBindings.mapM renderParserLexicalBinding
  let entries := lexicalDeclarations.map renderLexicalDeclaration ++ productions
  pure <|
    "; Generated from the admitted Metamath source GSLT root.\n" ++
    "; Edit the Lean source and regenerate this artifact.\n\n" ++
    "(= (lib_parse:mm-source-grammar) (mkGram (\n" ++
    String.intercalate "\n" entries ++ "\n)))\n\n" ++
    "(= (lib_parse:mm-statement-grammar)\n" ++
    "   (lib_parse:mm-source-grammar))\n\n" ++
    "(= (lib_parse:mm-database-grammar)\n" ++
    "   (lib_parse:mm-source-grammar))\n\n" ++
    "; Generated lexical projection metadata for proof-certificate replay.\n" ++
    "(= (lib_parse:mm-source-parser-lexical-bindings) (\n" ++
    String.intercalate "\n" parserBindings ++ "\n))\n"

/-- Every fixed terminal in the structural root has exactly the data needed
by the classified-token presentation.  The exporter fails closed as well,
but this theorem catches an omitted row at Lean build time. -/
theorem everySourceTerminalClassified :
    sourceGrammar.terms.all (fun rule =>
      rule.syntaxPattern.all fun item =>
        match item with
        | .terminal token => (literalClassifiedToken token).isSome
        | _ => true) = true := by
  decide

/-- Every scannerless lexical reference used by the parser compiler has a
matching classified-token declaration for generic certificate replay. -/
theorem everyParserLexicalBindingClassified :
    lexicalParserBindings.all (fun binding =>
      (lexicalClassForSort? binding.1).isSome) = true := by
  decide

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      match render? with
      | none =>
          IO.eprintln "Metamath source grammar contains an unsupported row"
          pure 1
      | some rendered =>
          IO.FS.writeFile outputPath rendered
          IO.println s!"wrote {rendered.toUTF8.size} bytes to {outputPath}"
          pure 0
  | _ =>
      IO.eprintln "usage: SourceGSLTMeTTaExport <output.metta>"
      pure 1

end Mettapedia.Languages.Metamath.SourceGSLTMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.SourceGSLTMeTTaExport.main arguments
