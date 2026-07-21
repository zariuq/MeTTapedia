import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
import Mettapedia.Languages.Metamath.MMLean4SemanticView

/-!
# MeTTa export of canonical `mm-lean4` semantic database views

The generated artifact contains one source-identity-bound semantic reference
per corpus.  The grammar-derived ordered ledger is projected independently in
CeTTa and compared with these references object by object.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTSemanticMeTTaExport

open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.Languages.Metamath.MMLean4SemanticView

private def renderCons (render : α → String) : List α → String
  | [] => "Nil"
  | value :: values => s!"(Cons {render value} {renderCons render values})"

private def renderPair (pair : String × String) : String :=
  s!"(MMSemanticPair {quote pair.1} {quote pair.2})"

private def renderSymbol : Metamath.Verify.Sym → String
  | .const name => s!"(MMSemanticConstantSymbol {quote name})"
  | .var name => s!"(MMSemanticVariableSymbol {quote name})"

private def renderObject : RuntimeObjectView → String
  | .constant name => s!"(MMSemanticConstant {quote name})"
  | .variable name => s!"(MMSemanticVariable {quote name})"
  | .hypothesis essential formula label =>
      let renderedEssential := if essential then "True" else "False"
      s!"(MMSemanticHypothesis {renderedEssential} " ++
        s!"{renderCons renderSymbol formula} {quote label})"
  | .assertion formula distinctVariables hypotheses label =>
      s!"(MMSemanticAssertion {renderCons renderSymbol formula} " ++
        s!"{renderCons renderPair distinctVariables} " ++
        s!"{renderCons quote hypotheses} {quote label})"

private def renderEntry (entry : String × RuntimeObjectView) : String :=
  s!"(MMSemanticEntry {quote entry.1} {renderObject entry.2})"

private def renderDatabase (database : SemanticDatabaseView) : String :=
  s!"(MMSemanticDatabase " ++
    s!"{renderCons renderPair database.finalDistinctVariables} " ++
    s!"{renderCons quote database.finalHypotheses} " ++
    s!"{renderCons renderEntry database.objects})"

private def readCheckedDatabase (sourcePath : String) : IO Metamath.Verify.DB := do
  let sourceBytes ← IO.FS.readBinFile sourcePath
  pure <|
    Metamath.Verify.checkBytes sourceBytes
      Metamath.Verify.ModeConfig.soundDefault

private def renderReference
    (revision digest sourcePath : String) : IO (Except String String) := do
  let database ← readCheckedDatabase sourcePath
  if hAccepted : readerAccepted database = true then
    have _agreement : ReaderAgreement database := readerAccepted_sound hAccepted
    pure <| .ok <|
      s!"(= (mm-semantic-reference-v0 {quote digest}) " ++
        s!"(MMSemanticReference {quote revision} {quote digest} " ++
        s!"{renderDatabase (semanticDatabaseView database)}))"
  else
    pure <| .error s!"source rejected by mm-lean4: {sourcePath}"

private def renderAll
    (inputs : List (String × String × String)) : IO (Except String String) := do
  let mut references : List String := []
  for input in inputs do
    match ← renderReference input.1 input.2.1 input.2.2 with
    | .ok reference => references := references ++ [reference]
    | .error message => return .error message
  pure <| .ok <|
    "!(import! &self metamath_statement_semantics_v0)\n\n" ++
      String.intercalate "\n\n" references ++
      s!"\n\n!(MMSemanticReferenceV0Summary {references.length})\n"

private def parseInputs : List String → Except String (List (String × String × String))
  | [] => .ok []
  | revision :: digest :: sourcePath :: rest => do
      let inputs ← parseInputs rest
      pure ((revision, digest, sourcePath) :: inputs)
  | _ => .error "each semantic source requires REVISION DIGEST SOURCE"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | outputPath :: rawInputs =>
      match parseInputs rawInputs with
      | .ok [] =>
          IO.eprintln
            "usage: SourceGSLTSemanticMeTTaExport OUTPUT (REVISION DIGEST SOURCE)+"
          pure 2
      | .ok inputs =>
          match ← renderAll inputs with
          | .ok output =>
              IO.FS.writeFile outputPath output
              IO.println s!"wrote {output.toUTF8.size} bytes to {outputPath}"
              pure 0
          | .error message =>
              IO.eprintln message
              pure 1
      | .error message =>
          IO.eprintln message
          pure 2
  | _ =>
      IO.eprintln
        "usage: SourceGSLTSemanticMeTTaExport OUTPUT (REVISION DIGEST SOURCE)+"
      pure 2

end Mettapedia.Languages.Metamath.SourceGSLTSemanticMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.SourceGSLTSemanticMeTTaExport.main arguments
