import Mettapedia.GSLT.LanguageDef.HOLSourceKernel
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

namespace Mettapedia.GSLT.LanguageDef.HOLSourceInferenceMeTTaExport

open Mettapedia.GSLT.LanguageDef.HOLSourceKernel
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

private def requireSome (message : String) : Option α → Except String α
  | some value => pure value
  | none => throw message

private def renderExtendableDefinition (name : String)
    (definition : CalculusLanguageDef) : String :=
  let constructors := renderList renderConstructor definition.toLanguageDef.terms
  let judgments := renderList renderJudgment definition.judgments
  let rules := renderList renderRule definition.rules
  let conversion := renderConversion definition.conversion
  s!"(= ({name} $extra-constructors $extra-rules)\n" ++
    s!"   (GInferenceLanguageV1 1\n" ++
    s!"     (gic-append {constructors} $extra-constructors) {judgments}\n" ++
    s!"     (gic-append {rules} $extra-rules) {conversion}))\n"

private def renderFormalManifest (system : String)
    (definition : CalculusLanguageDef) : String :=
  definition.rules.map (fun rule =>
    s!"; MIK-HOL-FORMALS {system} {rule.id.value} " ++
      String.intercalate "," (rule.metavariables.map (·.1))) |>
    String.intercalate "\n"

private def render : Except String String := do
  let holLight ← requireSome "HOL Light source definition rejected"
    holLightSourceDefinition?
  let hol4 ← requireSome "HOL4 source definition rejected"
    hol4SourceDefinition?
  pure <|
    "!(import! &self generic_inference_checker_v0)\n\n" ++
    renderFormalManifest "HL" holLight ++ "\n" ++
    renderFormalManifest "H4" hol4 ++ "\n\n" ++
    renderExtendableDefinition "hl-source-language-with" holLight ++ "\n" ++
    renderExtendableDefinition "h4-source-language-with" hol4 ++ "\n" ++
    "(= (hl-source-base-language) (hl-source-language-with LNil LNil))\n" ++
    "(= (h4-source-base-language) (h4-source-language-with LNil LNil))\n\n" ++
    "!(assertEqual (gic-language-valid (hl-source-base-language)) True)\n" ++
    "!(assertEqual (gic-language-valid (h4-source-base-language)) True)\n" ++
    s!"!(HOLSourceLanguageSummary 2 {holLight.rules.length} " ++
      s!"{hol4.rules.length} 0)\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      match render with
      | .error message =>
          IO.eprintln message
          pure 1
      | .ok output =>
          IO.FS.writeFile outputPath output
          IO.println s!"wrote {output.toUTF8.size} bytes to {outputPath}"
          pure 0
  | _ =>
      IO.eprintln "usage: HOLSourceInferenceMeTTaExport <output.metta>"
      pure 1

end Mettapedia.GSLT.LanguageDef.HOLSourceInferenceMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.HOLSourceInferenceMeTTaExport.main arguments
