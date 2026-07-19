import Mettapedia.GSLT.LanguageDef.HOLSourceKernel
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

namespace Mettapedia.GSLT.LanguageDef.HOLSourceInferenceMeTTaExport

open Mettapedia.GSLT.LanguageDef.HOLSourceKernel
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

private def requireSome (message : String) : Option α → Except String α
  | some value => pure value
  | none => throw message

private def renderExtendablePresentation (name : String)
    (presentation : Presentation) : String :=
  let constructors := renderList renderConstructor presentation.language.terms
  let judgments := renderList renderJudgment presentation.judgments
  let rules := renderList renderRule presentation.rules
  s!"(= ({name} $extra-constructors $extra-rules)\n" ++
    s!"   (GPresentation (gic-append {constructors} $extra-constructors) {judgments}\n" ++
    s!"     (gic-append {rules} $extra-rules)))\n"

private def renderFormalManifest (system : String)
    (presentation : Presentation) : String :=
  presentation.rules.map (fun rule =>
    s!"; MIK-HOL-FORMALS {system} {rule.id.value} " ++
      String.intercalate "," (rule.metavariables.map (·.1))) |>
    String.intercalate "\n"

private def render : Except String String := do
  let holLight ← requireSome "HOL Light source presentation rejected"
    holLightSourcePresentation?
  let hol4 ← requireSome "HOL4 source presentation rejected"
    hol4SourcePresentation?
  pure <|
    "!(import! &self generic_inference_checker_v0)\n\n" ++
    renderFormalManifest "HL" holLight ++ "\n" ++
    renderFormalManifest "H4" hol4 ++ "\n\n" ++
    renderExtendablePresentation "hl-source-presentation-with" holLight ++ "\n" ++
    renderExtendablePresentation "h4-source-presentation-with" hol4 ++ "\n" ++
    "(= (hl-source-base-presentation) (hl-source-presentation-with LNil LNil))\n" ++
    "(= (h4-source-base-presentation) (h4-source-presentation-with LNil LNil))\n\n" ++
    "!(assertEqual (gic-presentation-valid (hl-source-base-presentation)) True)\n" ++
    "!(assertEqual (gic-presentation-valid (h4-source-base-presentation)) True)\n" ++
    s!"!(HOLSourcePresentationSummary 2 {holLight.rules.length} " ++
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
