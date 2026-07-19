import Mettapedia.GSLT.LanguageDef.HOLInferenceExtraction
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

namespace Mettapedia.GSLT.LanguageDef.HOLInferenceMeTTaExport

open Mettapedia.GSLT.LanguageDef.HOLInferenceExtraction
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

private def requireSome (message : String) : Option α → Except String α
  | some value => pure value
  | none => throw message

private def render : Except String String := do
  let h4Presentation ← requireSome "HOL4 generated presentation rejected"
    hol4InferencePresentation?
  let h4Positive ← requireSome "HOL4 positive proof unavailable" hol4ImpIdProof?
  let h4Missing ← requireSome "HOL4 missing-child proof unavailable"
    hol4ImpIdMissingChildProof?
  let h4Reordered ← requireSome "HOL4 reordered-child proof unavailable"
    hol4ImpIdReorderedProof?
  let h4Extra ← requireSome "HOL4 extra-child proof unavailable"
    hol4ImpIdExtraChildProof?
  let h4Wrong ← requireSome "HOL4 wrong-rule proof unavailable"
    hol4ImpIdWrongRuleProof?
  let hlPresentation ← requireSome "HOL Light generated presentation rejected"
    holLightInferencePresentation?
  let hlPositive ← requireSome "HOL Light positive proof unavailable"
    holLightSelfImpProof?
  let hlMissing ← requireSome "HOL Light missing-child proof unavailable"
    holLightSelfImpMissingChildProof?
  let hlReordered ← requireSome "HOL Light reordered-child proof unavailable"
    holLightSelfImpReorderedProof?
  let hlExtra ← requireSome "HOL Light extra-child proof unavailable"
    holLightSelfImpExtraChildProof?
  let hlWrong ← requireSome "HOL Light wrong-rule proof unavailable"
    holLightSelfImpWrongRuleProof?
  pure <|
    "!(import! &self generic_inference_checker_v0)\n\n" ++
    s!"(= (hol4-generated-presentation) {renderPresentation h4Presentation})\n" ++
    s!"(= (hol4-generated-goal) {renderPattern hol4ImpIdGoal})\n" ++
    s!"(= (hol4-generated-positive) {renderRawProof h4Positive})\n" ++
    s!"(= (hol4-generated-missing) {renderRawProof h4Missing})\n" ++
    s!"(= (hol4-generated-reordered) {renderRawProof h4Reordered})\n" ++
    s!"(= (hol4-generated-extra) {renderRawProof h4Extra})\n" ++
    s!"(= (hol4-generated-wrong) {renderRawProof h4Wrong})\n\n" ++
    "!(assertEqual (gic-presentation-valid (hol4-generated-presentation)) True)\n" ++
    "!(assertEqual (gic-check (hol4-generated-presentation) (hol4-generated-goal) (hol4-generated-positive)) True)\n" ++
    "!(assertEqual (gic-check (hol4-generated-presentation) (hol4-generated-goal) (hol4-generated-missing)) False)\n" ++
    "!(assertEqual (gic-check (hol4-generated-presentation) (hol4-generated-goal) (hol4-generated-reordered)) False)\n" ++
    "!(assertEqual (gic-check (hol4-generated-presentation) (hol4-generated-goal) (hol4-generated-extra)) False)\n" ++
    "!(assertEqual (gic-check (hol4-generated-presentation) (hol4-generated-goal) (hol4-generated-wrong)) False)\n\n" ++
    s!"(= (hl-generated-presentation) {renderPresentation hlPresentation})\n" ++
    s!"(= (hl-generated-goal) {renderPattern holLightSelfImpGoal})\n" ++
    s!"(= (hl-generated-positive) {renderRawProof hlPositive})\n" ++
    s!"(= (hl-generated-missing) {renderRawProof hlMissing})\n" ++
    s!"(= (hl-generated-reordered) {renderRawProof hlReordered})\n" ++
    s!"(= (hl-generated-extra) {renderRawProof hlExtra})\n" ++
    s!"(= (hl-generated-wrong) {renderRawProof hlWrong})\n\n" ++
    "!(assertEqual (gic-presentation-valid (hl-generated-presentation)) True)\n" ++
    "!(assertEqual (gic-check (hl-generated-presentation) (hl-generated-goal) (hl-generated-positive)) True)\n" ++
    "!(assertEqual (gic-check (hl-generated-presentation) (hl-generated-goal) (hl-generated-missing)) False)\n" ++
    "!(assertEqual (gic-check (hl-generated-presentation) (hl-generated-goal) (hl-generated-reordered)) False)\n" ++
    "!(assertEqual (gic-check (hl-generated-presentation) (hl-generated-goal) (hl-generated-extra)) False)\n" ++
    "!(assertEqual (gic-check (hl-generated-presentation) (hl-generated-goal) (hl-generated-wrong)) False)\n\n" ++
    "!(HOLGeneratedInventory 15 8 3 3)\n" ++
    "!(HOLGeneratedGICSummary 2 12 12 0)\n"

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
      IO.eprintln "usage: HOLInferenceMeTTaExport <output.metta>"
      pure 1


end Mettapedia.GSLT.LanguageDef.HOLInferenceMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.HOLInferenceMeTTaExport.main arguments
