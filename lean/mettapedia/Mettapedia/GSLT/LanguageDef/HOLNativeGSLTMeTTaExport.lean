import Mettapedia.GSLT.LanguageDef.HOLNativeGSLTSlice
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

namespace Mettapedia.GSLT.LanguageDef.HOLNativeGSLTMeTTaExport

open Mettapedia.GSLT.LanguageDef.HOLNativeGSLTSlice
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

private def render : String :=
  "!(import! &self gslt_checked_source_v1)\n\n" ++
  s!"(= (hl-native-source) {renderGSLTSource holLightNativeSource})\n" ++
  s!"(= (hl-native-goal) {renderPattern holLightGoal})\n" ++
  s!"(= (hl-native-proof) {renderRawProof holLightEqMpProof})\n" ++
  s!"(= (hl-native-wrong-order) {renderRawProof holLightWrongChildOrderProof})\n" ++
  s!"(= (hl-native-changed-binding) {renderRawProof holLightChangedBindingProof})\n\n" ++
  s!"(= (h4-native-source) {renderGSLTSource hol4NativeSource})\n" ++
  s!"(= (h4-native-goal) {renderPattern hol4Goal})\n" ++
  s!"(= (h4-native-proof) {renderRawProof hol4DischProof})\n" ++
  s!"(= (h4-native-missing-removal) {renderRawProof hol4MissingRemovalProof})\n" ++
  s!"(= (h4-native-wrong-removal) {renderRawProof hol4WrongRemovalEvidenceProof})\n\n" ++
  "!(assertEqual (gslt-source-validation-v1 (hl-native-source)) SourceAcceptedV1)\n" ++
  "!(assertEqual (gslt-source-check-v1 (hl-native-source) (hl-native-goal) (hl-native-proof)) True)\n" ++
  "!(assertEqual (gslt-source-check-v1 (hl-native-source) (hl-native-goal) (hl-native-wrong-order)) False)\n" ++
  "!(assertEqual (gslt-source-check-v1 (hl-native-source) (hl-native-goal) (hl-native-changed-binding)) False)\n" ++
  "!(assertEqual (gslt-source-validation-v1 (h4-native-source)) SourceAcceptedV1)\n" ++
  "!(assertEqual (gslt-source-check-v1 (h4-native-source) (h4-native-goal) (h4-native-proof)) True)\n" ++
  "!(assertEqual (gslt-source-check-v1 (h4-native-source) (h4-native-goal) (h4-native-missing-removal)) False)\n" ++
  "!(assertEqual (gslt-source-check-v1 (h4-native-source) (h4-native-goal) (h4-native-wrong-removal)) False)\n" ++
  "!(assertEqual (gslt-source-check-v1 (hl-native-source) (h4-native-goal) (h4-native-proof)) False)\n" ++
  "!(HOLNativeGSLTSummary 2 5 8 9 9 0)\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      IO.FS.writeFile outputPath render
      IO.println s!"wrote {render.toUTF8.size} bytes to {outputPath}"
      pure 0
  | _ =>
      IO.eprintln "usage: HOLNativeGSLTMeTTaExport <output.metta>"
      pure 1

end Mettapedia.GSLT.LanguageDef.HOLNativeGSLTMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.HOLNativeGSLTMeTTaExport.main arguments
