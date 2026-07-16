import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
import Mettapedia.Languages.Metamath.NativeSourceCalculus

/-!
# Exact MeTTa export of the first native Metamath source slice

The exported value is the canonical source package, goal, and native proof
proved in `NativeSourceCalculus`.  The operational gate compares it directly
with the value compiled from the checked ordered source ledger.
-/

namespace Mettapedia.Languages.Metamath.NativeSourceCalculusMeTTaExport

open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.Languages.Metamath.NativeSourceCalculus
open Mettapedia.Languages.Metamath.MMLean4SemanticView

private def renderedSlice : String :=
  "(MMNativeSourceSlice " ++
    renderGSLTSource checkedSource ++ " " ++
    renderPattern targetGoal ++ " " ++
    renderRawProof targetRawProof ++ " " ++
    quote "th" ++ ")"

private def render : String :=
  "!(import! &self metamath_native_source_calculus_v0)\n\n" ++
  s!"(= (mm-native-reference-slice-v0) {renderedSlice})\n\n" ++
  "!(assertEqual\n" ++
  "  (mm-native:check-slice (mm-native-reference-slice-v0))\n" ++
  "  (MMNativeSourceCheck \"th\" SourceAcceptedV1 True))\n" ++
  "!(MMNativeReferenceSliceSummary 1 1 0)\n"

private def mismatchReport (database : Metamath.Verify.DB) : String :=
  let entryLines := expectedRuntimeObjects.map fun entry =>
    let actual := database.find? entry.1 |>.map runtimeObjectView
    s!"{entry.1}: expected={reprStr entry.2}; actual={reprStr actual}"
  String.intercalate "\n" <|
    [s!"error-free={database.error?.isNone}",
     s!"scope-count={database.scopes.size}",
     s!"final-dv-count={database.frame.dj.size}",
     s!"final-hypothesis-count={database.frame.hyps.size}",
     s!"final-hypotheses={reprStr database.frame.hyps.toList}",
     s!"object-count={database.objects.toList.length}",
     s!"entry-matches={expectedRuntimeObjects.all (runtimeObjectMatches database)}",
     s!"object-labels={reprStr (database.objects.toList.map (·.1))}"] ++
      entryLines

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [sourcePath, outputPath] =>
      let sourceBytes ← IO.FS.readBinFile sourcePath
      let database :=
        Metamath.Verify.checkBytes sourceBytes
          Metamath.Verify.ModeConfig.soundDefault
      if hMatches : runtimeSourceMatches database = true then
        have _certificate :
            Nonempty (RuntimeAnchoredNativeSourceCertificate database) :=
          runtime_anchored_native_source_certificate hMatches
        IO.FS.writeFile outputPath render
        IO.println s!"wrote {render.toUTF8.size} bytes to {outputPath}"
        pure 0
      else
        IO.eprintln
          "mm-lean4 source database does not match the selected native slice"
        IO.eprintln (mismatchReport database)
        pure 1
  | _ =>
      IO.eprintln
        "usage: NativeSourceCalculusMeTTaExport <source.mm> <output.metta>"
      pure 1

end Mettapedia.Languages.Metamath.NativeSourceCalculusMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.NativeSourceCalculusMeTTaExport.main arguments
