import Mettapedia.Languages.MM0Lite.LookupPlan
import Mettapedia.Languages.MM0Lite.RewriteIR
import Mettapedia.Languages.MM0Lite.TransitionSpec
import Mettapedia.Languages.MM0Lite.SpecProfile

namespace Mettapedia.OSLF.Tools.ExportMM0LiteArtifacts

private def defaultOutDir : System.FilePath := "artifacts/mm0lite"

private def exportAll (outDir : System.FilePath) : IO UInt32 := do
  let a ← Mettapedia.Languages.MM0Lite.LookupPlan.exportMM0LookupPlan outDir
  let b ← Mettapedia.Languages.MM0Lite.TransitionSpec.exportMM0TransitionSpec outDir
  let c ← Mettapedia.Languages.MM0Lite.RewriteIR.exportMM0RewriteIR outDir
  let d ← Mettapedia.Languages.MM0Lite.SpecProfile.exportProfile outDir
  if a == 0 && b == 0 && c == 0 && d == 0 then pure 0 else pure 2

private def checkAll (outDir : System.FilePath) : IO UInt32 := do
  let a ← Mettapedia.Languages.MM0Lite.LookupPlan.checkMM0LookupPlan outDir
  let b ← Mettapedia.Languages.MM0Lite.TransitionSpec.checkMM0TransitionSpec outDir
  let c ← Mettapedia.Languages.MM0Lite.RewriteIR.checkMM0RewriteIR outDir
  let d ← Mettapedia.Languages.MM0Lite.SpecProfile.checkProfile outDir
  if a == 0 && b == 0 && c == 0 && d == 0 then pure 0 else pure 3

private def usage : String :=
  String.intercalate "\n"
    [ "mm0lite artifact commands:"
    , "  export-all <out-dir>"
    , "  export-all            (default out-dir: artifacts/mm0lite)"
    , "  check-all <out-dir>"
    , "  check-all             (default out-dir: artifacts/mm0lite)"
    ]

def runCli (args : List String) : IO UInt32 := do
  match args with
  | ["export-all", outDir] => exportAll outDir
  | ["export-all"] => exportAll defaultOutDir
  | ["check-all", outDir] => checkAll outDir
  | ["check-all"] => checkAll defaultOutDir
  | _ =>
      IO.println usage
      pure 1

end Mettapedia.OSLF.Tools.ExportMM0LiteArtifacts

def main (args : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportMM0LiteArtifacts.runCli args
