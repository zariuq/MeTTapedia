import Mettapedia.Languages.MinskyLite.LookupPlan
import Mettapedia.Languages.MinskyLite.RewriteIR
import Mettapedia.Languages.MinskyLite.TransitionSpec
import Mettapedia.Languages.MinskyLite.SpecProfile

namespace Mettapedia.OSLF.Tools.ExportMinskyLiteArtifacts

private def defaultOutDir : System.FilePath := "artifacts/minskylite"

private def exportAll (outDir : System.FilePath) : IO UInt32 := do
  let a <- Mettapedia.Languages.MinskyLite.LookupPlan.exportMinskyLiteLookupPlan outDir
  let b <- Mettapedia.Languages.MinskyLite.TransitionSpec.exportMinskyLiteTransitionSpec outDir
  let c <- Mettapedia.Languages.MinskyLite.RewriteIR.exportMinskyLiteRewriteIR outDir
  let d <- Mettapedia.Languages.MinskyLite.SpecProfile.exportProfile outDir
  if a == 0 && b == 0 && c == 0 && d == 0 then pure 0 else pure 2

private def checkAll (outDir : System.FilePath) : IO UInt32 := do
  let a <- Mettapedia.Languages.MinskyLite.LookupPlan.checkMinskyLiteLookupPlan outDir
  let b <- Mettapedia.Languages.MinskyLite.TransitionSpec.checkMinskyLiteTransitionSpec outDir
  let c <- Mettapedia.Languages.MinskyLite.RewriteIR.checkMinskyLiteRewriteIR outDir
  let d <- Mettapedia.Languages.MinskyLite.SpecProfile.checkProfile outDir
  if a == 0 && b == 0 && c == 0 && d == 0 then pure 0 else pure 3

private def usage : String :=
  String.intercalate "\n"
    [ "minskylite artifact commands:"
    , "  export-all <out-dir>"
    , "  export-all            (default out-dir: artifacts/minskylite)"
    , "  check-all <out-dir>"
    , "  check-all             (default out-dir: artifacts/minskylite)"
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

end Mettapedia.OSLF.Tools.ExportMinskyLiteArtifacts

def main (args : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportMinskyLiteArtifacts.runCli args
