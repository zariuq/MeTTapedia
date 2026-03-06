import Mettapedia.Languages.IMP.LookupPlan
import Mettapedia.Languages.IMP.RewriteIR
import Mettapedia.Languages.IMP.TransitionSpec
import Mettapedia.Languages.IMP.SpecProfile

namespace Mettapedia.OSLF.Tools.ExportIMPArtifacts

private def defaultOutDir : System.FilePath := "artifacts/imp"

private def exportAll (outDir : System.FilePath) : IO UInt32 := do
  let a ← Mettapedia.Languages.IMP.LookupPlan.exportIMPLookupPlan outDir
  let b ← Mettapedia.Languages.IMP.TransitionSpec.exportIMPTransitionSpec outDir
  let c ← Mettapedia.Languages.IMP.RewriteIR.exportIMPRewriteIR outDir
  let d ← Mettapedia.Languages.IMP.SpecProfile.exportProfile outDir
  if a == 0 && b == 0 && c == 0 && d == 0 then pure 0 else pure 2

private def checkAll (outDir : System.FilePath) : IO UInt32 := do
  let a ← Mettapedia.Languages.IMP.LookupPlan.checkIMPLookupPlan outDir
  let b ← Mettapedia.Languages.IMP.TransitionSpec.checkIMPTransitionSpec outDir
  let c ← Mettapedia.Languages.IMP.RewriteIR.checkIMPRewriteIR outDir
  let d ← Mettapedia.Languages.IMP.SpecProfile.checkProfile outDir
  if a == 0 && b == 0 && c == 0 && d == 0 then pure 0 else pure 3

private def usage : String :=
  String.intercalate "\n"
    [ "imp artifact commands:"
    , "  export-all <out-dir>"
    , "  export-all            (default out-dir: artifacts/imp)"
    , "  check-all <out-dir>"
    , "  check-all             (default out-dir: artifacts/imp)"
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

end Mettapedia.OSLF.Tools.ExportIMPArtifacts

def main (args : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportIMPArtifacts.runCli args
