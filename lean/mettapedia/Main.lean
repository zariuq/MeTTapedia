import Mettapedia
import Mettapedia.Languages.MeTTa.HE.LookupPlan

private def usage : String :=
  String.intercalate "\n"
    [ "mettapedia commands:"
    , "  lookup-plan export-he <out-dir>"
    , "  lookup-plan export-he            (default out-dir: artifacts/lookup)"
    , "  lookup-plan check-he <out-dir>"
    , "  lookup-plan check-he             (default out-dir: artifacts/lookup)"
    ]

private def defaultLookupOutDir : System.FilePath :=
  "artifacts/lookup"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["lookup-plan", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.exportHeLookupPlan outDir
  | ["lookup-plan", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.exportHeLookupPlan defaultLookupOutDir
  | ["lookup-plan", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.checkHeLookupPlan outDir
  | ["lookup-plan", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.checkHeLookupPlan defaultLookupOutDir
  | _ =>
      IO.println usage
      pure 1
