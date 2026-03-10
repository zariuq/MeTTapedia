import Mettapedia.Languages.MeTTa.HE.LookupPlan
import Mettapedia.Languages.MeTTa.HE.TransitionSpec
import Mettapedia.Languages.MeTTa.HE.RewriteIR
import Mettapedia.Languages.MeTTa.PurePrototypeEval

private def usage : String :=
  String.intercalate "\n"
    [ "mettapedia commands:"
    , "  pure-eval <file>"
    , "  pure-eval <file> --fuel <n>"
    , "  lookup-plan export-he <out-dir>"
    , "  lookup-plan export-he            (default out-dir: artifacts/lookup)"
    , "  lookup-plan check-he <out-dir>"
    , "  lookup-plan check-he             (default out-dir: artifacts/lookup)"
    , "  transition-spec export-he <out-dir>"
    , "  transition-spec export-he            (default out-dir: artifacts/transition)"
    , "  transition-spec check-he <out-dir>"
    , "  transition-spec check-he             (default out-dir: artifacts/transition)"
    , "  rewrite-ir export-he <out-dir>"
    , "  rewrite-ir export-he                 (default out-dir: artifacts/transition)"
    , "  rewrite-ir check-he <out-dir>"
    , "  rewrite-ir check-he                  (default out-dir: artifacts/transition)"
    ]

private def defaultLookupOutDir : System.FilePath :=
  "artifacts/lookup"

private def defaultTransitionOutDir : System.FilePath :=
  "artifacts/transition"

private def parseFuelArg? (s : String) : Option Nat :=
  s.toNat?

def main (args : List String) : IO UInt32 := do
  match args with
  | ["pure-eval", file] =>
      Mettapedia.Languages.MeTTa.PurePrototypeEval.runPureEvalFile file
  | ["pure-eval", file, "--fuel", fuelText] =>
      match parseFuelArg? fuelText with
      | some fuel =>
          Mettapedia.Languages.MeTTa.PurePrototypeEval.runPureEvalFile file fuel
      | none =>
          IO.eprintln s!"invalid fuel: {fuelText}"
          pure 1
  | ["lookup-plan", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.exportHeLookupPlan outDir
  | ["lookup-plan", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.exportHeLookupPlan defaultLookupOutDir
  | ["lookup-plan", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.checkHeLookupPlan outDir
  | ["lookup-plan", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.checkHeLookupPlan defaultLookupOutDir
  | ["transition-spec", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.TransitionSpec.exportHeTransitionSpec outDir
  | ["transition-spec", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.TransitionSpec.exportHeTransitionSpec defaultTransitionOutDir
  | ["transition-spec", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.TransitionSpec.checkHeTransitionSpec outDir
  | ["transition-spec", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.TransitionSpec.checkHeTransitionSpec defaultTransitionOutDir
  | ["rewrite-ir", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIR.exportHeRewriteIR outDir
  | ["rewrite-ir", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIR.exportHeRewriteIR defaultTransitionOutDir
  | ["rewrite-ir", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIR.checkHeRewriteIR outDir
  | ["rewrite-ir", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIR.checkHeRewriteIR defaultTransitionOutDir
  | _ =>
      IO.println usage
      pure 1
