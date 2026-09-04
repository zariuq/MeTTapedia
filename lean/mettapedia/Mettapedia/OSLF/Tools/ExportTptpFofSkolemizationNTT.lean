import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationNTT

/-!
# Export the authored FOF Skolemization language and generated NTT

This qualification tool emits four projections from the validated Lean
objects.  The authored operational transformation remains independently
usable.  The generated object-language and inference-calculus projections
form an optional source-indexed typing layer over that transformation.  The
checked-source package retains the exact inference definition together with
the revision and digest of its generated object-language projection.
-/

namespace Mettapedia.OSLF.Tools.ExportTptpFofSkolemizationNTT

open Mettapedia.GSLT.LanguageDef

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | [sourcePath, generatedLanguagePath, generatedInferencePath,
      generatedSourcePath] =>
      IO.FS.writeFile sourcePath TptpFofSkolemizationLanguageDef.wire
      IO.FS.writeFile generatedLanguagePath
        TptpFofSkolemizationNTT.generatedLanguageWire
      IO.FS.writeFile generatedInferencePath
        TptpFofSkolemizationNTT.generatedInferenceWire
      IO.FS.writeFile generatedSourcePath
        TptpFofSkolemizationNTT.generatedSourceWire
      pure 0
  | _ =>
      IO.eprintln
        "usage: ExportTptpFofSkolemizationNTT <source-language> <generated-language> <generated-inference> <generated-source>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpFofSkolemizationNTT

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpFofSkolemizationNTT.run arguments
