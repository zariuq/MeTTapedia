import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionResultCarrier

/-!
# Export the official TPTP include-resolution result carrier

This tool writes the validated result carrier through the canonical five-field
wire. Unsupported declarations fail closed instead of being silently omitted.
-/

namespace Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeResolutionResultCarrier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

def runCli (arguments : List String) : IO UInt32 := do
  match arguments with
  | [output] =>
      match CanonicalWire.renderLanguage?
          TptpOfficialIncludeResolutionResultCarrier.language with
      | some wire =>
          IO.FS.writeFile output wire
          pure 0
      | none =>
          IO.eprintln
            "canonical wire does not support every include-resolution result row"
          pure 1
  | _ =>
      IO.eprintln
        "usage: ExportTptpOfficialIncludeResolutionResultCarrier <output-file>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeResolutionResultCarrier

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeResolutionResultCarrier.runCli
    arguments
