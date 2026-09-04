import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionCarrier

/-!
# Export the official TPTP include-resolution environment carrier

This tool writes the validated carrier through the canonical five-field wire.
Unsupported declarations fail closed instead of being silently omitted.
-/

namespace Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeResolutionCarrier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

def runCli (arguments : List String) : IO UInt32 := do
  match arguments with
  | [output] =>
      match CanonicalWire.renderLanguage?
          TptpOfficialIncludeResolutionCarrier.language with
      | some wire =>
          IO.FS.writeFile output wire
          pure 0
      | none =>
          IO.eprintln
            "canonical wire does not support every include-resolution carrier row"
          pure 1
  | _ =>
      IO.eprintln
        "usage: ExportTptpOfficialIncludeResolutionCarrier <output-file>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeResolutionCarrier

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeResolutionCarrier.runCli
    arguments
