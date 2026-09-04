import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeInputClassificationLanguageDef

/-!
# Export the official TPTP include-input classification LanguageDef

This tool writes the validated all-family classifier through the canonical
five-field wire. Unsupported declarations fail closed instead of being
silently omitted.
-/

namespace Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeInputClassificationLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

def runCli (arguments : List String) : IO UInt32 := do
  match arguments with
  | [output] =>
      match CanonicalWire.renderLanguage?
          TptpOfficialIncludeInputClassificationLanguageDef.language with
      | some wire =>
          IO.FS.writeFile output wire
          pure 0
      | none =>
          IO.eprintln
            "canonical wire does not support every include-input classification row"
          pure 1
  | _ =>
      IO.eprintln
        "usage: ExportTptpOfficialIncludeInputClassificationLanguageDef <output-file>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeInputClassificationLanguageDef

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeInputClassificationLanguageDef.runCli
    arguments
