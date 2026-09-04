import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeSelectionLanguageDef

/-!
# Export the official TPTP include-selection LanguageDef

This tool writes the validated premise-bearing selection language through the
canonical five-field wire. Unsupported declarations fail closed instead of
being silently omitted.
-/

namespace Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeSelectionLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

def runCli (arguments : List String) : IO UInt32 := do
  match arguments with
  | [output] =>
      match CanonicalWire.renderLanguage?
          TptpOfficialIncludeSelectionLanguageDef.language with
      | some wire =>
          IO.FS.writeFile output wire
          pure 0
      | none =>
          IO.eprintln
            "canonical wire does not support every include-selection row"
          pure 1
  | _ =>
      IO.eprintln
        "usage: ExportTptpOfficialIncludeSelectionLanguageDef <output-file>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeSelectionLanguageDef

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeSelectionLanguageDef.runCli
    arguments
