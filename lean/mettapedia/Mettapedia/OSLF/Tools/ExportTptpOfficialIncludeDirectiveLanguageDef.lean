import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeDirectiveLanguageDef

/-!
# Export the official TPTP include-directive LanguageDef

This tool writes the validated include-directive language through the canonical
five-field wire.  Unsupported declarations fail closed instead of being
silently omitted.
-/

namespace Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeDirectiveLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

def runCli (arguments : List String) : IO UInt32 := do
  match arguments with
  | [output] =>
      match CanonicalWire.renderLanguage?
          TptpOfficialIncludeDirectiveLanguageDef.language with
      | some wire =>
          IO.FS.writeFile output wire
          pure 0
      | none =>
          IO.eprintln
            "canonical wire does not support every official include-directive row"
          pure 1
  | _ =>
      IO.eprintln
        "usage: ExportTptpOfficialIncludeDirectiveLanguageDef <output-file>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeDirectiveLanguageDef

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeDirectiveLanguageDef.runCli
    arguments
