import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeEnvironmentLookupLanguageDef

/-!
# Export the official TPTP include-environment lookup LanguageDef

This tool writes the validated premise-bearing document and parent-relative
binding lookup language through the canonical five-field wire. Unsupported
declarations fail closed instead of being silently omitted.
-/

namespace Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeEnvironmentLookupLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

def runCli (arguments : List String) : IO UInt32 := do
  match arguments with
  | [output] =>
      match CanonicalWire.renderLanguage?
          TptpOfficialIncludeEnvironmentLookupLanguageDef.language with
      | some wire =>
          IO.FS.writeFile output wire
          pure 0
      | none =>
          IO.eprintln
            "canonical wire does not support every include-environment lookup row"
          pure 1
  | _ =>
      IO.eprintln
        "usage: ExportTptpOfficialIncludeEnvironmentLookupLanguageDef <output-file>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeEnvironmentLookupLanguageDef

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpOfficialIncludeEnvironmentLookupLanguageDef.runCli
    arguments
