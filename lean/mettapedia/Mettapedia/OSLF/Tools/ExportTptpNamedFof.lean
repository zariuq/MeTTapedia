import Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef

open Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [path] => writeWire path
  | _ =>
      IO.eprintln "usage: ExportTptpNamedFof <output-path>"
      IO.Process.exit 2
