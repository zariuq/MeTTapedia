import Mettapedia.GSLT.LanguageDef.TptpFirstOrderDerivation

open Mettapedia.GSLT.LanguageDef

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      TptpFirstOrderDerivation.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: ExportTptpFirstOrderDerivation <output-path>"
      pure 2
