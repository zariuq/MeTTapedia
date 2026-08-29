import Mettapedia.GSLT.LanguageDef.TptpFirstOrderDocument

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.TptpFirstOrderDocument.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: lake env lean --run ExportTptpFirstOrderDocument.lean <output>"
      pure 2
