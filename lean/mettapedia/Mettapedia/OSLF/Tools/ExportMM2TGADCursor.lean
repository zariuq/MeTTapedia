import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TGADCursorWire

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TGADCursorWire.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: export-mm2-tgad-cursor <output-path>"
      pure 2
