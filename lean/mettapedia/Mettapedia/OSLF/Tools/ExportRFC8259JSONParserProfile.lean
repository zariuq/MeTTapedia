import Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileWire

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileWire.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: export-rfc8259-json-parser-profile <output-path>"
      pure 2
