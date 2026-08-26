import Mettapedia.GSLT.LanguageDef.RFC8259SyntaxLanguageDefWire

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.RFC8259SyntaxLanguageDefWire.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: export-rfc8259-json-syntax <output-path>"
      pure 2
