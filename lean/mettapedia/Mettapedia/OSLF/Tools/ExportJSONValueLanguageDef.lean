import Mettapedia.GSLT.LanguageDef.JSONValueLanguageDefWire

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.JSONValueLanguageDefWire.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: export-json-value-language-def <output-path>"
      pure 2
