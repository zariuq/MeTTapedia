import Mettapedia.GSLT.LanguageDef.C1DigitLanguageDef

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      IO.FS.writeFile path
        Mettapedia.GSLT.LanguageDef.C1DigitLanguageDef.wire
      pure 0
  | _ =>
      IO.eprintln "usage: export-c1-digit-language-def <output-path>"
      pure 2
