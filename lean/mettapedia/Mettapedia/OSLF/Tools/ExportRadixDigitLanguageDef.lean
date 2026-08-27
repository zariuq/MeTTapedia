import Mettapedia.GSLT.LanguageDef.RadixDigitLanguageDef

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      IO.FS.writeFile path
        Mettapedia.GSLT.LanguageDef.RadixDigitLanguageDef.wire
      pure 0
  | _ =>
      IO.eprintln "usage: export-radix-digit-language-def <output-path>"
      pure 2
