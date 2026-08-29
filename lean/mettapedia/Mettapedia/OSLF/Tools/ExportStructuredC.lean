import Mettapedia.GSLT.LanguageDef.StructuredC

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      IO.FS.writeFile path
        Mettapedia.GSLT.LanguageDef.StructuredC.wire
      pure 0
  | _ =>
      IO.eprintln "usage: export-structured-c <output-path>"
      pure 2
