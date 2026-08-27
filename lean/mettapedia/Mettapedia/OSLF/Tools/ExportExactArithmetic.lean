import Mettapedia.GSLT.LanguageDef.ExactArithmeticNTT

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      IO.FS.writeFile path
        Mettapedia.GSLT.LanguageDef.ExactArithmeticNTT.exactArithmeticWire
      pure 0
  | _ =>
      IO.eprintln "usage: export-exact-arithmetic <output-path>"
      pure 2
