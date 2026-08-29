import Mettapedia.GSLT.LanguageDef.ArithmeticTargetCoproduct

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      IO.FS.writeFile path
        Mettapedia.GSLT.LanguageDef.ArithmeticTargetCoproduct.wire
      pure 0
  | _ =>
      IO.eprintln "usage: export-arithmetic-target-coproduct <output-path>"
      pure 2
