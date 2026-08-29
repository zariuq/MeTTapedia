import Mettapedia.GSLT.LanguageDef.FirstOrderClauseData

open Mettapedia.GSLT.LanguageDef.FirstOrderClauseData

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: export-first-order-clause-data <output-path>"
      pure 2
