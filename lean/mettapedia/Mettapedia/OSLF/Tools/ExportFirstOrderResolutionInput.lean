import Mettapedia.GSLT.LanguageDef.FirstOrderResolutionInput

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.FirstOrderResolutionInput.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: lake env lean --run ExportFirstOrderResolutionInput.lean <output>"
      pure 2
