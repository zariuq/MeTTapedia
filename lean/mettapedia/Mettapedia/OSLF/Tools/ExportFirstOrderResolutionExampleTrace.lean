import Mettapedia.GSLT.LanguageDef.FirstOrderResolutionExampleTrace

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.FirstOrderResolutionExampleTrace.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: lake env lean --run ExportFirstOrderResolutionExampleTrace.lean <output>"
      pure 2
