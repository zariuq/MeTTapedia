import Mettapedia.GSLT.LanguageDef.TptpOfficialSyntaxTree

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.TptpOfficialSyntaxTree.writeWire path
      pure 0
  | _ =>
      IO.eprintln "usage: lake env lean --run ExportTptpOfficialSyntaxTree.lean <output>"
      pure 2
