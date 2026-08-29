import Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier

def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.writeWire path
        *> pure 0
  | _ =>
      IO.eprintln
        "usage: lake env lean --run ExportTptpOfficialSemanticCarrier.lean <output>"
        *> pure 2
