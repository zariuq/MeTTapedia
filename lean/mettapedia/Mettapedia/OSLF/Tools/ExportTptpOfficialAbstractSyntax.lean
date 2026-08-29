import Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntax

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntax.writeWire path
      return 0
  | _ =>
      IO.eprintln
        "usage: lake env lean Mettapedia/OSLF/Tools/ExportTptpOfficialAbstractSyntax.lean -- <output>"
      return 2
