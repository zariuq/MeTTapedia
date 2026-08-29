import Mettapedia.GSLT.LanguageDef.TptpFofCnfSyntaxTree

open Mettapedia.GSLT.LanguageDef.TptpFofCnfSyntaxTree

def main (arguments : List String) : IO Unit :=
  match arguments with
  | [path] => writeWire path
  | _ => throw <| IO.userError
      "usage: lake env lean Mettapedia/OSLF/Tools/ExportTptpFofCnfSyntaxTree.lean <output>"
