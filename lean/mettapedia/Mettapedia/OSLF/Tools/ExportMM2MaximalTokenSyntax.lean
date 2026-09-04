import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSyntax

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [path] =>
      match CanonicalWire.renderLanguage? language with
      | some wire => IO.FS.writeFile path wire
      | none => throw (IO.userError "MM2 maximal-token syntax is not wire-supported")
  | _ =>
      throw (IO.userError
        "usage: lake env lean --run ExportMM2MaximalTokenSyntax.lean <output>")
