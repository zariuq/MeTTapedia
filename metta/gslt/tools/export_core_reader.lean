import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxExport

open Mettapedia.GSLT.LanguageDef.ModuleFormat

def main (arguments : List String) : IO UInt32 := do
  let [language, outputPath] := arguments
    | throw (IO.userError "expected ocaml|maude|erlang and an output directory")
  let description? := match language with
    | "ocaml" => GoldCoreSyntax.OCaml.description?
    | "maude" => GoldCoreSyntax.Maude.description?
    | "erlang" => GoldCoreSyntax.Erlang.description?
    | _ => none
  let some description := description?
    | throw (IO.userError "unknown source profile or refused authored syntax")
  let selection? := match language with
    | "ocaml" => GoldCoreSyntax.OCaml.selection?
    | "maude" => GoldCoreSyntax.Maude.selection?
    | "erlang" => GoldCoreSyntax.Erlang.selection?
    | _ => none
  let some selection := selection?
    | throw (IO.userError "refused authored source-selection policy")
  let output := System.FilePath.mk outputPath
  SourceSyntaxExport.exportDescription description output
  SourceSyntaxExport.exportSelection selection output
  pure 0
