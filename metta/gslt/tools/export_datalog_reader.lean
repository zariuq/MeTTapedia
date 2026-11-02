import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxExport

open Mettapedia.GSLT.LanguageDef.ModuleFormat

def main (arguments : List String) : IO UInt32 := do
  let [outputPath] := arguments | throw (IO.userError "expected one output directory")
  let some description := SouffleDatalog.syntaxDescription?
    | throw (IO.userError "actual authored syntax or selected profile port was refused")
  SourceSyntaxExport.exportDescription description (System.FilePath.mk outputPath)
  pure 0
