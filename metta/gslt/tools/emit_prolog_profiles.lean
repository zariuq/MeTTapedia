import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxModule

/-! Regenerate the shared source grammar and its two declared reader profiles. -/

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Logic.Prolog.ReaderProfile

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  let root : System.FilePath := directory
  IO.FS.createDirAll root
  IO.FS.writeFile (root / "CommonSyntax.module")
    (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print PrologSyntaxModule.common)
  for (name, profile) in [("ISO", iso), ("SWI", swi)] do
    IO.FS.writeFile (root / (name ++ "Syntax.module"))
      (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print (PrologSyntaxModule.module profile))
  IO.println "wrote shared Prolog syntax and separate ISO/SWI reader profiles"
