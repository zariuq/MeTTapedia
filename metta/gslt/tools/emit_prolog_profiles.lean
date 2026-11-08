import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSyntax

/-! Regenerate the shared source grammar and its two declared reader profiles,
and, given a second path, the ground CHR source grammar that imports them. -/

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Logic.Prolog.ReaderProfile

def main (arguments : List String) : IO Unit := do
  let (directory, chr) ← match arguments with
    | [directory] => pure (directory, none)
    | [directory, chr] => pure (directory, some chr)
    | _ => throw (IO.userError "expected output directory and optional CHR module path")
  let root : System.FilePath := directory
  IO.FS.createDirAll root
  IO.FS.writeFile (root / "PrologCommonSyntax.module")
    (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print PrologSyntaxModule.common)
  for (name, profile) in [("ISO", iso), ("SWI", swi)] do
    IO.FS.writeFile (root / (name ++ "Syntax.module"))
      (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print (PrologSyntaxModule.module profile))
  if let some path := chr then
    IO.FS.writeFile path (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print CHRPrologSyntax.module)
  IO.println "wrote shared Prolog syntax and separate ISO/SWI reader profiles"
