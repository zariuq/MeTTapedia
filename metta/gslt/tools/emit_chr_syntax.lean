import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSyntax

/-! Emit CHR's source-only module over the shared Prolog syntax library. -/

open Mettapedia.GSLT.LanguageDef.ModuleFormat

def main (arguments : List String) : IO Unit := do
  let [destination] := arguments | throw (IO.userError "expected CHR syntax module destination")
  IO.FS.writeFile destination
    (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print CHRPrologSyntax.module)
  IO.println "wrote compositional CHR source grammar and reader profile"
