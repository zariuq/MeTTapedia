import Mettapedia.Logic.Prolog.ReaderProfileState
import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxModule

/-! Retain source sentences with their evolving reader profiles. Recognition,
forest coverage and term interpretation use the ordinary source pipeline on
each exported unit; this planning command does not certify those steps. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open Mettapedia.Logic.Prolog ReaderProfile
open Mettapedia.GSLT.LanguageDef.ModuleFormat

def main (arguments : List String) : IO Unit := do
  let [dialect, sourcePath, outputPath] := arguments
    | throw (IO.userError "expected iso|swi, source file and new output directory")
  let initial ← match dialect with
    | "iso" => pure iso | "swi" => pure swi | _ => throw (IO.userError "unknown reader profile")
  let source ← IO.FS.readFile sourcePath
  let (sentences, final) ← match ReaderProfileState.readSource ReaderProfileState.noImports
      (source.toList.length + 1) initial source with
    | .ok result => pure result | .error reason => throw (IO.userError reason)
  let output : System.FilePath := outputPath
  if ← output.pathExists then throw (IO.userError "output directory already exists")
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "source.pl") source
  let mut manifest := #[]
  for (sentence,index) in sentences.zipIdx do
    let directory := output / toString index
    IO.FS.createDirAll directory
    IO.FS.writeFile (directory / "sentence.pl") sentence.text
    IO.FS.writeFile (directory / "CommonSyntax.module")
      (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print PrologSyntaxModule.common)
    let module := PrologSyntaxModule.module sentence.before
    IO.FS.writeFile (directory / (module.name ++ ".module"))
      (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print module)
    manifest := manifest.push (Lean.Json.mkObj [("unit",Lean.toJson index),
      ("module",Lean.toJson (module.name ++ ".module")),
      ("operatorCount",Lean.toJson sentence.before.operators.length)])
  IO.FS.writeFile (output / "sentences.json") ((Lean.Json.arr manifest).pretty ++ "\n")
  IO.FS.createDirAll (output / "final")
  IO.FS.writeFile (output / "final" / "CommonSyntax.module")
    (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print PrologSyntaxModule.common)
  let finalModule := PrologSyntaxModule.module final
  IO.FS.writeFile (output / "final" / (finalModule.name ++ ".module"))
    (Mettapedia.GSLT.LanguageDef.ModuleSource.Printer.print finalModule)
  IO.println s!"retained {sentences.length} sentences with their exact reader environments"
