/-
Write the reference export of the TemplateScope model for the C scope matrix:
one JSON record per corpus row and configuration, from
`Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge.exportJson`, whose answer
bags are the model's `ans` (`Bridge.records_bag`).
Run:   `lake env lean --run scripts/ExportScopeSpectrumReference.lean OUT.json`
Check: `lake env lean --run scripts/ExportScopeSpectrumReference.lean --check OUT.json`
(exit 0 when OUT.json is exactly the export of the current model).
-/
import Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge
open Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge

def main (args : List String) : IO UInt32 := do
  match checkTexts with
  | .error e =>
      IO.eprintln s!"export refused: {e}"
      return 1
  | .ok () => pure ()
  match args with
  | ["--check", path] =>
      let current ← IO.FS.readFile path
      if current == exportText then
        IO.println s!"{path} is the export of the current model ({records.length} records)"
        return 0
      else
        IO.eprintln s!"{path} differs from the export of the current model"
        return 1
  | [path] =>
      IO.FS.writeFile path exportText
      IO.println s!"wrote {records.length} records to {path}"
      return 0
  | _ =>
      IO.eprintln "usage: ExportScopeSpectrumReference.lean OUT.json | --check OUT.json"
      return 2
