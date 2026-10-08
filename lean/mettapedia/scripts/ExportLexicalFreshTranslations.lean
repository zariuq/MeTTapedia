/-
Write the corpus translations of the lexical-fresh translator: for every row of
the scope corpus, the program, its translation from rule M to lexical fresh,
the census of refining patterns and un-introduced names, and the answer bags
of both models, from
`Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus.exportJson`.
Run:   `lake env lean --run scripts/ExportLexicalFreshTranslations.lean OUT.json`
Check: `lake env lean --run scripts/ExportLexicalFreshTranslations.lean --check OUT.json`
(exit 0 when OUT.json is exactly the export of the current model).
-/
import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus
open Mettapedia.GSLT.LanguageDef.TemplateScope

def main (args : List String) : IO UInt32 := do
  match Bridge.checkTexts with
  | .error e =>
      IO.eprintln s!"export refused: {e}"
      return 1
  | .ok () => pure ()
  match args with
  | ["--check", path] =>
      let current ← IO.FS.readFile path
      if current == LexicalFreshCorpus.exportText then
        IO.println s!"{path} is the export of the current model ({Bridge.rows.length} rows)"
        return 0
      else
        IO.eprintln s!"{path} differs from the export of the current model"
        return 1
  | [path] =>
      IO.FS.writeFile path LexicalFreshCorpus.exportText
      IO.println s!"wrote {Bridge.rows.length} rows to {path}"
      return 0
  | _ =>
      IO.eprintln "usage: ExportLexicalFreshTranslations.lean OUT.json | --check OUT.json"
      return 2
