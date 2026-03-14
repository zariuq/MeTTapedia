import Mettapedia.OSLF.MeTTaIL.OptManifest
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef

/-!
# Export Optimization Manifest to JSON

CLI tool that renders the optimization contract manifest for a given language.

Usage:
```bash
lean --run Mettapedia/OSLF/Tools/ExportOptManifest.lean              # stdout
lean --run Mettapedia/OSLF/Tools/ExportOptManifest.lean output.json  # file
```
-/

open Mettapedia.OSLF.MeTTaIL.OptManifest
open Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef (mettaFull)

def main (args : List String) : IO UInt32 := do
  let manifest := manifestFor mettaFull [
    { baseLang := "rhoCalc"
      extLang := "rhoCalcSetExt"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.specialization_preserves_reduction" }
  ]
  let json := renderManifestJSON manifest
  match args with
  | []     => IO.println json; return 0
  | [path] => IO.FS.writeFile path json; return 0
  | _      => IO.eprintln "Usage: ExportOptManifest [output.json]"; return 1
