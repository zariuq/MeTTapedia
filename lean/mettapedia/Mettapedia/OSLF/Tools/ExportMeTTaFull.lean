import Mettapedia.OSLF.MeTTaIL.ExportBackend
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef
import Mettapedia.Languages.MeTTa.OSLFCore.FullPremises

/-!
# MeTTa Full Export Tool

Generates the complete Rust `language!{}` macro block for MeTTaFullState,
including the logic section auto-generated from `mettaFullPremises`.

Usage:
  lean --run Mettapedia/OSLF/Tools/ExportMeTTaFull.lean > output.rs

Or print to stdout for inspection.
-/

open Mettapedia.OSLF.MeTTaIL.ExportBackend
open Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef (mettaFull)
open Mettapedia.Languages.MeTTa.OSLFCore.FullPremises (mettaFullPremises)

def main : IO Unit := do
  let output := renderLanguageFull mettaFull mettaFullPremises
  IO.println output
