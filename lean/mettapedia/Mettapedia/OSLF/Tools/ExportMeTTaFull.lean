import Mettapedia.OSLF.MeTTaIL.ExportBackend
import Mettapedia.OSLF.MeTTaCore.FullLanguageDef
import Mettapedia.OSLF.MeTTaCore.FullPremises

/-!
# MeTTa Full Export Tool

Generates the complete Rust `language!{}` macro block for MeTTaFullState,
including the logic section auto-generated from `mettaFullPremises`.

Usage:
  lean --run Mettapedia/OSLF/Tools/ExportMeTTaFull.lean > output.rs

Or print to stdout for inspection.
-/

open Mettapedia.OSLF.MeTTaIL.ExportBackend
open Mettapedia.OSLF.MeTTaCore.FullLanguageDef (mettaFull)
open Mettapedia.OSLF.MeTTaCore.FullPremises (mettaFullPremises)

def main : IO Unit := do
  let output := renderLanguageFull mettaFull mettaFullPremises
  IO.println output
