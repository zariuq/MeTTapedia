import Mettapedia.OSLF.MeTTaIL.ExportBackend
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.HE.HEPremises

/-!
# HE MeTTa Export Tool

Generates the complete Rust `language!{}` macro block for MeTTaHE,
including the logic section auto-generated from `mettaHEPremises`.

Usage:
  lean --run Mettapedia/OSLF/Tools/ExportMeTTaHE.lean > mettahe_from_lean.rs

Or print to stdout for inspection.
-/

open Mettapedia.OSLF.MeTTaIL.ExportBackend
open Mettapedia.Languages.MeTTa.HE.LanguageDef (mettaHE)
open Mettapedia.Languages.MeTTa.HE.Premises (mettaHEPremises)

def main : IO Unit := do
  let output := renderLanguageFull mettaHE mettaHEPremises
  IO.println output
