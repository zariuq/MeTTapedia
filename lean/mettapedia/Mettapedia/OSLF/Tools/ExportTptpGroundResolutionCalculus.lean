import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCalculus

/-!
# Export the TPTP ground-resolution calculus

This qualification tool emits the finite-Horn projection of the admitted
calculus definition.  CeTTa consumes the checked-in projection during normal
operation; regeneration is a separate cross-implementation identity gate.
-/

namespace Mettapedia.OSLF.Tools.ExportTptpGroundResolutionCalculus

open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCalculus

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      if finiteHornSource = "" then
        IO.eprintln "ground-resolution calculus is outside the finite-Horn fragment"
        pure 1
      else
        IO.FS.writeFile outputPath finiteHornSource
        pure 0
  | _ =>
      IO.eprintln "usage: ExportTptpGroundResolutionCalculus <output.metta>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpGroundResolutionCalculus

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpGroundResolutionCalculus.run arguments
